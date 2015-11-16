# This file is part of the TSM Desktop Application.
#
# The TSM Desktop Application is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# The TSM Desktop Application is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with the TSM Desktop Application.  If not, see <http://www.gnu.org/licenses/>.


# Local modules
from AppAPI import AppAPI, ApiError, ApiTransientError
import Config
import PrivateConfig
from Settings import load_settings
from WoWHelper import WoWHelper

# PyQt5
from PyQt5.QtCore import pyqtSignal, QMutex, QSettings, QThread, QVariant, QWaitCondition

# General python modules
from enum import Enum
from hashlib import sha512
from io import BytesIO
import logging
import re
import sys
from time import time, sleep
from zipfile import ZipFile


class MainThread(QThread):
    class WaitEvent(Enum):
        NONE = 0
        LOGIN_BUTTON = 1


    class State(Enum):
        INIT = 0
        LOGGED_OUT = 1
        PENDING_NEW_SESSION = 2
        VALID_SESSION = 3
        SLEEPING = 4

        @staticmethod
        def is_valid_transition(old_state, new_state):
            if new_state == MainThread.State.INIT:
                # should never go back to this state
                return False
            elif new_state == MainThread.State.LOGGED_OUT:
                # any current state is valid
                return True
            elif new_state == MainThread.State.PENDING_NEW_SESSION:
                return old_state == MainThread.State.SLEEPING
            elif new_state == MainThread.State.VALID_SESSION:
                return old_state in [MainThread.State.LOGGED_OUT, MainThread.State.PENDING_NEW_SESSION]
            elif new_state == MainThread.State.SLEEPING:
                return old_state == MainThread.State.VALID_SESSION


    set_login_window_visible = pyqtSignal(bool)
    set_login_window_enabled = pyqtSignal(bool)
    set_login_window_form_values = pyqtSignal(str, str)
    get_login_window_form_values = pyqtSignal()
    set_login_window_button_text = pyqtSignal(str)
    set_login_window_error_text = pyqtSignal(str)
    set_main_window_visible = pyqtSignal(bool)
    set_main_window_header_text = pyqtSignal(str)
    set_main_window_sync_status_data = pyqtSignal(list)
    set_main_window_addon_status_data = pyqtSignal(list)


    def __init__(self):
        # initi parent class and get a refernece to the logger
        QThread.__init__(self)
        self._logger = logging.getLogger()

        # load settings
        self._settings = load_settings(Config.DEFAULT_SETTINGS)
        if self._settings.version == 0:
            # this is the first time we've run r300 or higher
            old_login_settings = load_settings(Config.DEFAULT_OLD_LOGIN_SETTINGS, Config.ORG_NAME, "TSMAppLogin")
            if old_login_settings.userId > 0:
                # import the settings we care about from the old app
                self._settings.email = old_login_settings.email
                self._settings.password = str(old_login_settings.password, encoding="ascii")
                self._settings.accepted_terms = (old_login_settings.touAccepted == "true")
                # need to use QSettings directly for the regular settings since it uses groups / arrays
                old_settings = QSettings(QSettings.IniFormat, QSettings.UserScope, Config.ORG_NAME, "TSMApplication")
                self._settings.wow_path = old_settings.value("core/wowDirPath", Config.DEFAULT_SETTINGS['wow_path'])
                self._settings.tsm3_beta = (WoWHelper().get_installed_version("TradeSkillMaster")[0] == WoWHelper.BETA_VERSION)
                # TODO: clear the old settings
                self._logger.info("Imported old settings!")
        self._settings.version = Config.CURRENT_VERSION

        # initialize other helper classes
        self._api = AppAPI()
        self._wow_helper = WoWHelper()

        # initialize the variables which allow us to wait for signals
        self._wait_event = self.WaitEvent.NONE
        self._wait_context = None
        self._wait_condition = QWaitCondition()
        self._wait_mutex = QMutex()

        # initialize the FSM state
        self._state = self.State.INIT


    def _wait_for_event(self, event):
        self._wait_mutex.lock()
        if self._wait_event != self.WaitEvent.NONE:
            raise Exception("Already waiting for event {}".format(self.waiting_key))
        self._wait_event = event
        self._wait_condition.wait(self._wait_mutex)
        self._wait_event = self.WaitEvent.NONE
        self._wait_mutex.unlock()
        context = self._wait_context
        self._wait_context = None
        return context


    def _fire_wait_event(self, event, context=None):
        if self._wait_event != event:
            self._logger.info("Dropping event: {}".format(event))
            return
        self._wait_context = context
        self._wait_condition.wakeAll()


    def login_button_clicked(self, email, password):
        self._fire_wait_event(self.WaitEvent.LOGIN_BUTTON, (email, password))


    def addon_status_table_clicked(self, click_key):
        parts = click_key.split("~")
        table = parts.pop(0)
        if table == "addon":
            self._download_addon(*parts)
        else:
            raise Exception("Invalid table: {}".format(click_key))


    def _download_addon(self, addon, version):
        self._logger.info("Downloading {} version of {}".format(version, addon))
        try:
            with ZipFile(BytesIO(self._api.addon(addon, version))) as zip:
                self._wow_helper.install_addon(addon, zip)
        except (ApiTransientError, ApiError) as e:
            # either the user or we will try again later
            self._logger.error("Addon download error: {}".format(str(e)))
            if isinstance(e, ApiError):
                self._set_fsm_state(self.State.LOGGED_OUT)


    def _set_fsm_state(self, new_state):
        if new_state == self._state:
            # already in the desired state
            return
        old_state = self._state
        self._state = new_state
        if not self.State.is_valid_transition(old_state, new_state):
            raise Exception("Invalid state transtion from {} to {}!".format(old_state, new_state))

        self._logger.info("Set FSM state to {}".format(new_state))
        is_logged_out = (new_state == self.State.LOGGED_OUT)
        self.set_main_window_visible.emit(not is_logged_out)
        self.set_login_window_visible.emit(is_logged_out)
        if new_state == self.State.LOGGED_OUT:
            self._api.logout()
        elif new_state == self.State.PENDING_NEW_SESSION:
            pass
        elif new_state == self.State.VALID_SESSION:
            pass
        elif new_state == self.State.SLEEPING:
            pass
        else:
            raise Exception("Unpexected state transition from {} to {}".format(old_state, new_state))


    def _login_request(self):
        try:
            self._api.login(self._settings.email, self._settings.password)
            # the login was successful!
            self._logger.info("Logged in successfully!")
            self._set_fsm_state(self.State.VALID_SESSION)
        except (ApiTransientError, ApiError) as e:
            # either the user or we will try again later
            self._logger.error("Login error: {}".format(str(e)))
            self._settings.email = ""
            self._settings.password = ""
            if isinstance(e, ApiError):
                self._set_fsm_state(self.State.LOGGED_OUT)
            return str(e)

    def _login(self):
        self.set_login_window_enabled.emit(True)
        self.set_login_window_button_text.emit("Login")
        if self._settings.email == "" or self._settings.password == "":
            # wait for the user to login
            email, password = self._wait_for_event(self.WaitEvent.LOGIN_BUTTON)
            # do a simple sanity check on the email / password provided
            if email and re.match(r"[^@]+@[^@]+\.[^@]+", email) and password != "":
                # this is a valid email and password, so store it
                self._settings.email = email
                self._settings.password = sha512(password.encode("utf-8")).hexdigest()
                self.set_login_window_error_text.emit("")
            else:
                # the email / password is not valid
                self.set_login_window_error_text.emit("Invalid email / password")
        else:
            # send off a login request
            self.set_login_window_enabled.emit(False)
            self.set_login_window_button_text.emit("Logging in...")
            error_msg = self._login_request()
            if error_msg:
                self.set_login_window_error_text.emit(error_msg)


    def _check_status(self):
        try:
            result = self._api.status()
        except (ApiError, ApiTransientError) as e:
            self._logger.error("Got error from status API: {}".format(str(e)))

        # check addon versions
        addon_updates = []
        addon_status = []
        for addon in result['addons']:
            name = addon['name']
            latest_version = addon['betaVersion'] if self._settings.tsm3_beta else addon['version']
            version_type, version_int, version_str = self._wow_helper.get_installed_version(addon['name'])
            status = None
            if version_type == WoWHelper.INVALID_VERSION or True:
                status = {'text':"Not installed (double-click to install)", 'click_enabled':True, 'click_key':"addon~{}~{}".format(name, "beta")}
            elif version_type == WoWHelper.RELEASE_VERSION or version_type == WoWHelper.BETA_VERSION:
                if latest_version == 0:
                    # this addon no longer exists, so uninstall it (and don't set a status)
                    # TODO
                    pass
                elif version_int < latest_version:
                    # this addon needs to be updated
                    if self._api.get_is_premium() or self._settings.tsm3_beta:
                        # defer the auto-updating until after we set the status
                        addon_updates.append(name)
                        status = {'text':"Updating..."}
                    else:
                        status = {'text':"Update available. Please update or go premium for automatic updates.", 'color':[255, 0, 0]}
            elif version_type == WoWHelper.DEV_VERSION:
                status = {'text':"Automatic updates disabled"}
            else:
                raise Exception("Unexpected version type for {} ({}): {}".format(addon, version_str, version_type))
            if status:
                addon_status.append([{'text':name}, {'text':version_str}, status])
        self.set_main_window_addon_status_data.emit(addon_status)

        # update addons
        for name in addon_updates:
            # TODO: do the update
            pass

        # check realm data (AuctionDB / Shopping / WoWuction) status
        for realm in result['realms']:
            pass


    def run(self):
        while True:
            if self._state == self.State.INIT:
                # just go to the next state - this is so we can show the login window when we enter LOGGED_OUT
                self._set_fsm_state(self.State.LOGGED_OUT)
            elif self._state == self.State.LOGGED_OUT:
                # process login requests (which will move us to VALID_SESSION)
                self._login()
            elif self._state == self.State.PENDING_NEW_SESSION:
                # get a new session by making a login request (which will move us to VALID_SESSION)
                self._login_request()
            elif self._state == self.State.VALID_SESSION:
                # make a status request and move on to SLEEPING (even if it fails)
                if self._settings.wow_path != "":
                    self._check_status()
                self._set_fsm_state(self.State.SLEEPING)
            elif self._state == self.State.SLEEPING:
                # go to sleep and then go back to PENDING_NEW_SESSION
                self.sleep(60)
                self._set_fsm_state(self.State.PENDING_NEW_SESSION)
                # sync_status = [
                    # ('US Region', 'Updated 2 minutes ago', 'Updated 14 hours ago', 'Updated 2 minutes ago'),
                    # ('Tichondrius', 'Updated 2 minutes ago', 'Updated 14 hours ago', 'Updated 2 minutes ago'),
                    # ('Dunemaul', 'Updated 2 minutes ago', 'Updated 14 hours ago', 'Updated 2 minutes ago'),
                    # ('Chromaggus', 'Updated 2 minutes ago', 'Updated 14 hours ago', 'Updated 2 minutes ago'),
                    # ('Illidan', 'Updated 2 minutes ago', 'Updated 14 hours ago', 'Updated 2 minutes ago'),
                # ]
                # self.set_main_window_sync_status_data.emit(sync_status)
                # self.sleep(300)
            else:
                raise Exception("Invalid state {}".format(self._state))