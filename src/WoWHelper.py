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
from AppData import AppData
from Backup import Backup
import Config
from SavedVariables import SavedVariables
from Settings import load_settings

# PyQt5
from PyQt5.QtCore import pyqtSignal, QFileSystemWatcher, QObject, QStandardPaths, QTimer

# General python modules
from datetime import datetime, timedelta
import logging
import os
import re
from shutil import rmtree
from time import time
from zipfile import ZipFile, ZIP_LZMA


class WoWHelper(QObject):
    INVALID_VERSION = 0
    RELEASE_VERSION = 1
    DEV_VERSION = 2


    addons_folder_changed = pyqtSignal()


    def __init__(self):
        QObject.__init__(self)
        self._watcher = QFileSystemWatcher()
        self._watcher.directoryChanged.connect(self.directory_changed)
        # initialize instances variables
        self._addons_folder_change_scheduled = False
        self._valid_wow_path = False
        self._addons = []
        self._settings = load_settings(Config.DEFAULT_SETTINGS)
        self._saved_variables = {}
        self._temp_backup_path = os.path.join(QStandardPaths.writableLocation(QStandardPaths.AppDataLocation), Config.TEMP_BACKUP_DIR)

        # load the WoW path
        if not self.set_wow_path(self._settings.wow_path):
            # try to automatically determine the wow path
            self.find_wow_path()


    def _get_addon_path(self, addon=None):
        addons_path = os.path.join(self._settings.wow_path, "Interface", "Addons")
        if not os.path.isdir(addons_path):
            addons_path = os.path.join(self._settings.wow_path, "Interface", "AddOns")
        if addon:
            return os.path.abspath(os.path.join(addons_path, addon))
        else:
            return os.path.abspath(addons_path)


    def _get_saved_variables_path(self, account, addon=None):
        if addon:
            return os.path.join(self._settings.wow_path, "WTF", "Account", account, "SavedVariables", "{}.lua".format(addon))
        else:
            return os.path.join(self._settings.wow_path, "WTF", "Account", account, "SavedVariables")


    def _get_saved_variables(self, account, addon):
        if (account, addon) not in self._saved_variables:
            self._saved_variables[(account, addon)] = SavedVariables(self._get_saved_variables_path(account, addon), addon)
        return self._saved_variables[(account, addon)].get_data()


    def get_accounts(self):
        accounts = []
        if not os.path.isdir(os.path.join(self._settings.wow_path, "WTF", "Account")):
            return accounts
        for account_name in os.listdir(os.path.join(self._settings.wow_path, "WTF", "Account")):
            if re.match("[^a-zA-Z0-9#]", account_name):
                continue
            if os.path.isfile(self._get_saved_variables_path(account_name, "TradeSkillMaster")):
                accounts.append(account_name)
        return accounts


    def _addons_folder_changed_delayed(self):
        self._addons_folder_change_scheduled = False
        self.addons_folder_changed.emit()


    def find_wow_path(self):
        if Config.IS_WINDOWS:
            import string
            from ctypes import windll

            search_paths = []
            bitmask = windll.kernel32.GetLogicalDrives()
            for drive in ["{}:\\".format(c) for i, c in enumerate(string.ascii_uppercase) if bitmask & (1 << i)]:
                try:
                    if windll.kernel32.GetDriveTypeW(drive) == 3: # magic number for the "fixed" drive type
                        for sub_path in ["", "Games", "Program Files", "Program Files (x86)"]:
                            search_paths.append(os.path.join(drive, sub_path, "World of Warcraft"))
                except Exception as e:
                    logging.getLogger().error("Could not lookup drive type for '{}' ({})".format(drive, str(e)))
        elif Config.IS_MAC:
            search_paths = [os.path.join("~/Applications", "World of Warcraft")]
        elif Config.IS_LINUX:
            search_paths = [os.path.expanduser("~/.wine/drive_c/Program Files (x86)/World of Warcraft")]
        else:
            raise Exception("Unexpected platform")
        for path in search_paths:
            if self.set_wow_path(path):
                return


    def directory_changed(self, path):
        if path == self._get_addon_path():
            if not self._addons_folder_change_scheduled:
                self._addons_folder_change_scheduled = True
                QTimer.singleShot(5000, self._addons_folder_changed_delayed)


    def set_wow_path(self, path):
        # We'll validate the WoW folder by checking for Interface/Addons and WTF folders
        if not (os.path.isdir(os.path.abspath(os.path.join(path, "Interface", "Addons"))) or os.path.isdir(os.path.abspath(os.path.join(path, "Interface", "AddOns")))) or not os.path.isdir(os.path.abspath(os.path.join(path, "WTF"))):
            if self._settings.wow_path != "":
                self._watcher.removePath(self._get_addon_path())
            self._settings.wow_path = ""
            self._valid_wow_path = False
            return False
        self._valid_wow_path = True
        # store the new path
        prev_wow_path = self._settings.wow_path
        self._settings.wow_path = os.path.abspath(path)
        logging.getLogger().info("WoW path is set to '{}'".format(self._settings.wow_path))
        # update the directory watcher
        if prev_wow_path != "":
            self._watcher.removePath(self._get_addon_path())
        self._watcher.addPath(self._get_addon_path())
        return True


    def has_valid_wow_path(self):
        return self._valid_wow_path


    def get_installed_version(self, addon):
        if self._settings.wow_path == "":
            return self.INVALID_VERSION, 0, ""
        # look at the addon's TOC file to get the current version
        toc_path = os.path.abspath(os.path.join(self._get_addon_path(addon), "{}.toc".format(addon)))
        if not os.path.isfile(toc_path):
            return self.INVALID_VERSION, 0, ""
        # get the version as a string
        version_str = None
        with open(toc_path, encoding="utf8", errors="replace") as toc_file:
            for line in toc_file:
                if "## Version:" in line:
                    version_str = line[len("## Version:"):].strip()
        if not version_str:
            return self.INVALID_VERSION, 0, ""
        elif version_str == "@project-version@":
            # this is a dev version
            return self.DEV_VERSION, -1, "Dev"
        elif version_str[0] == "v":
            # this is a release version
            parts = version_str[1:].split(".")
            # check that the parts are all numeric
            if not all(x.isdigit() for x in parts):
                logging.getLogger().error("Invalid version line for {}: {}".format(addon, version_str))
                return self.INVALID_VERSION, 0, ""
            if len(parts) == 2:
                return self.RELEASE_VERSION, int(parts[0]) * 1000000 + int(parts[1]) * 10000, version_str
            elif len(parts) == 3:
                return self.RELEASE_VERSION, int(parts[0]) * 1000000 + int(parts[1]) * 10000 + int(parts[2]) * 100, version_str
            elif len(parts) == 4:
                return self.RELEASE_VERSION, int(parts[0]) * 1000000 + int(parts[1]) * 10000 + int(parts[2]) * 100 + int(parts[3]), version_str
        else:
            logging.getLogger().error("Invalid version line for {}: {}".format(addon, version_str))
        return self.INVALID_VERSION, 0, ""


    def delete_addon(self, addon):
        assert(addon)
        addon_dir = self._get_addon_path(addon)
        # try deleting the addon directory 3 times
        retries = 3
        while True:
            try:
                if os.path.isdir(addon_dir):
                    rmtree(addon_dir)
                break
            except OSError as e:
                logging.getLogger().error("Failed to remove addon ({}, {}): {}".format(addon, retries, str(e)))
                if retries == 0:
                    raise
                retries -= 1


    def install_addon(self, addon, zip):
        # remove the addon if it already exists
        self.delete_addon(addon)
        zip.extractall(self._get_addon_path())


    def get_app_data(self):
        path = os.path.join(self._get_addon_path("TradeSkillMaster_AppHelper"), "AppData.lua")
        if not os.path.isfile(path):
            return None
        return AppData(path)


    def get_accounting_accounts(self):
        result = {}
        for account_name in self.get_accounts():
            data = self._get_saved_variables(account_name, "TradeSkillMaster_Accounting")
            if data:
                try:
                    result[account_name] = [x for x in data['_scopeKeys']['realm'].values()]
                except KeyError:
                    pass
        return result


    def export_accounting_csv(self, account, realm, key):
        DB_KEYS = {
            'sales': "csvSales",
            'purchases': "csvBuys",
            'income': "csvIncome",
            'expenses': "csvExpense",
            'expired': "csvExpired",
            'canceled': "csvCancelled"
        }
        path = os.path.join(QStandardPaths.writableLocation(QStandardPaths.DesktopLocation), "Accounting_{}_{}.csv".format(realm, key))
        try:
            data = self._get_saved_variables(account, "TradeSkillMaster_Accounting")
            if not data:
                return
            item_names = data["g@ @itemStrings"]
            data = data["r@{}@{}".format(realm, DB_KEYS[key])]
        except KeyError as e:
            logging.getLogger().error("Failed to export accounting data ({}, {}, {}): {}".format(account, realm, key, str(e)))
            return
        if type(data) != str:
            logging.getLogger().error("Failed to export accounting data ({}, {}, {})".format(account, realm, key))
            return
        keys, data = self._parse_csv(data)
        item_lookup = {}
        if 'itemString' in keys and 'itemName' not in keys:
            keys.insert(1, "itemName")
            for item_name, item_string in item_names.items():
                item_lookup[item_string] = item_name.replace(',', '')
        with open(path, 'w', encoding="utf8", errors="replace") as f:
            try:
                rows = [','.join(keys)]
                for row in data:
                    row_values = []
                    for item_key in keys:
                        if item_key == "itemName":
                            if item_key in row and row[item_key] != "?":
                                row_values += [row[item_key]]
                            elif row['itemString'] in item_lookup:
                                row_values += [item_lookup[row['itemString']]]
                            else:
                                row_values += ["?"]
                        else:
                            row_values += [row[item_key]]
                    rows += [','.join(row_values)]
                f.write('\n'.join(rows))
            except KeyError as e:
                logging.getLogger().error("Failed to export accounting data ({}, {}, {}): {}".format(account, realm, key, str(e)))
                return

        # data = data.replace("\\n", "\n")
        # with open(path, 'w', encoding="utf8", errors="replace") as f:
            # f.write(data)
        logging.getLogger().info("Exported accounting data to {}".format(path))


    def set_addons_and_do_backups(self, addons):
        self._addons = addons
        return self._do_backup()


    def _saved_variables_iterator(self, account):
        for addon in self._addons:
            sv_path = self._get_saved_variables_path(account, addon)
            if os.path.isfile(sv_path):
                yield sv_path


    def _do_backup(self, account=None):
        accounts = [account] if account else self.get_accounts()
        backed_up = []
        backups = self.get_backups()
        for account_name in accounts:
            # delete expired backups first so we'll do a new backup if the most recent one expired
            backup_times = []
            for backup in [x for x in backups if x.account == account_name]:
                path = os.path.join(Config.BACKUP_DIR_PATH, backup.get_local_zip_name())
                if (datetime.now() - backup.timestamp) > timedelta(seconds=self._settings.backup_expire):
                    logging.getLogger().info("Purged old backup for account ({}): {}".format(account_name, path))
                    os.remove(path)
                else:
                    backup_times.append(backup.timestamp)

            # check if the files have changed since the last backup - if not, don't take a new backup
            modified_times = [int(os.path.getmtime(sv_path)) for sv_path in self._saved_variables_iterator(account_name)]
            if not modified_times:
                logging.getLogger().info("No files to back-up for account ({})".format(account_name))
                continue
            elif backup_times:
                last_backup = max(backup_times)
                if datetime.fromtimestamp(max(modified_times)) < last_backup:
                    logging.getLogger().info("No update since last backup for account ({})".format(account_name))
                    continue
                elif (datetime.now() - last_backup) < timedelta(seconds=self._settings.backup_period):
                    logging.getLogger().info("Backup period hasn't yet passed for account ({})".format(account_name))
                    continue

            # do the backup
            assert(Config.BACKUP_NAME_SEPARATOR not in Config.BACKUP_TIME_FORMAT)
            if Config.BACKUP_NAME_SEPARATOR in account_name:
                # can't backup this account
                continue
            new_backup = Backup(system_id=Config.SYSTEM_ID, account=account_name, raw_timestamp=int(time()), is_local=True, is_remote=False)
            with ZipFile(os.path.join(Config.BACKUP_DIR_PATH, new_backup.get_local_zip_name()), 'w', ZIP_LZMA) as zip:
                for sv_path in self._saved_variables_iterator(account_name):
                    zip.write(sv_path, os.path.basename(sv_path))
            backed_up.append(new_backup)
            logging.getLogger().info("Created backup for account ({})".format(account_name))
        return backed_up


    def get_backups(self):
        backups = []
        if not os.path.isdir(Config.BACKUP_DIR_PATH):
            os.makedirs(Config.BACKUP_DIR_PATH, exist_ok=True)
        for file_path in os.listdir(Config.BACKUP_DIR_PATH):
            try:
                backups.append(Backup(zip_name=os.path.basename(file_path), is_local=True, is_remote=False))
            except ValueError:
                pass
        return backups


    def restore_backup(self, backup):
        if backup.is_local:
            zip_path = os.path.abspath(os.path.join(Config.BACKUP_DIR_PATH, backup.get_local_zip_name()))
        else:
            zip_path = os.path.abspath(os.path.join(self._temp_backup_path, backup.get_remote_zip_name()))
        if not os.path.isfile(zip_path):
            logging.getLogger().error("Could not find backup: {}".format(zip_path))
            return False
        with ZipFile(zip_path) as zip:
            zip.extractall(self._get_saved_variables_path(backup.account))
        logging.getLogger().info("Restored backup ({})".format(str(backup)))
        return True


    def get_black_market_data(self):
        result = {}
        for account in self.get_accounts():
            data = self._get_saved_variables(account, "TradeSkillMaster_AppHelper")
            if not data:
                continue
            try:
                account_data = data["blackMarket"]
                region = data["region"]
                if not account_data or not region:
                    continue
            except KeyError as e:
                logging.getLogger().warn("No black market data for {}".format(account))
                continue
            for realm, data in account_data.items():
                if data['updateTime'] < (int(time()) - Config.MAX_DATA_AGE):
                    # data is too old to bother uploading
                    continue
                key = (region, realm)
                if key not in result or result[key]['updateTime'] < data['updateTime']:
                    result[key] = data
        return result


    def get_wow_token_data(self):
        result = {}
        for account in self.get_accounts():
            data = self._get_saved_variables(account, "TradeSkillMaster_AppHelper")
            if not data:
                continue
            try:
                account_data = data['wowToken']
                if not account_data:
                    continue
            except KeyError as e:
                logging.getLogger().warn("No WoW token data for {}".format(account))
                continue
            for region, region_data in account_data.items():
                if region_data['updateTime'] < (int(time()) - Config.MAX_DATA_AGE):
                    # data is too old to bother uploading
                    continue
                if region not in result or result[region]['updateTime'] < region_data['updateTime']:
                    result[region] = region_data
        return result


    def get_analytics_data(self):
        result = {}
        for account in self.get_accounts():
            data = self._get_saved_variables(account, "TradeSkillMaster_AppHelper")
            if not data:
                continue
            try:
                account_data = data['analytics']
                if not account_data:
                    continue
            except KeyError as e:
                logging.getLogger().warn("No analytics data for {}".format(account))
                continue
            result[account] = {
                'data': "[" + ",".join(account_data['data'].values()).replace("\\", "") + "]",
                'updateTime': account_data['updateTime']
            }
        return result


    def _parse_csv(self, data):
        import csv
        result = []
        rows = [x for x in csv.reader(data.split('\\n'), delimiter=',')]
        if len(rows) <= 1:
            return None, None
        keys = rows.pop(0)
        for row in rows:
            if len(row) != len(keys):
                # invalid row
                return None, None
            result_row = {}
            for i, cell_value in enumerate(row):
                result_row[keys[i]] = cell_value
            result.append(result_row)
        return keys, result


    def get_accounting_data(self):
        result = {}
        for account in self.get_accounts():
            app_helper_data = self._get_saved_variables(account, "TradeSkillMaster_AppHelper")
            if not app_helper_data:
                continue
            region = app_helper_data['region'] if 'region' in app_helper_data else None
            if not region:
                continue
            data = self._get_saved_variables(account, "TradeSkillMaster_Accounting")
            if not data or '_scopeKeys' not in data or 'realm' not in data['_scopeKeys']:
                continue
            for realm in data['_scopeKeys']['realm'].values():
                def parse_data_helper(key, filter_by_source):
                    if key not in data:
                        return None
                    parsed_keys, parsed_data = self._parse_csv(data[key])
                    if not parsed_data:
                        return None
                    if filter_by_source:
                        return [x for x in parsed_data if 'source' in x and x['source'] == "Auction"]
                    else:
                        return parsed_data
                sales = parse_data_helper("r@{}@csvSales".format(realm), True)
                buys = parse_data_helper("r@{}@csvBuys".format(realm), True)
                expires = parse_data_helper("r@{}@csvExpired".format(realm), False)
                cancels = parse_data_helper("r@{}@csvCancelled".format(realm), False)
                def parse_save_time_helper(key):
                    if key not in data:
                        return None
                    return [int(x) for x in data[key].split(",") if x.isdigit()]
                save_time_sales = parse_save_time_helper("r@{}@saveTimeSales".format(realm))
                save_time_buys = parse_save_time_helper("r@{}@saveTimeBuys".format(realm))
                save_time_expires = parse_save_time_helper("r@{}@saveTimeExpires".format(realm))
                save_time_cancels = parse_save_time_helper("r@{}@saveTimeCancels".format(realm))
                account_data = {'data': {}, 'updateTime': 0}
                def process_data_iterator(data, save_times, has_price):
                    if not data or not save_times or len(data) != len(save_times):
                        return
                    for i, record in enumerate(data):
                        item_string_parts = record['itemString'].split(":")
                        if item_string_parts[0] == "i":
                            try:
                                price = int(record['price']) if has_price else 0
                                yield int(item_string_parts[1]), price, int(record['stackSize']), int(record['quantity']), int(record['time']), int(save_times[i])
                            except ValueError:
                                pass
                for item_id, price, stack_size, quantity, sale_time, save_time in process_data_iterator(sales, save_time_sales, True):
                    if item_id not in account_data['data']:
                        account_data['data'][item_id] = []
                    account_data['data'][item_id].append([price, stack_size, quantity, sale_time, save_time, 2])
                    account_data['updateTime'] = max(account_data['updateTime'], save_time)
                for item_id, price, stack_size, quantity, sale_time, save_time in process_data_iterator(buys, save_time_buys, True):
                    if item_id not in account_data['data']:
                        account_data['data'][item_id] = []
                    account_data['data'][item_id].append([price, stack_size, quantity, sale_time, save_time, 3])
                    account_data['updateTime'] = max(account_data['updateTime'], save_time)
                for item_id, price, stack_size, quantity, sale_time, save_time in process_data_iterator(expires, save_time_expires, False):
                    if item_id not in account_data['data']:
                        account_data['data'][item_id] = []
                    account_data['data'][item_id].append([price, stack_size, quantity, sale_time, save_time, 4])
                    account_data['updateTime'] = max(account_data['updateTime'], save_time)
                for item_id, price, stack_size, quantity, sale_time, save_time in process_data_iterator(cancels, save_time_cancels, False):
                    if item_id not in account_data['data']:
                        account_data['data'][item_id] = []
                    account_data['data'][item_id].append([price, stack_size, quantity, sale_time, save_time, 5])
                    account_data['updateTime'] = max(account_data['updateTime'], save_time)
                if account_data:
                    result[(region, realm, account)] = account_data
        return result


    def get_group_data(self):
        result = {}
        for account in self.get_accounts():
            account_data = {}
            data = self._get_saved_variables(account, "TradeSkillMaster_AppHelper")
            if not data:
                continue
            try:
                account_data = data["shoppingMaxPrices"]
                region = data["region"]
                if not account_data or not region:
                    continue
            except KeyError as e:
                logging.getLogger().warn("No shopping data for {}".format(account))
                continue
            for profile, data in account_data.items():
                data = data.copy()
                update_time = data.pop('updateTime', None)
                if update_time:
                    account_data[profile] = {'updateTime': update_time, 'data': data}
            for profile, data in account_data.items():
                data['profiles'] = list(account_data.keys())
                result[(account, profile)] = data
        return result
