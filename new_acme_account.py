#!/usr/bin/python3

from certbot import main
import os
import json
import shutil
import argparse


CERTBOT_WORKING_DIR = "./certbot"

def run():
    parser = argparse.ArgumentParser(description="Helper script to get an ACME account at an ACME server and convert "
                                                 "the account data in a format suitable for our interoperable ACME "
                                                 "client, including creation of a configuration file.",
                                     epilog="Note: When using the local pebble server, you have to overwrite the list "
                                            "of trusted CAs for python's requests library. This is necessary because "
                                            "pebble (on purpose!) does not run with a valid TLS certificate, but "
                                            "registering an ACME account requires an HTTPS connection. So before "
                                            "running this script with a pebble server, set the environment variable "
                                            "REQUESTS_CA_BUNDLE to 'pebble.minica.pem' (that file can be found right "
                                            "next to this script). Make sure to unset that variable once you're done"
                                            " testing!")
    parser.add_argument("-s", "--server", choices=["pebble", "le_staging", "le"], default='pebble',
                        help="The server for which an account is created. Note that this script only supports a small "
                             "selection of ACME servers - if you want to use another server, see the implementation of "
                             "this script for how to get the necessary account data. The choices are: 1) pebble: A "
                             "local pebble instance, assuming you used the docker-compose.yml file next to this script."
                             " 2) le_staging: The Let's Encrypt staging environment. 3) le: The Let's Encrypt "
                             "production environment.  The default is pebble."
                        )
    parser.add_argument("-c", "--cfg-file", help="Base name of the config files to write. Generally, two files will be "
                                                 "produced: private_key_<base name>.json and <base name>_config.yaml. "
                                                 "By default, the value of --server will be used.")
    parser.add_argument("-d", "--domain", nargs='*', default=[],
                        help="Domains for which you plan to order certificates. While this is not related to account "
                             "creation, the list of domains is part of the configuration file written by this script. "
                             "You can edit the list of domains later without running this script again. Default is an "
                             "empty list.")
    args = parser.parse_args()
    if not args.cfg_file:
        args.cfg_file = args.server

    if args.server == "pebble" and os.getenv("REQUESTS_CA_BUNDLE") != "pebble.minica.pem":
            print("ERROR: You're trying to communicate with a pebble test server which does not have\n"
                  "a valid TLS certificate. This won't work. Please set the environment variable\n"
                  "REQUESTS_CA_BUNDLE to 'pebble.minica.pem' and run this script again. I.e., run\n"
                  "export REQUESTS_CA_BUNDLE='pebble.minica.pem'\n"
                  "This overwrites the TLS root CA store for the python requests library. So make sure to\n"
                  "UNSET this variable once you're done testing! (I.e., run 'unset REQUESTS_CA_BUNDLE').")
            return
    if args.server != "pebble" and os.getenv("REQUESTS_CA_BUNDLE") == "pebble.minica.pem":
        print("ERROR: You've set REQUESTS_CA_BUNDLE to 'pebble.minica.pem', but are trying to register an account "
              "at a Let's Encrypt server. This won't work. Please unset REQUESTS_CA_BUNDLE and run this script again.")
        return
    if os.getenv("PROVISION_KEY_AUTHZ_TO_CHALL_TEST_SRV") == "true" and args.server != "pebble":
        print("WARNING: Environment variable PROVISION_KEY_AUTHZ_TO_CHALL_TEST_SRV is set to 'true'. This means that "
              "our ACME client will try to provision authorizations automatically to a local pebble test server. But "
              "you've selected a different server. So you may want to unset PROVISION_KEY_AUTHZ_TO_CHALL_TEST_SRV "
              "before running the client (otherwise, the client will not wait for you to provision challenges before "
              "triggering verification).")

    if args.server == "pebble":
        server_directory_url = 'https://pebble:14000/dir'
        accounts_data_dir = f"{CERTBOT_WORKING_DIR}/accounts/pebble:14000/dir"
    elif args.server == "le_staging":
        server_directory_url = "https://acme-staging-v02.api.letsencrypt.org/directory"
        accounts_data_dir = f"{CERTBOT_WORKING_DIR}/accounts/acme-staging-v02.api.letsencrypt.org/directory"
    elif args.server == "le":
        server_directory_url = "https://acme-v02.api.letsencrypt.org/directory"
        accounts_data_dir = f"{CERTBOT_WORKING_DIR}/accounts/acme-v02.api.letsencrypt.org/directory"
    else:
        print(f"Unknown server '{args.server}'. Aborting.")
        return

    private_key_file = f"./private_key_{args.cfg_file}.json"
    config_file_name = f"./{args.cfg_file}_config.yaml"


    print("Registering a new account on", server_directory_url)

    # Delete existing accounts (otherwise, certbot will not register a new one)
    shutil.rmtree(CERTBOT_WORKING_DIR, ignore_errors=True)
    # Re-create directory (certbot won't do that by itself)
    os.mkdir(CERTBOT_WORKING_DIR)

    # Register account
    certbot_args = ["register",
                    "--config-dir", CERTBOT_WORKING_DIR,
                    "--work-dir", CERTBOT_WORKING_DIR,
                    "--logs-dir", CERTBOT_WORKING_DIR,
                    "--server", server_directory_url,
                    "--register-unsafely-without-email",
                    "--agree-tos"]
    r = main.main(certbot_args)

    if type(r) is str:
        print(r)

    # Get account data
    if not os.path.isdir(accounts_data_dir):
        print("No account data found! Exiting.")
        return

    account_data_dir = os.path.join(accounts_data_dir, os.listdir(accounts_data_dir)[0])

    # Copy key file
    with open(os.path.join(account_data_dir, 'private_key.json'), 'r') as key_file:
        l = key_file.readlines()
    with open(private_key_file, 'w') as key_file:
        key_file.writelines(l)

    # Get kid
    with open(os.path.join(account_data_dir, 'regr.json'), 'r') as misc_account_data_file:
        kid = json.load(misc_account_data_file)['uri']

    # Write config file for OCaml
    config_lines = [
        f"acme_server_directory_url: '{server_directory_url}'\n",
        f"account_key_location: '{private_key_file}'\n",
        f"kid: '{kid}'\n",
        f"cert_domains: {args.domain}\n"
    ]

    with open(config_file_name, 'w') as config_file:
        config_file.writelines(config_lines)
    print("Wrote config to", config_file_name)


if __name__ == "__main__":
    run()
