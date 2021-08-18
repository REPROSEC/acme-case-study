# Supplementary Material to "An In-Depth Symbolic Security Analysis of the ACME Standard"

For an overview, see our CCS '21 paper "An In-Depth Symbolic Security
Analysis of the ACME Standard".

In this README, we give an overview on how to verify the F* ACME
model, how to run the symbolic tests and finally how to use the OCaml
wrapper library to run our model with a real-world ACME server,
including Let's Encrypt's production servers.


## Preparations

While all verification, compilation etc. should work with any recent
version of F* and OCaml, we provide a docker container and a
docker-compose setup to make verification and testing as easy as
possible.  Note however that this setup assumes to be run on a *nix
operating system.  Using, e.g., VirtualBox with a recent Ubuntu Linux,
such an environment can be created on almost every machine.

1. Download and install docker & docker-compose for your host platform.
   See [docker website](https://www.docker.com/)

2. Make sure that the docker service is started (you may need to
   restart your machine for this).

3. In the directory of this readme, run `docker-compose up -d`. This
   will download and start all required containers.

4. To get a shell prompt inside the correct container, run
   `docker exec -it fstar-emacs /bin/bash`

5. Now you should see a shell prompt inside the docker
   container. Switch to the model directory with `cd acmestar/`.  See
   the next subsections for further instructions (note that all
   verification/compilation commands in the following subsections
   assume that you start out in a shell inside the docker container in
   the `acmestar` directory).

6. After verifying, testing, ...; shut down all containers by running
   `docker-compose down` (in the directory with this readme).

## Directory structure

Next to this readme, there is a `Makefile`, a script to apply for an
ACME account at different servers (explained below) called
`new_acme_account.py`, a `main.ml` which is the entry point for our
interoperable client and finally directories `fstar` and
`wrapper_lib`.

`wrapper_lib` contains the code for the OCaml wrapper which translates
between real network messages and abstract DY* terms.

`fstar` contains the F* files of the (extended) DY* model and another
directory `acme` which contains our ACME model (including scheduling
code for functional tests).


## Verify DY* and ACME model

To verify DY*, `cd` into the `fstar` directory and run `make`.
Similarly, to verify the ACME model, `cd` into `fstar/acme` and run
`make` there.

You can also just run `make` from the root directory (i.e., the one
with this readme), this will not only verify DY* and the ACME model,
but also build the interoperable client.


## Run functional (symbolic) tests

To run our functional tests, make sure to first verify DY* and the
ACME model, then `cd` into `fstar/acme` and run `make test`.  This
invokes the so-called *extraction*, i.e., compilation from F* to
OCaml, followed by compilation from OCaml to an executable.  The
resulting executable is `fstar/acme/ocaml/test.exe`, which can be
started by `cd`ing into `fstar/acme/ocaml/` and running `./test.exe`
there.


## Run the interoperable ACME client

### Compilation

To compile the interoperable client, run `make` in the directory of
this readme.

### ACME server selection & account creation

Now, select an ACME server against which you want to run the
interoperable client.  While our interoperable client can be used with
any ACME server, we provide a convenient way to generate the necessary
configuration files for three servers:

  1. pebble. Pebble is an ACME compliance testing tool and implements
     an ACME server which, e.g., randomizes the order or sequences
     wherever allowed by the ACME standard. A pebble server is already
     running in a separate container (assuming you used our
     docker-compose setup).  You can order certificates for arbitrary
     domains. Of course, certificates issued by pebble are rejected by
     virtually all systems.
  2. Let's Encrypt Staging. Configured very similar to the "real"
     Let's Encrypt servers, the staging area is meant for testing,
     issuing certificates that will be rejected by virtually all
     systems.  Note that you need to be able to put a text file with
     an arbitrary name and content on (HTTP) path
     `.well_known/acme_challenge/` for each ordered domain (otherwise,
     the protocol flow cannot be finished).
  3. Let's Encrypt Production. The "real" Let's Encrypt servers,
     issuing valid, widely-accepted certificates. Note that you need
     to be able to put a text file with an arbitrary name and content
     on (HTTP) path `.well_known/acme_challenge/` for each ordered
     domain (otherwise, the protocol flow cannot be finished).

If you chose the pebble server, you now need to set up the system
running in the docker container to trust pebble's temporary
certificate (ACME requires use of TLS). Run
`export REQUESTS_CA_BUNDLE='pebble.minica.pem'` to do so. If you're testing
outside of docker, make sure to run `unset REQUESTS_CA_BUNDLE`
after you're done testing!

Now run the script `new_acme_account.py` (located next to this readme)
with the following arguments (see also `./new_acme_account.py -h`):

  - `-s <server>`, where `<server>` is one of `pebble`, `le_staging`,
    `le` (as explained above)
  - `-d <domain>` or `-d <domain1> <domain2> ...`: The domains you
    intend to order - these domains are not necessary to create an
    ACME account, but they end up in the same configuration file.

This will create an account at the specified server and suitable
configuration files for our ACME client: one called
`private_key_<server>.json` and one called `<server>_config.yaml`

### Get a certificate from pebble

If you're using our docker-compose setup, most things are already in
place, just run `./main.exe -c pebble_config.yaml`. The ACME
challenges will be provisioned automatically (this is possible using
another testing tool developed for use with pebble: the
"challtestsrv", see below for details on all the containers in use).

### Get a certificate from Let's Encrypt (staging or production)

To get a certificate from Let's Encrypt, first turn off the automatic
provisioning of challenges on the (local) *challtestsrv* container:
`unset PROVISION_KEY_AUTHZ_TO_CHALL_TEST_SRV`

Now start the interoperable ACME client:
`./main.exe -c le_config.yaml`
(or `./main.exe -c le_staging_config.yaml` when using
Let's Encrypt staging).

At some point, the ACME client will ask you to provision a challenge
for the ordered domain (i.e., put a text file with a certain name and
content under `<domain>/.well_known/acme_challenge`). Do so and press
Enter to continue the protocol flow. If you've ordered multiple
domains, this process is repeated for every domain. Once all domains
are verified, the client will output the certificate (chain) it
received from Let's Encrypt.


## Technical information: Containers in use (for local testing)

As you can see in the `docker-compose.yml` file, we use Let's
Encrypt's [pebble](https://github.com/letsencrypt/pebble) ACME test
server for local testing.  Pebble is a minimal implementation of an
ACME server as defined by RFC 8555 explicitly designed to test ACME
clients (e.g., it randomizes URLs etc. in such a way that clients
cannot make any assumptions except for what RFC 8555 defines - this
ensures that clients tested against pebble will not rely on a specific
ACME server implementation like boulder).

In addition to pebble, we need a (local) web server which can serve
the ACME challenge response to the ACME server (pebble in our
case). Once again, we use a tool provided by Let's Encrypt: [Challenge
Test Server](https://github.com/letsencrypt/challtestsrv) It provides
a convenient way to provision challenge responses and (mock) DNS
responses.  While we could have added such a server component to the
container running our verified client, we chose to keep ACME client
and web server separated to prove that our client can be used with any
web server. Note that you can configure the client's container such
that it does not use the Challenge Test Server, but outputs the
necessary data to provision the challenge response on any other server
(set `PROVISION_KEY_AUTHZ_TO_CHALL_TEST_SRV` to `false`).

The third container provides the necessary build and linking tools to
verify & extract F* code and compile OCaml code. This is where our
verified ACME client can be built & run.
