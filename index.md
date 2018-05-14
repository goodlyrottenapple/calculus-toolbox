---
layout: default
title: "Calculus Toolbox Docs Home"
---

### Get started

To try to make setting up the calculus toolbox as simple as possible, we now recommend installing the toolbox using [Docker](https://www.docker.com). Please install Docker for your platform and then follow the setup guide below.

## Compiled toolboxes
If you just want to test out a toolbox GUI generated from a JSON description file, compiled toolboxes for the D.EAK calculus and a version of an LK Sequent calculus fragment are available as Scala JAR files (these have been tested on Linux and macOS):

- [DEAK-calculus-tool](https://github.com/goodlyrottenapple/calculus-toolbox/raw/master/calculi/DEAK.jar)
- [Sequent-calculus-tool](https://github.com/goodlyrottenapple/calculus-toolbox/raw/master/calculi/Sequent.jar)

Please ensure you have Java 8.0 or older and Scala 2.12.0 or older on your system. In order to launch the toolbox, run

```bash
scala DEAK.jar
```

or

```bash
scala Sequent.jar
```

## Installing Docker

- macOS: For macOS, simply download the [Docker CE desktop app](https://download.docker.com/mac/stable/Docker.dmg) and install it on your system.
- Ubuntu: Follow this [guide](https://www.digitalocean.com/community/tutorials/how-to-install-and-use-docker-on-ubuntu-16-04) to install Docker on Ubuntu
- Other Linux: Check the [Docker documentation](https://docs.docker.com/engine/installation/) for install instructions for other Linux distributions.
- Windows 10: Download [Docker CE for Windows](https://download.docker.com/win/stable/Docker%20for%20Windows%20Installer.exe) and install it on your system. Please see the [docs](https://docs.docker.com/docker-for-windows/install/#what-to-know-before-you-install) for further information on installing and using Docker on Windows.

## Setup

First, download or fork this repository, then, inside the repo, run:

```bash
./run.sh
```

This script will download and compile all the dependencies and launch a sandboxed environment shell for building custom calculi toolboxes. 

--------

### Windows

If on Windows, you will have to run the commands inside the bash script `run.sh` manually. First open PowerShell, navigate to the calculus-toolbox folder and run:

```bash
docker build -t calculus-toolbox .
```

Once the build is finished, launch the sandboxed shell by running:

```bash
docker run -ti -v %cd%/calculi:/root/calculi calculus-toolbox
```

--------

The JSON description files can be found in the `calculi` folder and this also where you should save your own JSON description files. To build a calculus from a description file, simply run:

```bash
./build.py -c calculi/<your_json_file>.json
```

The JSON file will be compiled into the `gen_calc` folder. In order to generate a JAR file of the custom calculus toolbox, run the following commands:

```bash
cd gen_calc
./build
mv calc.jar ../calculi/calc.jar
```

To exit the Docker sandbox shell, press Control (Command on Mac) + D. In order to run the compiled JAR file, run:

```bash
scala calculi/calc.jar
```

(This is assuming that you have Java 8.0 or older and Scala 2.12.0 or older installed on your system)

For more information on how the toolbox works, head to the [Introduction](https://goodlyrottenapple.github.io/calculus-toolbox/doc/introduction.html) page.

