# calculus-toolbox
A set of tools for generating calculi in Isabelle and supporting tools through a JSON description file

To try to make setting up the calculus toolbox as simple as possible, we now recommend installing the toolbox using [Docker](https://www.docker.com). Please install Docker for your platform and then follow the setup guide below.

## Installing Docker

- macOS: For macOS, simply download the [Docker CE desktop app](https://download.docker.com/mac/stable/Docker.dmg) and install it on your system.
- Ubuntu: Follow this [guide](https://www.digitalocean.com/community/tutorials/how-to-install-and-use-docker-on-ubuntu-16-04) to install Docker on Ubuntu
- Other linux: Check the [Docker documentation](https://docs.docker.com/engine/installation/) for install instructions for other linux distributions.
- Windows 10: Download [Docker CE for Windows](https://download.docker.com/win/stable/Docker%20for%20Windows%20Installer.exe) and install it on your system. Please see the [docs](https://docs.docker.com/docker-for-windows/install/#what-to-know-before-you-install) for further information on installing and using Docker on Windows.

## Setup

First, download or fork this repository, then, inside the repo, run:

```bash
./run.sh
```

This script will download and compile all the dependencies and launch a sandboxed environment shell for building custom calculi toolboxes. 

--------

### Windows

If on Windows, you will have to run the commands inside the bash script `run.sh` manually. First open PowerShell, navigate to the repo folder and run:

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

To exit the Docker sandox shell, press Control (Command on Mac) + D. In order to run the compiled JAR file, run:

```bash
scala calculi/calc.jar
```

(This is assuming that you have Java 8.0 or older and Scala 2.12.0 or older installed on your system)

For more information on how the toolbox works, head to the [Introduction](https://goodlyrottenapple.github.io/calculus-toolbox/doc/introduction.html) page.

## Compiled toolboxes
Compiled toolboxes for the D.EAK calculus and a version of an LK Sequent calculus fragment are available as Scala JAR files:

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


## OLD SETUP:
### Get started

To get started, fork the [github repository](https://github.com/goodlyrottenapple/calculus-toolbox) or download the project as a [zip file](https://github.com/goodlyrottenapple/calculus-toolbox/archive/master.zip) and then head over to the [Introduction](https://goodlyrottenapple.github.io/calculus-toolbox/doc/introduction.html) page.

**If you are using an older version of Isabelle (2014/2015), switch to the `isabelle2015` branch  via `git checkout isabelle2015`.**

### System requirements

To run the tools in the Calculus Toolbox, you need the following:

- Isabelle2016 (`isabelle` needs to be added to bash PATH) (if running Isabelle2014, please use the `--isa2014` flag when compiling the calculus)
- Scala (preferred 2.10 or higher)
- Python (2.7 or higher)
- (optional) `npyscreen` and `watchdog` python modules
