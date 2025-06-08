[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# **HistFuzz-demo**

This is the instruction for the paper *Validating SMT Solvers via Skeleton Enumeration Empowered by Historical Bug-Triggering Inputs* for ICSE AE track.

## **Description**

$\mathrm{HistFuzz}$ utilizes historical data to test SMT solvers.
<br>

The following table shows the important files and their purposes in this artifact, which may help you use the artifact with a good experience.

| File name      | Purpose |
| ----------- | ----------- |
| [LICENSE](LICENSE)     | description of the distribution rights       |
| [README](README.md)   | guidance on how to read the documentation        |
| [STATUS](STATUS.md)  |  the badges we are applying for and the reasons |
| [REQUIREMENTS](REQUIREMENTS.md)  | requirements needed with building from source |
| [INSTALL](INSTALL.md)  | installation guidance needed with building from source |

The purpose of this artifact is to reproduce the main results in our original paper. More details in [Evaluation](#evaluation).

Besides, this [file](STATUS.md) states the badges we are applying for as well as the reasons why we believe that the artifact deserves the badges.

<!--
## **QuickStart**

We recommend users to use docker container to evaluate the artifacts.
-->


## **Installation**

There are two ways to run $\mathrm{HistFuzz}$ and reproduce the results on your machines.

* ![Recommended-Yes](https://img.shields.io/badge/Recommended-Yes-brightgreen) **Downloading Docker Image.** For macOS or Linux users, you can directly use the command `docker pull histfuzz/histfuzz; docker run -it histfuzz/histfuzz /bin/bash` to obtain and get into the Docker container. Alternatively, you can also download the Docker container image from the [Zenodo repository](https://doi.org/10.5281/zenodo.7631379), and follow the following commands to get into the container. 
 
    For Windows users, you need to download [docker desktop](https://www.docker.com/products/docker-desktop) and [Cygwin](https://www.cygwin.com/) first and make sure that there is no error message when the docker destop starts for the first time. Then, you need to open Cygwin and run the commands below. If there is any error messages, please follow the pop-up link to fix the problems. Usually, the problem is that BIOS disables cpu virtualization function. You can fix it by entering BIOS, enabling the function, and restarting.

```
# You can download the Image package histfuzz.tar.zip (about 4G) from the link <https://doi.org/10.5281/zenodo.7631379>.
unzip histfuzz.tar.zip
# import as a Docker Image
docker import histfuzz.tar # This process may take a few minutes depending on the machine performance. When the process finishes, the image id will show on the screen.
# get into the container
docker run -it [image id] /bin/bash 
```


* ![Recommended-No](https://img.shields.io/badge/Recommended-No-red) 
**Building from Source Code.** The installation guidance is successfully tested on a machine with Ubuntu 20.04 and 22.04. The requirements are listed in [REQUIREMENTS](REQUIREMENTS.md). You can successfully build the tools and reproduce the evaluation by following the guidance in [Evaluation](#evaluation). We DO NOT recommend building from source because there are many dependencies and the subjects of the experiments.



## **Evaluation**

The evaluation results of $\mathrm{HistFuzz}$ include two tasks, including **Task1 (Bug detection evaluation)** and **Task2 (Code coverage evaluation)**. Task 1 is the evaluation experiment for finding real bugs in SMT solvers. Task 2 is the evaluation experiment of code coverage achieved by different tools. We don’t include other experimental evaluations here since they need several days.


###  **Task 1: Bug detection evaluation**

You can use $\mathrm{HistFuzz}$ to detect real bugs in SMT solvers. For example, this is a basic command for $\mathrm{HistFuzz}$ you can adopt in the docker container.

`/home/histfuzz/bin/histfuzz --solver1=z3 --solver2=cvc5 --solverbin1=/home/z3/build/z3 --solverbin2=/home/cvc5/build/bin/cvc5`

If you want to stress-test more important options of solvers, you can add `--option` flag to the command:

`/home/histfuzz/bin/histfuzz --solver1=z3 --solver2=cvc5 --solverbin1=/home/z3/build/z3 --solverbin2=/home/cvc5/build/bin/cvc5 --option=regular`

Moreover, to run `n` parallel instances of $\mathrm{HistFuzz}$ on `n` cores, use the `--cores` flag. For example:

`/home/histfuzz/bin/histfuzz --solver1=z3 --solver2=cvc5 --solverbin1=/home/z3/build/z3 --solverbin2=/home/cvc5/build/bin/cvc5 --option=regular --cores=20`

Every time the tool detects a bug, you can manually stop the running process and inspect it in the `/home/histfuzz/temp` directory. These bugs can encompass soundness bugs, invalid model bugs, and crashes. The evaluation results prove that $\mathrm{HistFuzz}$ is capable of identifying genuine bugs in solvers.

#### Evaluation C-1 for RQ2

We provide resource files to replicate C-1. You can use the `--c1` flag to exclude bug reports resolved before the release of specific old versions, consistent with C-1. To run the evaluation, use the following command:

`/home/histfuzz/bin/histfuzz --solver1=z3 --solver2=cvc5 --solverbin1=/home/z3/build/z3 --solverbin2=/home/cvc5/build/bin/cvc5 --option=default --c1`



###  **Task 2: Code coverage evaluation**

In this evaluation, you can compare the code coverage achieved by $\mathrm{HistFuzz}$ to the baselines (i.e., storm, yinyang, opfuzz, and typefuzz). 

We implement a Python script and you can run it to reproduce the results of this evaluation. For example, in the docker container, you can use `python3 /home/histfuzz/reproduce/script.py`, and the results will be stored in `/home/histfuzz/reproduce/results` directory.

If you do not use the docker container, You should unzip and install the baselines in `/home/histfuzz/baselines` directory.

The results of this evaluation will show that $\mathrm{HistFuzz}$ can achieve significantly higher code coverage for the solvers than the baselines.


### **Additional Experience**

$\mathrm{HistFuzz}$ can automate the collection of the bug-triggering formulas in solvers' issue trackers. If you want to experience the feature, you can use the command `/home/histfuzz/bin/histfuzz --update --token=<GitHub Token>`.

GitHub personal access token can be generated in [GitHub token](https://github.com/settings/tokens). The collected formulas will be stored in `/home/histfuzz/bug_triggering_formulas` by default.
