# TestML

TestML is a tool for detecting logcial errors in functional programming assingments.
It generates a counter-example if it given a program with bug.
The tool is licensed under the [MIT license](LICENSE.txt).

## Basic Settings

Since the tool is implemented in OCaml, you have to install OCaml and packages:

```bash
sudo apt-get install ocaml
sudo apt-get install ocamlbuild
sudo apt-get install opam
```

The tool uses the libraries, ``str``, ``batteries``, and Z3 SMT solver.
You can install the libraries using opam with follwing commands:

```bash
opam install str
opam install batteries
```

You can install and use Z3 OCaml binding at Z3 github repository (https://github.com/Z3Prover/z3)

## Contents

engine stores implemantation of TestML. More specifically, you can see that the main parts of TestML are implemented in the following files:

- engine/TestML/testGenerator.ml: Overall algirthm and symbolic test case generation 
- engine/TestML/sym_exec.ml: Symbolic verification


benchmarks stores 4,060 students submission we used in evaluation. All sub directories of ``benchmarks`` contains submissions that are correct or incorrect, a solution, set of test cases, and a grading function to test (if it required).

## Build

After installing the prerequisites, run the build script:

```bash
cd engine
eval `opam config env`
./build
```

If the compilation is done, you can check that the ``main.native`` is created.

## How to Run

To use the TestML, you need to input:

 - Student's program that has logical error
 - The function name of the problem
 - Correct implemetation

Then, TestML will detect a counter-example which triggers the error in student's program.
The template for running the TestML as follows:

```bash
engine/main.native -submission [submissions path] -entry [function name] -solution [solution path]
```

For example, we can generate counter-example of a submission of problem filter with following command:

```bash
engine/main.native -submission benchmarks/filter/filter/submissions/sub10.ml -entry filter -solution benchmarks/filter/filter/sol.ml
`````

If TestML finds a counter-example, it reutrns the result.

By using ``-run`` option you can run each program with predefined test cases. 
The template for running a test case as follows:

```bash
engine/main.native -submission [submissions path] -entry [function name] -testcases [testcase path]
```

For example, you can run a submission of problem filter with following command:

```bash
engine/main.native -run -submission benchmarks/filter/filter/submissions/sub1.ml -entry filter -testcases benchmarks/filter/filter/testcases
```

The correct implementation and student's program must be written in OCaml.
Especially, the format of testcases is restricted.
The format is ```{[input_11];[input_12];...;[input_1n]=>[output1];[input_21];[input_22];...;[input2n]=>[output2];...}```.
For instance, the testcases of proble filter is:
```
{
  (fun n-> n*(-1) <= 0);[-5;10;3] => [10;3];
  (fun n -> (n mod 2) = 0);[1;3;2;4] => [2;4];
  ...
}
```
