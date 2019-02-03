## EmeraldC
EmeraldC is a compiler for the imperative langauge Emerald. EmeraldC compiles Emerald into byte code language EmeraldByte which can be run with `EmeraltdVM - https://github.com/navyhockey56/emeraldvm/blob/master/README.md`

### Build Requirements
- OCaml (built with 4.06)
- OCamlbuild
- OCamlfind
- Ocamllex

### Test Requirements
- Ruby
- EmeraldVM

### Building the project
To build the project, execute:
```
./Makefile
```
Note: You must have OCaml, Ocamlbuild, Ocamlfind, and Ocamllex installed. If you are missing these requirements, it is reccomended to use `opam - https://opam.ocaml.org/doc/Install.html` to install them.

### Compiling an Emerald program
Compiling an Emerald file is as simple as:
```
./emerald file_to_compile.em
```
Compiling will create a `.evm` with the same name as the Emerald program and place it in your current directory. You can then run the byte code using `EmeraldVM`

### Running the EmeraldVM tests
The ruby test script requires your project structure to be:
```
main.byte
tests/run_tests.rb
tests/inputs/
tests/outputs/
```
The test script will run any file contained within the `tests/inputs/` directory following the naming convention:
- File name starts with `test_`
- File has extension `.em`

The test results for each test script must be contained within the `tests/outputs/`, and must follow the naming convention:
- File name is the same as the test script, except for the extension
- File has extension `.out`

To run the test script, navigate to the `tests/` directory and execute:
```
ruby run_tests.rb
```