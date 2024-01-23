# Python parser

This project is aimed at making a parser that translates C programs, which manipulate
the heap, into Z3-compatible instructions.

## Usage

See further information on the arguments required with:

```
usage: Parse a C file [-h] [--print-result] [--no-print-result] filename

positional arguments:
  filename           name of file to parse

options:
  -h, --help         show this help message and exit
  --print-result     prints the result of the instructions
  --no-print-result  does not print the result of the instruction

```

## Project structure

In the `examples/` folder are some code examples. The `externals/` folder contains the classes to enable the translation of the instructions

## Getting started

### Run in a Virtualenv

Install all the required libraries using the `requirements.txt` file by running in your environment.

```
pip3 install -r requirements.txt
```

### Run

You can run the project with two different options: one that prints the result of the instructions and one that does not print it.

#### Execution by printing the instructions

```
 python3 parser.py examples/test.c --print-result
```

#### Execution by not printing the instructions

```
 python3 parser.py examples/test.c --no-print-result
```
