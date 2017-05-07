# SpecCp: Speculative Constraint Processing for Multi-Agent Systems

SpecCp is an implementation of the speculative constraint processing
framework presented in the following paper:

> Hiroshi Hosobe, Ken Satoh, Jiefei Ma, Alessandra Russo, and Krysia
> Broda, "Speculative Constraint Processing for Hierarchical Agents,"
> in AI Communications, Vol. 23, No. 4, pp. 373-388, IOS Press, 2010.
> DOI: [10.3233/AIC-2010-0480](http://dx.doi.org/10.3233/AIC-2010-0480)

This repository contains the following files:

- README.md: this file
- COPYING: license
- Makefile: makefile
- SpecCp.ml: main program
- test.ml: test example
- test.log: output obtained by executing the test example

The program is written in [OCaml](http://ocaml.org/), and was tested
with OCaml version 3.11.0.

The main program together with the test example can be compiled by:

    make

To run the test example, execute the generated binary:

    ./speccp

When asked "Which step?", select one from the reducible processes or
the receivable answers that are printed just before the prompt.

## Author

[Hiroshi HOSOBE](http://www.hosobe.org/)

## License

GNU General Public License, version 2 (GPL v2)

Copyright (C) 2009-2017 Hiroshi HOSOBE

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; version 2 of the License.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>
