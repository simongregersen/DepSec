# DepSec: Static Information-Flow Control in Idris

This repository contains DepSec, a dependently typed library for
static information-flow control in Idris.

This repository is the accompanying code for the POST 2019 paper **A
Dependently Typed Library for Static Information-Flow Control in
Idris** by [Simon Gregersen](http://cs.au.dk/~gregersen), [Søren Eller
Thomsen](http://cs.au.dk/~sethomsen), and [Aslan
Askarov](http://askarov.net).

## Prerequisites

DepSec has been built and tested using

* [Idris](https://www.idris-lang.org) 1.3.1.

## Installation

Copy this package and run

```bash
$ idris --install depsec.ipkg
```

To use it in your program, run Idris with

```bash
$ idris -p depsec yourprogram.idr
```

## Directory Structure

* `DepSec` - core library, together with declassification primitives
* `Examples` - case studies and examples from the paper
