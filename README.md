<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Coq JSON

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/liyishuai/coq-json/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/liyishuai/coq-json/actions/workflows/docker-action.yml




From JSON to Coq, and vice versa.

## Meta

- Author(s):
  - Yishuai Li
- License: [BSD 3-Clause "New" or "Revised" License](LICENSE)
- Compatible Coq versions: 8.14 or later
- Additional dependencies:
  - [Parsec](https://github.com/liyishuai/coq-parsec)
  - [ExtLib](https://coq-community.org/coq-ext-lib)
  - [Menhir](http://gallium.inria.fr/~fpottier/menhir/)
  - [MenhirLib](https://gitlab.inria.fr/fpottier/menhir/-/tree/master/coq-menhirlib/)
- Coq namespace: `JSON`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Coq JSON
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-json
```

To instead build and install manually, do:

``` shell
git clone https://github.com/liyishuai/coq-json.git
cd coq-json
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



