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
- Compatible Rocq/Coq versions: 8.14 or later
- Additional dependencies:
  - [Parsec](https://github.com/liyishuai/coq-parsec)
  - [Menhir](http://gallium.inria.fr/~fpottier/menhir/)
  - [MenhirLib](https://gitlab.inria.fr/fpottier/menhir/-/tree/master/coq-menhirlib/)
  - [Dune](https://dune.build) 3.6 or later
- Rocq/Coq namespace: `JSON`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Coq JSON
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-json
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/liyishuai/coq-json.git
cd coq-json
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
dune build
dune install
```



