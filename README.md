# coq-contribs

This is a repository of contributions to Coq "donated" by their authors, and generally not having an upstream source. It is currently maintained by @herbelin.

It differs from [Coq community](http://github.com/coq-community) which is a repository of contributions managed by the community, though, eventually coq-contrib could be integrated to coq-community.

It differs from the Coq [opam](http://github.com/coq/opam-coq-repository) repository which is a repository of formal recipes to automatically install a Coq package using the [OPAM](http://github.com/opam) package manager.

Each submodule of this repository represents a single coq-contrib.

See also: [FAQ](FAQ.md), [TODO](TODO.md).

# History

The coq-contribs repository of Coq contributions started in the mid-90's and was at this time released as a full tarball of existing contributions.

These contributions were used both to highlight what users do in Coq and as regression tests for Coq.

A Coq contribution online publishing mechanism was installed by Jean-Marc Notin in 2008, together with a repository allowing to download a version of the contribution compatible with a given version of Coq.

The double role of Coq contributions as donation of a completed result to a formal library (e.g. the proof of Gödel's incompleteness theorem) and as a platform for regression tests was posing problems.

In 2015, opam was introduced as a general mechanism to install Coq packages. This included installation of Coq contributions but also registration of an installation recipe for arbitrary user contributions, without having to be explicitly registered to the Coq contributions repository.

From 2016, regression tests for Coq started to be based on large active user developments, allowing to dissociate the role of Coq contributions as a repository of "donated" developments and as a repository of live regression tests.

In 2018, coq-community was introduced as a start to develop a collaborative formal repository of libraries and results.
