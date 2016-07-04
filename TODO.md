 - intuitionistic-nuprl is also being maintained [elsewhere](https://github.com/vrahli/NuprlInCoq). We should check it out; compare to our version and decide whether it make sense for us to maintain our version (separately).
 - add the proof of [Puiseaux theorem](https://scm.gforge.inria.fr/anonscm/git/puiseuxth/puiseuxth.git)
 - `intuitionistic-nuprl`
   - needs a proper `Makefile` and `Make`
   - OPAM packages for individual Coq versions (8.5.0, 8.5.1, ..., 8.5.dev, dev)
 - Clarify the purpose of coq-contribs.
   - It should be clear that if something is being actively worked on,
     it is not something anybody would want to include into coq-contribs.
     - Coq-contribs are diverse developments which are interesting but, sadly, no longer maintained by their original authors.
     - Coq-contribs is a place to preserve them to keep track of interesting things that were done in the past.
   - They also have less poetic purpose --- we can use them for testing/benchmarking current commits.
     E.g. today I see that commit e9c57a3 changed the behavior of coq_makefile in such a way that several
     coq-contribs no longer compile. Very possibly non-coq-contribs will not compile also
     and we see that something is not right.
 - Fix [`intuitionistic-nuprl` on `trunk`](https://ci.inria.fr/coq/job/bench-intuitionistic-nuprl/34/console).
 - Add the following new coq-contribs:
   - mmultisets
   - [mirror-core](https://github.com/coq-contribs/coq-contribs/issues/1)
   - [HoTT](https://github.com/coq-contribs/coq-contribs/issues/2)
 - [publish existing coq-contribs via OPAM](https://github.com/coq/opam-coq-archive/pull/72)
 - Go through existing coq-contribs:
   - identify those ones which have no licence
   - ask the author(s) whether this intentional or perhaps just an omission
 - There is an overlap between "description" and "opam" files. Can't we somehow refactor this information?
 - Remove the `branch = ...` lines from `.gitmodules`
 - The information in the `description` files should be properly structured and we should be able to mechanically "validate" it.
 - Go over categories declared by individual coq-contribs. Refactor and document them.
 - Go over tags declared by individual coq-contribs. Refactor and document them.
 - Go over licences declared by individual coq-contribs. Refactor licence names and provide links to the corresponding texts.
 - Convert `.svnignore` to `.gitignore`.
 - Add missing `.gitignore` files.
 - `compcert`: there seems to be an [upstream version](https://github.com/coq/opam-coq-archive/blob/master/released/packages/coq-compcert/coq-compcert.2.6.0/opam). If it is so, we should unlink [what we have](https://github.com/coq-contribs/compcert/tree/master) and instead fork the upstream version. Also, we shouldn't [try](https://github.com/matej-kosik/opam-coq-archive/tree/master/released/packages/coq-compcert/coq-compcert.8.5.0) to publish OPAM package in this case.
   - ask somebody in charge of CompCert about which is the correct "upstream" version
     and whether it would make sense to "reintegrate" it in a same way as we "reintegrated"
     the upstream "math-classes" and "corn"
 - `high-school-geometry`: there already seems to be an [OPAM package](https://github.com/matej-kosik/opam-coq-archive/tree/master/released/packages/coq-high-school-geometry/coq-high-school-geometry.1.0.0) for Coq 8.5. We shouldn't publish a [duplicate](https://github.com/matej-kosik/opam-coq-archive/tree/master/released/packages/coq-high-school-geometry/coq-high-school-geometry.8.5.0).
 - merge (?) our copy of `compcert` with the [upstream](https://github.com/AbsInt/CompCert) (?) version
 - add [lemma-overloading](https://github.com/coq-contribs/lemma-overloading) among the tracked coq-contribs. Problems:
   - it depends on `math-comp`
   - the `master` branch of `lemma-overloading` does not compile with Coq trunk.
 - merge [this](https://github.com/coq/opam-coq-archive/pull/72) pull-request to [opam-coq-archive](https://github.com/coq/opam-coq-archive)
 - web pages related to coq-contribs need to be updated (?), merged (?), migrated (?)
   - [here](http://www.lix.polytechnique.fr/coq/pylons/contribs/index)
   - and [here](http://coq.inria.fr/opam/www/archive.html)
 - Increase the consistency of names:
   - `*-theory` 
     - `graph-theory`
     - `set-theory`
     - `group-theory`
     - ... ?
   - `*-geometry`
     - `constructive-geometry`
     - `euclidean-geometry`
     - `high-school-geometry`
     - `projective-geometry`
     - `ruler-compass-geometry`
     - `tarski-geometry`
     - ... ?
   - `*-arithmetic`
     - e.g. we might want to rename `presburger` to `presburger-arithmetic`
   - `*-theorem`
     - ... ?
 - refactor coq-contribs
 - figure out why `-j32` does not work with `ergo`
 - For each coq-contrib check if there exists an upstream version.
   - `relation-algebra` ([www](http://perso.ens-lyon.fr/damien.pous/ra/), [git](https://github.com/damien-pous/relation-algebra))
 - we should write a "lint" script that will probably check the expected properties of coq-contribs as we have informally defined them [here](https://github.com/coq-contribs/coq-contribs/blob/master/FAQ.md#what-are-the-common-properties-of-all-coq-contribs)
 - Go over all OPAM packages. Those that are marked "proprietary" should not be released before we settle the licence issues.
 - Individual coq-contribs should have a nice, browsable and cross-referenced source-code presentation.
 - Convert `Make` files into `_CoqProject` files (proof-general and coqide both take it into consideration)
 - Change the names of repositories (and OPAM packages) that they correspond to directory name under which they are installed in the `user-contribs` directory.
 - All coq-contribs should have a `README.md` file.
 - Check why we currently see `warning: option -slash has no effect and is deprecated`
 - Check all warnings that are currently generated when compiling coq-contribs
   - Convert all warnings to errors.
 - Why we have `sum-of-two-square`? Why not `sum-of-two-squares`?
 - Jenkins
   - our Jenkins jobs should also test uninstallability of individual packages
     (we do not do this because there is some strange bug in OPAM which makes it behave in a wrong way with `--root` parameter in case we are uninstalling a package)
   - at the moment, URLs of the results of jobs have little clues about:
     - who started the job
     - which Coq branch was used
     It would make sense to include this kind of information into the job's name.
   - figure out how could we allow anyone to run Jenkins job without security risks
   - more descriptive names for the jobs we run should be generated at run-time (instead of numbers).
   - We already symbolically track dependencies of individual coq-contribs. We might reuse that information and instead of hardcoding the "dependencies" of individual coq-contribs in the following Jenkins jobs:
     - [coq-contribs](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs/)
     - [coq-contribs-trunk](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs-trunk/)
     - [coq-contribs-v8.5](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs-v8.5/)
   
     we might as well generate those jobs with from those dependencies.
   - Once we fix [this](https://coq.inria.fr/bugs/show_bug.cgi?id=4894), we will want to remove the corresponding workaround from the `/home/jenkins/bin/opam-install-package` file on pyrolyse node. Now, we use `-j1` instead of `-j32` for certain packages:
     - legacy-ring
     - legacy-field
     - string
     
     for which `-j32` would cause a spurious compilation error (due to [the bug](https://coq.inria.fr/bugs/show_bug.cgi?id=4894)).
 - Figure out what can we do with `lemma-overloading`. It now depends on `math-comp` which is not part of coq-contribs.
