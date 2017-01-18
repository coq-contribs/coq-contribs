# How to clone coq-contribs anonymously?

```bash
git clone https://github.com/coq-contribs/coq-contribs.git
cd coq-contribs
git submodule update --init --recursive
```

# How to clone coq-contribs non-anonymously?

```bash
clone https://$GITHUB_USERNAME:$GITHUB_PASSWORD@github.com/coq-contribs/coq-contribs.git
cd coq-contribs
git submodule update --init --recursive
git submodule foreach 'git remote remove origin; git remote add origin https://$GITHUB_USERNAME:$GITHUB_PASSWORD@github.com/coq-contribs/$name.git'
```

Another way (based on ssh access)

```bash
git clone git@github.com:coq-contribs/coq-contribs.git
cd coq-contribs
git submodule update --init --recursive
git submodule foreach 'git remote set-url origin git@github.com:coq-contribs/$name.git'

```

Btw, note that the git configuration of contrib xyz is in .git/modules/xyz/config 

# In the contribs, how do I switch from "detached HEAD" to a given branch  ?

For instance for master, we first ensure that a local master branch exists, switch to it,
and update it w.r.t. origin/master.

```bash
git submodule foreach 'git branch master origin/master || true'
git submodule foreach 'git checkout master'
git submodule foreach 'git pull'
```

# How to compile a given coq-contrib?

Assuming that all dependencies of a given coq-contrib were already compiled and installed:
```bash
cd $COQ_CONTRIB_YOU_WANT_TO_COMPILE
make
```

# How to install a given coq-contrib?

```bash
make install
```

# How can I update a given coq-contrib?

If you want to update some particular coq-contrib, there are always two steps.
 1. The first (obvious) step is to update the repository corresponding to the coq-contrib (e.g. [aac-tactics](https://github.com/coq-contribs/aac-tactics/tree/master), [abp](https://github.com/coq-contribs/abp/tree/master), [additions](https://github.com/coq-contribs/additions/tree/master), ...).
 2. The second (non-obvious) step is to update the [coq-contribs](https://github.com/coq-contribs/coq-contribs/tree/master) repository itself.

If you do not perform the second step, people who clone the [coq-contribs](https://github.com/coq-contribs/coq-contribs/tree/master) repository will not see your new commits by default.

# What are the common properties of all coq-contribs?

Each coq-contrib:
 - is registered as a submodule of the [coq-contribs](https://github.com/coq-contribs/coq-contribs/tree/master) GIT repository.
 - has the following branches:
   - `master`: this branch of a coq-contrib must be compilable with the current Coq trunk (tracked [here](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs-trunk))
   - `v8.5`: this branch of a coq-contrib must be compilable with Coq 8.5 (tracked [here](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs-v8.5/))
   - `v8.6`: this branch of a coq-contrib must be compilable with Coq 8.5 (tracked [here](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs-v8.6/))
 - merging any of the branches to `master` shouldn't lead to any conflicts
 - has the following tags:
   - `8.5.0`: this version is known to work with Coq 8.5.0
   - `8.5.1`: this version is known to work with Coq 8.5.1
   - `v8.6.0` : this version is known to work with Coq 8.6
 - has a corresponding OPAM package that can be installed with:
   - `coq.dev` (tracked [here](https://ci.inria.fr/coq/view/opam/job/opam-install-trunk/))
   - `coq.8.5.dev` (tracked [here](https://ci.inria.fr/coq/view/opam/job/opam-install-v8.5/))
   - `coq.8.6.dev` (tracked [here](https://ci.inria.fr/coq/view/opam/job/opam-install-v8.6/))
   
   The names of the OPAM packages corresponding to individual coq-contribs is `coq-$COQ_CONTRIB_NAME`.
 - can depend only on:
   - on Coq (`v8.5` or `trunk`)
   - other coq-contribs
 - must contain `description` file.
 - has a toplevel `Makefile`
 - can be build by typing `make`
 - can be installed by typing `make install`
 - has a `LICENCE` file

# How can I add my work to coq-contribs?

To add your work to coq-contribs:
 1. check if it has all the [above](#what-are-the-common-properties-of-all-coq-contribs) properties
 2. and then opan a new issue for this repository.
