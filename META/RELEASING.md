Possible procedure to check the compilation, produce tar.gz and produce opam packages

## Check compilation of packages for Coq 8.7.0 or another number

1. Prepare a 8.7 branch if not already done

   git submodule foreach checkout -b v8.7 master

2. Make the contribution compatible with Coq 8.7.0

   - git submodule foreach checkout v8.7
   - META/check-contribs 8.7.0

     - If this succeeds, this automatically put a local tag v8.7.0
     - This can be reapplied as many time as necessary
     - This can be applied to one contribs only by doing

       META/check-contribs 8.7.0 name

## Building tar files from contributions

This amounts to push the existing local tags upstream: this makes the
corresponding tag.gz available online.

   META/make-package-release 8.7.0
  
   To do it for one package: "META/make-package-release 8.7.0 name"

## Building opam packages from contributions

1. Compile description extractor
   (from META directory)

   make

2. Produce opam packages for some Coq version major.median.minor (from
   coq-contribs directory), assuming that the archive files have been
   made:

   META/make-opam-packages opam-coq-archive-dir major median minor

   (example: "META/make-opam-packages ~/opam-coq-archive 8.7.1")

3. Push the files created in opam-coq-archive-root upstream
