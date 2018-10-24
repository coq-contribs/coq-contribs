## Building tar files from contributions

TODO (if ever necessary)

## Building opam packages from contributions

1. Compile description extractor
   (from COQCONTRIBSMETA directory)

   make

2. Produce opam packages for some Coq version major.median.minor (from
   coq-contribs directory), assuming that the archive files have been
   made:

   COQCONTRIBSMETA/make-opam-packages opam-coq-archive-dir major median minor

   (example: "COQCONTRIBSMETA/make-opam-packages ~/opam-coq-archive 8 7 1")

3. Push the files created in opam-coq-archive-root upstream
