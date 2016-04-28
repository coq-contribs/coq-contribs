# cloning all coq-contribs
## anonymously

```bash
git clone https://github.com/coq-contribs/coq-contribs.git
cd coq-contribs
git submodule update --init --recursive
```

## non-anonymously

```bash
clone https://$GITHUB_USERNAME:$GITHUB_PASSWORD@github.com/coq-contribs/coq-contribs.git
cd coq-contribs
cat .gitmodules | sed 's|https://github.com/coq-contribs|https://$GITHUB_USERNAME:$GITHUB_PASSWORD@github.com/coq-contribs|' > /tmp/out
mv /tmp/out .gitmodules 
git submodule sync
git submodule update --init --recursive
git co .gitmodules
```

# building all coq-contribs

```bash
# One can designate which Coq binaries to use:
export COQBIN=~/git/coq/bin/

# Drop all (currently) broken coq-contribs
coq_contribs=$(git submodule foreach --quiet 'pwd' |
               grep -v '/legacy-field$' |
               grep -v '/lemma-overloading$' |
               grep -v '/mmultisets$'|
               grep -v '/intuitionistic-nuprl')

# ... and build the rest of them
for coq_contrib in $coq_contribs; do
        cd $coq_contrib
        git submodule foreach --recursive git clean -dfx
        git clean -dfx
        for s in $(git submodule foreach --recursive --quiet pwd | tac); do
                cd $s
                make || exit 1
        done
        make || (echo; echo -n "${b}Error$n: build failed in: "; pwd; exit 1)
done
```
