#!/bin/sh

# Skrypt zaadaptowany z https://github.com/wkolowski/Typonomikon

coq_makefile -R "." DniOtwarte -arg "-async-proofs-cache force" -o makefile $(find . -name "*v")
make
rm makefile makefile.conf .makefile.d

coqdoc src/*v                                             \
       -d docs                                            \
       --html                                             \
       --with-footer assets/footer.html                   \
       --no-lib-name                                      \
       --lib-subtitles                                    \
       --parse-comments                                   \
       --no-index

cp assets/coqdoc.css docs/
mv docs/Coq.html docs/index.html
