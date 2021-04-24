#!/bin/sh

# Zrób nowego makefile'a na wypadek, gdyby pojawiły się jakieś nowe pliki .v
coq_makefile -R "." DniOtwarte -o makefile $(find . -name "*v")

# Zbuduj cały kod.
make

# Zbuduj wersję HTML.
coqdoc src/*v --html -d docs                              \
       --with-footer assets/footer.html                   \
       --no-lib-name --lib-subtitles                      \
       --parse-comments                                   \
       --no-index                                         \
       --toc --toc-depth 3

# Przenazwij wynikowy plik HTML.
mv docs/Coq.html docs/index.html

# Dodaj właściwe style CSS.
cp assets/*css docs/

# Wywal co niepotrzebne.
rm makefile makefile.conf docs/toc.html
