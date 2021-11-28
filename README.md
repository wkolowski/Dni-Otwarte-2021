# Dni Otwarte II UWr 2021

To repozytorium zawiera kod źródłowy interaktywnej notatki do mojego wystąpienia na [Dniach Otwartych II UWr 2021](https://ii.uni.wroc.pl/dla-studenta/drzwi-otwarte). Możesz ją przeczytać tutaj: [Coq: jak udowodnić, że nasz program działa poprawnie](https://wkolowski.github.io/Dni-Otwarte-2021/).

Żeby zbudować projekt lokalnie, użyj poniższych komend (musisz mieć `coqc` i resztę Coqowych rzeczy):

```bash
git clone https://github.com/wkolowski/Dni-Otwarte-2021
cd Dni-Otwarte-2021
./build.sh
```

Żeby obejrzeć notatkę lokalnie, postaw serwer HTTP w folderze `docs/`, np. za pomocą komendy

```bash
npx localhost docs/ &
```

a następnie otwórz w przeglądarce <http://localhost:8080>
