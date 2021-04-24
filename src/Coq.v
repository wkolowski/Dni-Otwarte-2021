(** * Coq: jak udowodnić, że nasz program działa poprawnie *)

(** * Coq a inne języki programowania *)

(** Coq jest mocno wyjątkowym językiem programowania, różniącym się znacznie
    od większości popularnych języków, jak C++ czy Python.

    Po pierwsze, Coq jest językiem funkcyjnym. Zamiast zmiennych globalnych,
    dajemy funkcjom dodatkowe argumenty. Zamiast iterować po strukturach
    danych zrobionych ze wskaźników, przemierzamy drzewa za pomocą funkcji
    rekurencyjnych - czyli takich, które wywołują same siebie. Zamiast
    wielkich pętli przetwarzających dane, budujemy duże funkcje składając
    ze sobą wiele małych funkcji. Nasze funkcje mogą brać inne funkcje jako
    argumenty oraz zwracać funkcje jako wynik.

    Jednak jest coś jeszcze, co odróżnia Coqa nawet od prawie wszystkich
    innych języków funkcyjnych. Mianowicie, Coq pozwala na formalną
    weryfikację poprawności napisanych w nim programów - najpierw piszemy
    program, a potem dowodzimy twierdzenia mówiącego, że program działa tak
    jak powinien. Gdy programujemy w Coqu, możemy (i powinniśmy!) być
    jednocześnie matematykiem. *)

(** * Środowisko jsCoq *)

(** Środowisko, którego aktualnie używamy, nazywa się jsCoq. Jest fajne, bo
    pozwala używać Coqa bezpośrednio w przeglądarce i nie trzeba niczego
    instalować.

    Interakcja z Coqiem wygląda tak. Po lewej mamy tekst i okna z kodem
    (można edytować kod, który tam jest - zachęcam do zabawy). Po prawej na
    dole jest okno, w którym Coq wyświetla nam informacje diagnostyczne,
    wiadomości o błędzie i odpowiedzi na nasze zapytania. W oknie na górze
    po prawej póki co nie ma nic ciekawego - uaktywni się ono dopiero, gdy
    będziemy chcieli czegoś dowodzić.

    Po prawej na samej górze mamy kilka strzałek, którymi mówimy Coqowi,
    co ma robić (możemy też używać skrótów klawiszowych). Strzałka w dół
    (skrót: alt + strzałka w dół) - "wczytaj następny kawałek kodu",
    strzałka w górę (skrót: alt + strzałka w górę) - "cofnij się do
    poprzedniego kawałka kodu", podwójna strzałka (skrót: alt + enter) -
    "wczytaj cały kod aż do miejsca, w którym znajduje się kursor".

    Ok, czas zobaczyć w końcu trochę kodu. *)

(** * Proste typy i funkcje *)

(** Wiesz pewnie, co to bit. Otóż bit to takie coś co może być zerem lub
    jedynką. Spróbujmy zaimplementować w Coqu typ reprezentujący bity,
    napisać jakąś funkcję i coś o niej udowodnić. Uwaga: "0" i "1" nie są
    legalnymi nazwami w Coqu, więc nasze bity musimy nazwać jakoś inaczej.
    Przyjmijmy nazwy [tak] i [nie]. *)

Inductive          (* Definicja typu zaczynaja się od słowa kluczowego [Inductive]. *)
  bit : Type :=    (* [bit] jest typem zdefiniowanym w ten sposób, że... *)
    | tak : bit    (* [tak] jest elementem typu [bit] *)
    | nie : bit    (* [nie] jest elementem typu [bit] *)
    .              (* I nie ma żadnych innych elementów typu bit. *)

(** Żeby Coq przeczytać powyższą definicję, kliknij na smaej górze po prawej
    strzałkę w dół (lub wciśnij alt + strzałka w dół). Kiedy Coq jest w trakcie
    czytania definicji, jest ona podświetlona na pomarańczowo, zaś gdy Coq ją
    zaakceptuje, jest podświetlona na szaro. Jeżeli Coq akceptuje definicję, to
    milczy. Jeżeli coś mu nie pasuje, komunikat o błędzie pojawia się w oknie
    na dole po prawej. Powyższa definicja, jak widać, jest w porządku.
    
    Co można zrobić z bitem? Zanegować! Tzn. zamienić "1" na "0", a "0" na "1"
    (w naszym przypadku zamienić [tak] na [nie], a [nie] na [tak]. Do dzieła. *)

Definition                  (* Definicja zaczyna się od słowa kluczowego [Definition] *)
  negacja : bit -> bit :=   (* [negacja] to funkcja, która bierze bit i zwraca bit, zdefiniowana następująco: *)
    fun b : bit =>          (* Weź jako argument bit nazwany [b]. *)
      match b with          (* Sprawdźmy, jakiej [b] jest postaci. *)
          | tak => nie      (* Gdy [b] to [tak], wynikiem funkcji jest [nie]. *)
          | nie => tak      (* Gdy [b] to [nie], wynikiem funkcji jest [tak]. *)
      end.                  (* Koniec definicji. *)

(** Uwaga: jeżeli oglądałeś moje nagranie z Dni Otwartych, to możesz tam
    zauważyć, że Coq automatycznie zamienia strzałkę [->] na [→], [=>]
    na [→], [fun] na [λ], a [forall] na [∀]. Żeby nie komplikować ci życia,
    na niniejszej stronie wyłączyłem te konwersje. *)

(** * Równość *)

(** Czy nasza definicja negacji jest poprawna? Na razie nie wiadomo - musimy
    udowodnić jakieś twierdzenie, które nas w tym upewni. Zanim jednak to
    nastąpi, zobaczmy jak w ogóle działają w Coqu twierdzenia. Szczególnie
    zainteresowani będziemy dowodzeniem równości dwóch obiektów.
    
    Twierdzenia i dowody są jedną z najmocniejszych stron Coqa. Gdy zaczynamy
    dowód, w oknie po prawej pojawia się nasz cel, czyli to czego chcemy
    dowieść. W miarę jak wykonujemy kolejne kroki dowodu, stan okna po prawej
    zmienia się, żeby pokazać nam co musimy zrobić, co mamy do dyspozycji oraz
    co pozostało jeszcze do zrobienia. Każdy dowód możemy swobodnie przewijać
    w przód i w tył za pomocą strzałek na górze po prawej lub skrótów
    klawiszowych. Jeżeli nie rozumiesz jakiegoś dowodu, możesz powtarzać go,
    dopóki cię nie oświeci. *)

Goal tak = tak. (* Po słowie kluczowym [Goal] piszemy, co chcemy udowodnić. *)
Proof.          (* Dowód zaczynamy od słowa kluczowego [Proof]. *)
  reflexivity.  (* Każda rzecz jest równa samej sobie i Coq o tym wie. *)
Qed.            (* Dowód kończymy słowem [Qed] - od łac. "Quod erat demonstrandum" - "Co należało udowodnić" *)

(** [reflexivity] znaczy po angielsku "zwrotność", a "zwrotność" to w
    matematycznej mowie nazwa na fakt, że każda rzecz jest równa samej
    sobie - wiedział o tym już Arystoteles jakieś 2400 lat temu, więc
    i nie dziwota, że Coq o tym wie. *)

Goal tak = nie.     (* A może [tak] jest równe [nie]? Oby nie! *)
Proof.
  Fail reflexivity. (* [tak] to coś innego niż [nie] i Coq to wie - nie da się go zrobić w wała *)
Abort.              (* Zakończenie dowodu za pomocą [Abort] oznacza, że się poddajemy. *) 

(** [reflexivity] jest taktyką. Taktyka to formalny, Coqowy odpowiednik
    nieformalnego sposobu rozumowania. Powiedzenie, że "każda rzecz jest
    równa samej sobie", to właśnie taki nieformalny sposób rozumowania,
    a taktyka [reflexivity] jest jego realizacją. Nie każdy sposób
    rozumowania jest poprawny, a zatem nie każde użycie taktyki kończy
    się sukcesem. W powyższym przykładzie rozumowanie "tak to to samo
    co nie, bo każda rzecz jest równa samej sobie" jest niepoprawne, a
    zatem próba użycia taktyki [reflexivity] zawodzi i musimy się poddać. *)

(** * Obliczenia *)

(** Obliczenia w Coqu są wykonywane w bardzo prosty sposób - wszystko
    sprowadza się do upraszczania wyrażeń. Uczyłeś się pewnie w szkole
    na matematyce, że 0 + x = x i że jeżeli mamy jakieś skomplikowane
    wyrażenie, w którym występuje 0 + x, to możemy to wyrażenie uprościć
    do postaci, w której zamiast 0 + x występuje samo x.

    Każdy program w Coqu jest po prostu wyrażeniem, a jego obliczanie
    polega na wykonywaniu po kolei różnych uproszczeń. Są trzy główne
    rodzaje uproszczeń: odwinięcie definicji, podstawienie wartości za
    argument funkcji, i wykonanie dopasowania do wzorca. W praktyce
    wygląda to tak: *)

Goal negacja tak = nie.
Proof.
  cbv delta.   (* Pierwszym krokiem obliczeń jest odwinięcie definicji. *)
  cbv beta.    (* Kolejnym krokiem jest podstawienie wartości [tak] za argument funkcji. *)
  cbv iota.    (* Ostatnim krokiem jest wykonanie dopasowania i zwrócenie odpowiedniej wartości. *)
  reflexivity.
Qed.

Goal negacja nie = tak.
Proof.
  cbv. (* Oczywiście możemy policzyć wszystko za jednym zamachem. *)
  reflexivity.
Qed.

(** Taktyka [cbv] realizuje sposób rozumowania "uprość program
    maksymalnie jak tylko się da". Nazwa pochodzi od angielskiego
    "call by value" i oznacza pewną konkretną kolejność, w której
    wykonywane są trzy podstawowe rodzaje uproszczeń, które
    widzieliśmy powyżej. *)

(** * Niebanalne twierdzenie *)

(** No, wreszcie czas udowodnić coś o naszej negacji. Ale co? Cóż...
    gdyby tak zanegować jakiś bit dwa razy, to powinniśmy w wyniku
    otrzymać to samo, co mieliśmy na początku, czyż nie? *)

Goal forall b : bit,         (* Dla każdego bitu b... *)
  negacja (negacja b) = b.   (* negacja negacji b jest równa b *)
Proof.
  intro dowolne_b.           (* Weźmy dowolny bit *)
  destruct dowolne_b.        (* Analiza przypadków: bit może mieć jedną z dwóch postaci (tak/nie) *)
    cbv. reflexivity.        (* Trochę obliczeń i... udało się! *)
    reflexivity.             (* Nie musimy ręcznie prosić o policzenie - Coq sam wie, żeby to zrobić. *)
Qed.

(** Nasze twierdzenie ma stosować się do każdego bitu b, a więc nie
    możemy o tym bicie niczego założyć. Żeby to wyrazić, piszemy [forall],
    czyli po polsku "dla każdego".

    Żeby udowodnić coś o każdym bicie b, wystarczy udowodnić to dla
    dowolnego bitu. Właśnie ten sposób rozumowania realizuje taktyka
    [intros] (argument po [intros] to nazwa, którą chcemy nadać naszemu
    dowolnemu bitowi). Po przeczytaniu linijki [intro dowolne_b.] mamy
    spore zmiany w oknie po prawej - z naszego celu zniknęło [forall
    b : bit], zaś nad kreską pojawiła się linijka [dowolne_b : bit].
    To, co znajduje się nad kreską, to kontekst - widać tam wszystkie
    nasze założenia, hipotezy oraz wszelkie inne obiekty, którymi możemy
    się posługiwać w trakcie dowodu.

    Następnie rozumujemy przez analizę przypadków. Ponieważ zdefiniowaliśmy
    bit mówiąc (a raczej pisząc), że każdy bit to albo [tak] albo [nie], to
    rozpatrzenie tych dwóch przypadków z osobna wystarcza, by powiedzieć
    coś o dowolnym bicie. Właśnie ten sposób rozumowania jest realizowany
    przez taktykę [destruct]. W wyniku użycia tej taktyki mamy tearz dwa
    cele: w pierwszy z nich [dowolne_b] zostało zastąpione przez [tak], a w
    drugim przez [nie]. W pierwszym przypadku wystarczy wykonać nieco obliczeń
    i widać wtedy, że obie strony równości są takie same. Drugi przypadek jest
    analogiczny - co więcej, jeżeli użyjemy tylko taktyki [reflexivity], to
    Coq sam połapie się, że powinien wykonać odpowiednie obliczenia.

    Tym sposobem udało nam się udowodnić nasze twierdzenie, choć być może nie
    wzbudza ono w tobie jakiegoś wybitnego entuzjazmu. Wszakże w Pythonie czy
    innym C++, aby upewnić się, czy tamtejsza negacja jest poprawna, wystarczy
    napisać dwa testy. Jeżeli oba przechodzą, można ogłosić sukces. *)

(** * Bardziej skomplikowane typy, funkcje rekurencyjne i dowody przez indukcję *)

(** Czas więc, abyśmy ujrzeli jakiś bardziej skomplikowany przykład. Interesuje
    nas typ, który miałby nieskończenie wiele elementów. Z pewnością w Pythonie
    czy C++ nie da się napisać nieskończenie wielu testów, prawda? W Coqu zaś
    można dowodzić właściwości programów operujących na takich typach bez żadnego
    problemu. *)

Inductive lista : Type :=
    | koniec      : lista                  (* [koniec] jest listą *)
    | na_początku : bit -> lista -> lista. (* [na_początku b l] jest listą, pod warunkiem że [b] jest bitem a [l] listą *)

(* [[tak; nie; tak]] *)
Check na_początku tak (na_początku nie (na_początku tak koniec)).

Fixpoint na_końcu (b : bit) (l : lista) : lista :=       (* Definicje rekurencyjne zaczynają się od [Fixpoint]. *)
match l with
    | koniec           => na_początku b koniec
    | na_początku c l' => na_początku c (na_końcu b l')
end.

Fixpoint odwróć (l : lista) : lista :=
match l with
    | koniec           => koniec
    | na_początku b l' => na_końcu b (odwróć l')
end.

Theorem odwróć_na_końcu :
  forall (b : bit) (l : lista),
    odwróć (na_końcu b l) = na_początku b (odwróć l).
Proof.
  intro b. (* Weźmy dowolne b. *)
  induction l as [| głowa_l ogon_l hipoteza_indukcyjna].
     cbv. reflexivity.
     cbn. rewrite hipoteza_indukcyjna. cbn. reflexivity.
Qed.

Theorem odwróć_odwróć :
  forall l : lista,
    odwróć (odwróć l) = l.
Proof.
  induction l as [| głowa_l ogon_l hipoteza_indukcyjna].
    cbn. reflexivity.
    cbn. rewrite odwróć_na_końcu. rewrite hipoteza_indukcyjna.
      reflexivity.
Qed.

(** * Ćwiczenia *)

(** Zdefiniuj funkcję [lub : bit -> bit -> bit], która zwraca [tak], gdy co najmniej jeden
    z jej argumentów jest równy [tak], zaś [nie] w przeciwnym wypadku.

    Następnie udowodnij, że:
    - [forall a : bit, lub a a = a]
    - [forall a : bit, lub a (negacja a) = tak]
    - [forall a b : bit, lub a b = lub b a]
    - [forall a b c : bit, lub (lub a b) c = lub a (lub b c)]

    Co się stanie, gdy zanegujemy [lub], tzn. czemu jest równe [negacja (lub a b)]?

    Zdefiniuj funkcję [sklej : lista -> lista -> lista], które bierze dwie listy i
    skleja je ze sobą, np.

    [sklej (na_początku tak koniec) (na_początku nie koniec)
    =
    na_początku tak (na_początku nie koniec)]

    Następnie udowodnij następujące twierdzenia:
    - [forall l : lista, sklej koniec l = l]
    - [forall l : lista, sklej l koniec = l]
    - [forall l1 l2 l3 : lista, sklej (sklej l1 l2) l3 = sklej l1 (sklej l2 l3)]
    - [forall (b : bit) (l1 l2 : lista), na_końcu b (sklej l1 l2) = sklej l1 (na_końcu b l2)]
    - [forall l1 l2 : lista, odwróć (sklej l1 l2) = sklej (odwróć l2) (odwróć l1)] *)

(** * Dlaczego warto nauczyć się Coqa? *)

(** Języki funkcyjne ekspandują. *)

(** * Kim jesteśmy, dokąd zmierzamy? *)

(** Najłatwiej jest zapoznać się z Coqiem używając przeglądarkowego środowiska
    jsCoq (https://jscoq.github.io/scratchpad.html). Polecam - nie trzeba nic
    instalować i ma rozsądne podpowiadanie składni dla początkujących.

    Jeżeli chcecie zacząć dłuższą przygodę z Coqiem, polecam go zainstalować
    (https://coq.inria.fr/) - śmiga wtedy lepiej niż w przeglądarce. Musicie
    też wybrać sobie jakieś IDE:
    - CoqIDE (https://coq.inria.fr/) - standardowe IDE do Coqa, polecam.
    - Visual Studio Code (https://code.visualstudio.com/) z pluginem dla
      Coqa - również całkiem spoko.
    - Emacs (https://www.gnu.org/software/emacs/) z pluginem Proof General
      (https://proofgeneral.github.io/) - nie polecam.
    - W ostateczności można też używać Coqa z poziomu konsoli, ale tym
      bardziej nie polecam.

    Przyda się też troche materiałów dydaktycznych:
    - Nagranie z zeszłorocznych dni otwartych (po polsku, ok. 20 min):
      https://www.youtube.com/watch?v=njgUPWlWYUM&t=6936s
    - Nagranie z prezentacji podobnej do naszej (po angielsku, 3 godziny):
      https://www.youtube.com/watch?v=5e7UdWzITyQ
    - Książka Software Foundations, pierwsza połowa pierwszego tomu
      (po angielsku): https://softwarefoundations.cis.upenn.edu/lf-current/toc.html

    Jeżeli słuchanie/czytanie po angielsku sprawia wam problem, możecie też przeczytać
    pierwsze rozdziały mojej własnej twórczości: https://wkolowski.github.io/CoqBookPL/
    (uwaga, dość niekompletna i trochę nie po kolei).

    Przydatne linki:
    - Strona domowa: https://coq.inria.fr/
    - GitHub: https://github.com/coq/coq
    - Forum: https://coq.discourse.group/
    - Czat: https://coq.zulipchat.com/login/
    - Q&A: https://stackoverflow.com/questions/tagged/coq

    Jeżeli macie pytania, piszcie (asekuracyjnie podaje uczelniane maile):
    - Ja: 299899@uwr.edu.pl
    - Nie ja: tomasz.drab@cs.uni.wroc.pl *)