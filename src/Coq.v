(** * Coq: jak udowodnić, że nasz program działa poprawnie *)

(** Cześć, nazywam się Wojciech Kołowski i witam cię na Dniach Otwartych
    Instytutu Informatyki UWr 2021. Wszystkie materiały z tego wydarzenia
    możesz znaleźć tutaj: https://ii.uni.wroc.pl/dla-studenta/drzwi-otwarte,
    ja natomiast opowiem ci dziś o języku programowania Coq. *)

(** * Coq a inne języki programowania *)

(** Coq (wymawiane "kok"; nazwa pochodzi od francuskiego słowa "coq",
    oznaczającego koguta) jest mocno wyjątkowym językiem programowania,
    różniącym się znacznie od większości popularnych języków, jak C++ czy
    Python.

    Coq jest przede wszystkim językiem funkcyjnym. Funkcje są podstawowym
    budulcem wszystkich programów i cieszą się niespotykaną w mainstreamowych
    językach elastycznością - mogą brać inne funkcje jako argumenty, zwracać
    funkcje jako wynik, i tak dalej. W Coqu (i w ogóle w językach funkcyjnych)
    większość rzeczy robimy inaczej, niż w innych językach programowania:
    - Zamiast zmiennych globalnych, dajemy funkcjom dodatkowe argumenty.
    - Zamiast iterować po strukturach danych zrobionych ze wskaźników,
      przemierzamy drzewa za pomocą funkcji rekurencyjnych (czyli takich,
      które wywołują same siebie).
    - Zamiast wielkich pętli przetwarzających dane, budujemy duże funkcje
      składając ze sobą wiele małych funkcji.
    - Różnic jest więcej, ale nie sposób wszystkich ich tutaj wymienić.

    Jednak jest coś jeszcze, co odróżnia Coqa nawet od pozostałych języków
    funkcyjnych. Mianowicie, Coq pozwala na formalną weryfikację poprawności
    napisanych w nim programów... ale co to właściwie znaczy? W zwykłych
    językach, jak Python czy C++, w zasadzie jedyną możliwością sprawdzenia,
    czy napisany przez nas program działa tak jak chcemy, są testy. Pojedynczy
    test uruchamia nasz program dla jakichś konkretnych danych wejściowych i
    sprawdza, czy wynik jest taki jak się spodziewamy. Jeżeli napiszemy dużo
    testów i wszystkie one kończą się pomyślnie, to uznajemy, że nasz program
    jest poprawny.

    Takie podejście jako tako sprawdza się w praktyce, ale nie daje pełnych i
    niepodważalnych gwarancji poprawności. Wszak, jak powiedział niegdyś klasyk
    informatyki, "testy mogą wykazać obecność błędów w programie, ale nie mogą
    wykazać ich nieobecności". Coq zaś wykazanie nieobecności błędów umożliwia:
    najpierw piszemy program, a potem dowodzimy twierdzenia, które mówi, że
    program działa tak jak powinien. Pisząc "twierdzenia" mam na myśli rzeczy
    analogiczne do tych znanych ci z lekcji matematyki, jak twierdzenie
    Pitagorasa, tylko że dotyczące programów, a pisząc "dowodzimy" mam na myśli
    czynność analogiczną do tej, którą wykonuje matematyk, aby upewnić się, że
    twierdzenie Pitagorasa jest prawdziwe. Wynik jest również analogiczny: tak
    jak twierdzenie Pitagorsa jest prawdziwe i nie ma co do tego najmniejszych
    wątpliwości ani nie da się go w żaden sposób podważyć, tak też twierdzenie
    o poprawności naszego programu, gdy je udowodnimy, gwarantuje nam, że w
    programie na pewno nie ma błędów.

    Morał tej bajki jest prosty: gdy programujemy w Coqu, możemy (i powinniśmy!)
    być jednocześnie matematykiem. *)

(** * Środowisko jsCoq *)

(** Środowisko, którego aktualnie używamy, nazywa się jsCoq. Jest fajne, bo
    pozwala używać Coqa bezpośrednio w przeglądarce i nie trzeba niczego
    instalować.

    Interakcja z Coqiem przebiega następująco. Po lewej mamy tekst poprzeplatany
    polami tekstowymi zawierającymi kod (można ten kod edytować - zachęcam do
    zabawy). Po prawej na dole jest okno, w którym Coq wyświetla nam informacje
    diagnostyczne, wiadomości o błędach i odpowiedzi na nasze zapytania. W oknie
    po prawej na górze póki co nie ma nic ciekawego - uaktywni się ono dopiero, gdy
    będziemy chcieli czegoś dowodzić.

    Po prawej na samej górze mamy kilka strzałek, którymi mówimy Coqowi,
    co ma robić (możemy też używać skrótów klawiszowych). Strzałka w dół
    (skrót: alt + strzałka w dół) - "wczytaj następny kawałek kodu",
    strzałka w górę (skrót: alt + strzałka w górę) - "cofnij się do
    poprzedniego kawałka kodu", podwójna strzałka (skrót: alt + enter) -
    "wczytaj cały kod aż do miejsca, w którym znajduje się kursor".

    Ok, tyle tytułem wstępu. Czas zobaczyć w końcu jakiś przykład! *)

(** * Proste typy i funkcje *)

(** Wiesz pewnie, co to bit. Otóż bit to takie coś co może być zerem lub
    jedynką. Spróbujmy zaimplementować w Coqu typ reprezentujący bity,
    napisać jakąś funkcję i coś o niej udowodnić. Uwaga: "0" i "1" nie są
    legalnymi nazwami w Coqu, więc nasze bity musimy nazwać jakoś inaczej.
    Przyjmijmy nazwy [tak] i [nie]. Uwaga 2: tekst pomiędzy znacznikami "( *"
    oraz "* )" to komentarze. Po każdej linijce kodu, która wprowadza jakąś
    nowość, będę umieszczał komentarze tłumaczące, co dana linijka oznacza. *)

Inductive        (* Definicja typu zaczyna się od słowa kluczowego "Inductive". *)
  bit : Type :=  (* "bit" jest typem zdefiniowanym w ten sposób, że: *)
    | tak : bit  (* "tak" jest elementem typu "bit" *)
    | nie : bit. (* "nie" jest elementem typu "bit" *)

(** Żeby Coq przeczytał powyższą definicję, kliknij na samej górze po prawej
    strzałkę w dół (lub wciśnij alt + strzałka w dół). Kiedy Coq jest w trakcie
    czytania definicji, jest ona podświetlona na pomarańczowo. Jeżeli Coq ją
    zaakceptuje, zostaje ona podświetlona na szaro. Jeżeli z definicją jest coś
    nie tak, to zostanie podświetlona na czerwono, a komunikat o błędzie pojawi
    się w oknie po prawej na dole.

    Powyższa definicja, jak widać, jest w porządku. Nie pytaj na razie, skąd
    słowo kluczowe [Inductive] - dowiemy się tego później. Zauważ też, że
    definicja kończy się kropką, podobnie jak wszystkie inne komendy w Coqu.
    Samą definicję można odczytać następująco: "bit jest typem, który może
    przjmować tylko jedną z dwóch wartości: tak albo nie".

    Co można zrobić z bitem? Zanegować! Tzn. zamienić "1" na "0", a "0" na "1"
    (co w naszym przypadku oznacza, że chcemy zamienić [tak] na [nie], a [nie]
    na [tak]). A zatem do dzieła. *)

Definition                  (* Definicja zaczyna się od słowa kluczowego "Definition". *)
  negacja : bit -> bit :=   (* negacja to funkcja, która bierze bit i zwraca bit, zdefiniowana następująco: *)
    fun b : bit =>          (* Weź jako argument bit nazwany [b]. *)
      match b with          (* Sprawdź, jakiej [b] jest postaci: *)
          | tak => nie      (* Gdy [b] to [tak], wynikiem funkcji jest [nie]. *)
          | nie => tak      (* Gdy [b] to [nie], wynikiem funkcji jest [tak]. *)
      end.

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

(** Czas więc, abyśmy ujrzeli jakiś bardziej skomplikowany przykład. Interesować
    będzie nas typ, który ma nieskończenie wiele elementów. Z pewnością w Pythonie
    czy C++ nie da się napisać nieskończenie wielu testów, prawda? W Coqu zaś
    można dowodzić właściwości programów operujących na takich typach bez żadnego
    problemu. Ponieważ w językach funkcyjnych najbardziej rozpowszechnioną
    strukturą danych są listy, to właśnie one będą naszym kolejnym przykładem -
    zdefiniujemy typ reprezentujący listy bitów, dwie proste funkcje operujące
    na listach, i udowodnimy, że są one poprawne. *)

Inductive lista : Type :=
    | koniec      : lista                  (* [koniec] jest listą *)
    | na_początku : bit -> lista -> lista. (* [na_początku b l] jest listą, pod warunkiem że [b] jest bitem a [l] listą *)

(** Najpierw trochę terminologii: to, co w definicji typu piszemy po pionowej
    kresce "|", to konstruktor. A zatem konstruktorami typu [bit] są [tak] i
    [nie], zaś konstruktorami typu [lista] są [koniec] i [na_początku].
    Konstruktory danego typu służą do konstruowania jego elementów, stąd nazwa.
    Uwaga: konstruktory w Coqu nie mają nic wspólnego z konstruktorami znanymi
    z języków takich jak C++ czy Python - zbieżność nazw jest przypadkowa.

    Powyższą definicję możemy przeczytać w następujący sposób: każda lista to
    albo [koniec], albo [na_początku b l], gdzie [b] jest bitem, a [l] listą.
    [koniec] reprezentuje listę pustą (czyli taką, w której nie ma żadnych
    bitów), zaś [na_początku b l] reprezentuje listę, która powstaje z dostawienia
    bitu [b] na samym początku jakiejś innej listy [l]. Elementy typu [lista]
    mają się do bardziej tradycyjnego zapisu list (używającego kwadratowych nawiasów)
    następująco:
    - Tradycyjnie: [[]] (lista pusta). Po naszemu: [koniec].
    - Tradycyjnie: [[tak]]. Po naszemu: [na_początku tak koniec].
    - Tradycyjnie [[nie; tak]]. Po naszemu: [na_początku nie (na początku tak koniec)].
    - I tak dalej... *)

Check na_początku tak (na_początku nie (na_początku tak koniec)).
(* ===> na_początku tak (na_początku nie (na_początku tak koniec)) : lista *)

(** Żebyś miał pewność, że nie robię cię w konia, możemy poprosić Coqa żeby
    sprawdził, jakiego typu jest dany obiekt. Służy do tego komenda [Check].
    W prawym dolnym rogu Coq wyświetla swoją odpowiedź: najpierw powtarza to co
    wpisaliśmy, a potem, po dwukropku, podaje nam typ obiektu. Jak widać, Coq
    sądzi, że to, co napisaliśmy powyżej, jest obiektem typu [lista] (odpowiedź
    Coqa pozwoliłem sobie skopiować i wkleić powyżej w komentarzu po znaczniku
    "===>"). Lista ta w tradycyjnym zapisie to [[tak; nie; tak]]. *)

Fixpoint na_końcu (b : bit) (l : lista) : lista :=
match l with
    | koniec           => na_początku b koniec
    | na_początku c l' => na_początku c (na_końcu b l')
end.

(** Skoro umiemy robić listy, dostawiając bit na początku, to dobrze byłoby
    też dowiedzieć się, jak dostawić bit na końcu listy. W tym celu definiujemy
    funkcję [na_końcu]. Ta funkcja będzie rekurencyjna, więc definicję musimy
    zacząć od słowa kluczowego [Fixpoint] (co znaczy słowo "fixpoint" i co ma
    wspólnego z rekurencją, nie pytaj...). [na_końcu] jest funkcją typu
    [bit -> lista -> lista], tzn. bierze jako argumenty bit oraz listę, a zwraca
    listę. Zapis jednak nieco różni się od tego, którego użyliśmy definiując
    funkcję [negacja]. Zapis [na_końcu (b : bit) (l : lista) : lista := ...]
    oznacza to samo, co
    [na_końcu : bit -> lista -> lista := fun (b : bit) (l : lista) : lista => ...],
    a jest dużo bardziej zwięzły, bo unikamy pisania typów dwa razy.

    Definicję zaczynamy od sprawdzenia, jakiej postaci jest lista [l]. Opcje
    są dwie, tak jak wynika z definicji typu [lista]. Gdy [l] to [koniec],
    wynikiem jest [na_początku b koniec] - skoro doszliśmy do końca listy, to
    dostawienie bitu na końcu jest dokładnie tym samym, co dostawienie go na
    początku. Gdy [l] to [na_początku c l'] dla jakiegoś [c : bit] oraz
    [l' : lista], wynikiem jest [na_początku c (na_końcu b l')] - ponieważ bit
    chcemy dostawić na końcu, to początek listy pozostaje bez zmian. Co jednak
    z resztą listy, czyli z [l']? Musimy na jej końcu dostawić bit [b], a zrobić
    to możemy za pomocą funkcji [na_końcu]...

    I to właśnie jest rekurencja - żeby zdefiniować funkcję [na_końcu], musimy
    użyć funkcji [na_końcu]. Innymi słowy: funkcja [na_końcu] wywołuje samą
    siebie. Mogłoby się wydawać, że coś takiego jest nielegalne ("kręcimy się w
    kółko"), ale nic bardziej mylnego: każde wywołanie rekurencyjne bierze jako
    argument coraz mniejszą listę. Ponieważ każda lista jest skończona (mimo, że
    wszystkich list razem jest nieskończenie wiele), to wywołania rekurencyjne
    prędzej czy później skonsumują całą listę i trafimy na [koniec], a wtedy
    działanie funkcji się zakończy. Definicje rekurencyjne są więc w Coqu
    dozwolone. Ba! Są naszym jedynym wyjściem - nie mamy do dyspozycji żadnych
    pętli ani niczego takiego. *)

Fixpoint odwróć (l : lista) : lista :=
match l with
    | koniec           => koniec
    | na_początku b l' => na_końcu b (odwróć l')
end.

(** Kolejną funkcją, którą chcemy zdefiniować, jest funkcja [odwróć], której
    zadaniem jest odwrócenie listy tak, żeby początek był na końcu, a koniec
    na początku. [odwróć] jest typu [lista -> lista], czyli bierze listę oraz
    zwraca listę. Podobnie jak [na_końcu] (i prawie wszystkie inne definicje
    funkcji operaujących na listach), definicja jest rekurencyjna. Najpierw
    sprawdzamy, jakiej postaci jest argument [l]. Gdy [l] to [koniec], wynikiem
    również jest [koniec] - gdy nie ma na liście żadnych bitów, nie ma czego
    odwracać. Jeżeli [l] jest postaci [na_początku b l'] dla [b : bit] oraz 
    [l : lista], to początkowy bit [b] musi powędrować na koniec wynikowej listy -
    możemy wysłać go tam za pomocą funkcji [na_końcu] - zaś reszta listy (czyli
    [l']) musi zostać rekurencyjnie odwrócona, za pomocą funkcji [odwróć]. *)

Theorem odwróć_na_końcu :
  forall (b : bit) (l : lista),
    odwróć (na_końcu b l) = na_początku b (odwróć l).
Proof.
  intro b.
  induction l as [| głowa_l ogon_l hipoteza_indukcyjna].
     cbv. reflexivity.
     cbn. rewrite hipoteza_indukcyjna. cbn. reflexivity.
Qed.

(** Czas w końcu udowodnić jakieś twierdzenie. Tym razem zaczynamy od słowa
    kluczowego [Theorem] - jest ono konieczne, jeżeli chcemy móc nazwać nasze
    twierdzenie. A chcemy - żeby móc się do niego później odnosić. Twierdzenie
    nazywamy [odwróć_na_końcu], bo chcemy się przekonać, co się stanie, gdy
    najpierw dostawimy bit [b] na końcu listy [l], a potem całość odwrócimy.
    Odpowiedź jest prosta: oczywiście bit [b] trafi na początek odwróconej
    listy [l].

    Zaczynamy od [intros b], czyli "weźmy dowolne b". Następnym krokiem jest
    [induction l ...], co możemy przeczytać jako "indukcja po l". Indukcja to
    taka analiza przypadków na sterydach - w niektórych przypadkach do naszej
    dyspozycji dostajemy dodatkowo hipotezę indukcyjną. Indukcja jest sposobem
    rozumowania niezbędnym, gdy w grę wchodzą funkcje rekurencyjne. Ponieważ
    funkcja rekurencyjna wywołuje samą siebie na mniejszym argumencie, to żeby
    udowodnić coś na jej temat dla jakiegoś argumentu, najpierw trzeba udowodnić
    tę samą własność dla mniejszego argumentu. Widzimy więc, że potrzebne jest
    nam coś w stylu wywołania rekurencyjnego, tylko że chcemy użyć tego czegoś
    do dowodzenia, a nie definiowania funkcji... i właśnie tym czymś jest
    hipoteza indukcyjna!

    Uwaga: klauzula [as [| głowa_l ogon_l hipoteza indukcyjna]] pozwala nam
    nadać nazwy rzeczom powstałym z rozłożenia [l] na kawałki oraz hipotezie
    indukcyjnej. W programowaniu funkcyjnym tradycyjnie pierwszy element listy
    nazywa się głową, zaś resztę ogonem, i stąd biorą się nasze nazwy.

    Indukcja pozostawia nam do udowodnienia dwa przypadki. W pierwszym [l] jest
    postaci [koniec], a dowód jest prosty - po obu stronach równania jest to
    samo. W drugim przypadku same obliczenia już nie wystarczą, ale z pomocą
    przychodzi nam hipoteza indukcyjna, która jest równanie postaci
    [odwróć (na_końcu b ogon_l) = na_początku b (odwróć ogon_l)] - jest to
    niemal dokładnie ta właściwość, którą chcemy udowodnić, ale dotyczy ona
    ogona [l], a nie samej listy [l].

    Zauważmy, że nasz cel również jest równaniem, zaś po jego lewej stronie
    mamy [na_końcu głowa_l (odwróć (na_końcu b ogon_l))]. Ponieważ występuje
    tutaj wyrażenie [odwróć (na_końcu b ogon_l)], to możemy użyć naszej hipotezy
    indukcyjnej, żeby zastąpić je przez [na_początku b (odwróć ogon_l)]. Żeby
    to zrobić, używamy taktyki [rewrite hipoteza_indukcyjna], które realizuje
    rozumowania polegający na przepisywaniu równań. Na koniec wystarczy trochę
    policzyć i voilà - widać, że obie strony równania są takie same. *)

Theorem odwróć_odwróć :
  forall l : lista,
    odwróć (odwróć l) = l.
Proof.
  induction l as [| głowa_l ogon_l hipoteza_indukcyjna].
    cbn. reflexivity.
    cbn. rewrite odwróć_na_końcu. rewrite hipoteza_indukcyjna.
      reflexivity.
Qed.

(** Udowodnijmy jeszcze, że dwukrotne odwrócenie listy daje w wyniku tę samą
    listę. Dowód, podobnie jak poprzednio, jest przez indukcję po [l]. W tym
    momencie nie powinno nas to już dziwić - ponieważ prawie wszystkie funkcje
    operujące na listach są rekurencyjne, a dowodzenie właściwości funkcji
    rekurencyjnych wymaga rozumowania indukcyjnego, to prawie wszystkie dowody
    dotyczące list będą szły przez indukcję. Zauważmy też, że nie musimy dowodu
    zaczynąć taktyką [intro l] - gdy używamy indukcji, Coq sam wie, że powinien
    najpierw wprowadzić listę [l] do kontekstu.

    Mamy dwa przypadki. Gdy [l] jest postaci [koniec], wystarczy trochę policzyć
    by przekonać się, że faktycznie [odwróć (odwróć koniec) = koniec]. W drugim
    przypadku po wykonaniu obliczeń musimy pokazać
    [odwróć (na_końcu głowa_l (odwróć ogon_l)) = na_początku głowa_l ogon_l].
    Zauważmy, że możemy skorzystać z udowodnionego uprzednio twierdzenia
    [odwróć_na_końcu], gdyż nasz celu zawiera wyrażenie postaci
    [odwróć (na_końcu ...)]. Ponieważ twierdzenie [odwróć_na_końcu] jest po
    prostu równaniem, możemy użyć go za pomocą taktyki [rewrite]. Gdy już to
    zrobimy, po lewej stronie w naszym celu ukazuje się wyrażenie
    [odwróć (odwróć ogon_l)], które możemy uprościć korzystając z hipotezy
    indukcyjnej. I to by było na tyle, bo po obu stronach równania widzimy
    dokładnie to samo. *)

(** * Dlaczego warto nauczyć się Coqa? *)

(** Języki funkcyjne ekspandują. *)

(** * Ćwiczenia *)

(** Jeżeli dobrnąłeś aż tutaj, to gratuluję - znaczy, że musisz być całkiem
    wytrwały, a na dodatek zainteresowany tematem. Żeby nabyta w trakcie
    czytania wiedza nie uleciała, a entuzjazm nie opadł, proponuję żebyś
    wykonał parę łatwiutkich ćwiczeń.

    Oczywiście jak nie chcesz, to nie musisz robić ćwiczeń - nikt cię nie
    zmusza. To tylko taka dobra rada... *)

(** **** Funkcja [lub] *)

(** Zdefiniuj funkcję [lub : bit -> bit -> bit], która zwraca [tak], gdy co
    najmniej jeden z jej argumentów jest równy [tak], zaś [nie] w przeciwnym
    wypadku.

    Zanim zabierzesz się za następne zadanie, spróbuj wymyślić i udowodnić
    jakieś twierdzenie, które upewni cię, że twoja definicja jest poprawna. *)

(** **** Właściwości funkcji [lub] - zadania zamknięte *)

(** Udowodnij podstawowe właściwości funkcji [lub]:
    - Idempotencja: [forall a : bit, lub a a = a]
    - Przemienność: [forall a b : bit, lub a b = lub b a]
    - Łączność: [forall a b c : bit, lub (lub a b) c = lub a (lub b c)] *)

(** **** Właściwości funkcji [lub] - zadania otwarte *)

(** Udowodnij poniższe twierdzenia, zamieniając uprzednio symbol [?] na jakieś
    konkretne wyrażenie:
    - [forall a : bit, lub tak a = ?]
    - [forall a : bit, lub nie a = ?]
    - [forall a : bit, lub a tak = ?]
    - [forall a : bit, lub a nie = ?]
    - [forall a : bit, lub a (negacja a) = ?]
    - [forall a b : bit, negacja (lub a b) = ?] *)

(** **** Funkcja [sklej] *)

(** Zdefiniuj funkcję [sklej : lista -> lista -> lista], które bierze dwie listy i
    skleja je ze sobą, np.

    [sklej (na_początku tak koniec) (na_początku nie koniec)
    =
    na_początku tak (na_początku nie koniec)]

    Innymi słowy: [sklej l1 l2] zwraca listę, której początkiem jest lista [l1],
    zaś końcem lista [l2].

    Zanim zabierzesz się za następne zadanie, spróbuj wymyślić i udowodnić
    jakieś twierdzenie, które upewni cię, że twoja definicja jest poprawna. *)

(** **** Właściwości funkcji [sklej] - zadania zamknięte *)

(** Udowodnij podstawowe właściwości funkcji [sklej]:
    - Łączność: [forall l1 l2 l3 : lista, sklej (sklej l1 l2) l3 = sklej l1 (sklej l2 l3)] *)

(** **** Właściwości funkcji [sklej] - zadania otwarte *)

(** Udowodnij poniższe twierdzenia, zamieniając uprzednio symbol [?] na jakieś
    konkretne wyrażenie:
    - [forall l : lista, sklej koniec l = ?]
    - [forall l : lista, sklej l koniec = ?]
    - [forall (b : bit) (l1 l2 : lista), na_końcu b (sklej l1 l2) = ?]
    - [forall l1 l2 : lista, odwróć (sklej l1 l2) = ?] *)

(** * Co dalej? *)

(** ** Środowisko *)

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
      bardziej nie polecam. *)

(** ** Materiały dydaktyczne *)

(** Przyda ci się też trochę materiałów dydaktycznych:
    - Nagranie z zeszłorocznych dni otwartych (po polsku, ok. 20 min):
      https://www.youtube.com/watch?v=njgUPWlWYUM&t=6936s
    - Nagranie z prezentacji podobnej do naszej (po angielsku, 3 godziny):
      https://www.youtube.com/watch?v=5e7UdWzITyQ
    - Książka Software Foundations, pierwsza połowa pierwszego tomu
      (po angielsku): https://softwarefoundations.cis.upenn.edu/lf-current/toc.html

    Jeżeli słuchanie/czytanie po angielsku sprawia wam problem, możecie też przeczytać
    pierwsze rozdziały mojej własnej twórczości: https://wkolowski.github.io/CoqBookPL/
    (uwaga, dość niekompletna i trochę nie po kolei). *)

(** ** Linki i kontakt *)

(** Przydatne linki:
    - Strona domowa: https://coq.inria.fr/
    - GitHub: https://github.com/coq/coq
    - Forum: https://coq.discourse.group/
    - Czat: https://coq.zulipchat.com/login/
    - Q&A: https://stackoverflow.com/questions/tagged/coq

    Jeżeli masz pytania, pisz śmiało:
    - Ja: 299899@uwr.edu.pl
    - Nie ja: tomasz.drab@cs.uni.wroc.pl *)