(** * Coq: jak udowodnić, że nasz program działa poprawnie *)

(** Cześć, nazywam się Wojciech Kołowski i witam cię na Dniach Otwartych
    Instytutu Informatyki UWr 2021. Wszystkie materiały z tego wydarzenia
    możesz znaleźć
    #<a class='link' href='https://ii.uni.wroc.pl/dla-studenta/drzwi-otwarte'>tutaj</a>#,
    ja natomiast opowiem ci dziś o języku programowania Coq. *)

(** * Coq a inne języki programowania *)

(** Coq (wymawiane "kok"; nazwa pochodzi od francuskiego słowa _coq_,
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
    strzałkę w dół (lub wciśnij alt + strzałkę w dół). Kiedy Coq jest w trakcie
    czytania definicji, jest ona podświetlona na pomarańczowo. Jeżeli Coq ją
    zaakceptuje, zostaje ona podświetlona na szaro. Jeżeli z definicją jest coś
    nie tak, to zostanie podświetlona na czerwono, a komunikat o błędzie pojawi
    się w oknie po prawej na dole.

    Powyższa definicja, jak widać, jest w porządku. Nie pytaj na razie, skąd
    słowo kluczowe [Inductive] - dowiemy się tego później. Zauważ też, że
    definicja kończy się kropką, podobnie jak wszystkie inne komendy w Coqu.
    Samą definicję można odczytać następująco: "bit jest typem, który może
    przyjmować tylko jedną z dwóch wartości: tak albo nie".

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
    zauważyć, że Coq automatycznie zamienia [->] na [→], [=>] na [→], [fun] na
    [λ], a [forall] na [∀]. Żeby nie komplikować ci życia, na niniejszej stronie
    wyłączyłem te konwersje.

    Sama definicja jest dość prosta. Definicje zaczynają się od słowa kluczowego
    [Definition] (definiować tak możemy nie tylko funkcje, ale też inne obiekty).
    Następnie podajemy nazwę definiowanej funkcji. Żeby uniknąć niepotrzebnych
    komplikacji przyjąłem konwencję, że wszystkie nasze nazwy będą w języku
    polskim. Następnie, po dwukropku, podajemy typ definiowanego obiektu (nie
    zawsze jest to konieczne, ale pisanie typów to dobry zwyczaj). Zapis [A -> B]
    oznacza typ funkcyjny, a zatem [bit -> bit] to typ funkcji, które biorą
    argument typu [bit] i zwracają wynik również typu [bit].

    Ciało definicji zaczyna się po znaku [:=]. Funkcje o typie [A -> B] mają
    postać [fun x : A => e], gdzie [e] jest wyrażeniem typu [B] mogącym używać
    argumentu [x]. Zapis ten można odczytać jako "weź argument typu A o nazwie
    x i zwróć jako wynik wyrażenie e". Nazwa argumentu nie ma znaczenia - w
    naszym przypadku zamiast [fun b : bit => match b ...] moglibyśmy równie
    dobrze napisać [fun c : bit => match c ...]

    Dalej, między słowami kluczowymi [match] i [end] wykonujemy _dopasowanie
    do wzorca_ na bicie [b]. Ponieważ typ [bit] zdefiniowaliśmy tak, że są
    tylko dwie możliwości ([tak] albo [nie]), to możemy teraz sprawdzić, którą
    z tych postaci przyjmuje [b], i w każdym z tych dwóch przypadków zwrócić
    odpowiedni wynik. Uwaga: nie możemy pominąć żadnego przypadku. Nie możemy
    też podać większej ilości przypadków, niż faktycznie jest możliwości. *)

(** * Równość *)

(** Czy nasza definicja negacji jest poprawna? Wydaje się że tak, ale pewności
    nie mamy - dobrze byłoby udowodnić jakieś twierdzenie, które nas w tym
    upewni. Zanim jednak to nastąpi, zobaczmy jak w ogóle działają w Coqu
    twierdzenia. Szczególnie zainteresowani będziemy dowodzeniem równości
    dwóch obiektów.

    Twierdzenia i dowody są jedną z najmocniejszych stron Coqa. Gdy zaczynamy
    dowód, w oknie po prawej pojawia się nasz cel, czyli to czego chcemy
    dowieść. W miarę jak wykonujemy kolejne kroki dowodu, stan okna po prawej
    zmienia się, żeby pokazać nam co musimy zrobić, co mamy do dyspozycji oraz
    co pozostało jeszcze do zrobienia. Każdy dowód możemy swobodnie przewijać
    w przód i w tył za pomocą strzałek na górze po prawej lub skrótów
    klawiszowych. Jeżeli nie rozumiesz jakiegoś dowodu, możesz powtarzać go,
    dopóki cię nie oświeci. *)

Goal tak = tak. (* Po słowie kluczowym "Goal" piszemy, co chcemy udowodnić. *)
Proof.          (* Dowód zaczynamy od słowa kluczowego "Proof". *)
  reflexivity.  (* Każda rzecz jest równa samej sobie i Coq o tym wie. *)
Qed.            (* Dowód kończymy słowem kluczowym "Qed" - od łac. "Quod erat demonstrandum" - "Co należało udowodnić" *)

(** Nasze twierdzenie jest trywialne: chcemy pokazać, że [tak] jest równe [tak].
    Dowód jest równie trywialny i sprowadza się do użycia taktyki [reflexivity].
    Po angielsku "reflexivity" znaczy "zwrotność", a "zwrotność" to w
    matematycznej mowie nazwa na fakt, że każda rzecz jest równa samej sobie -
    wiedział o tym już Arystoteles jakieś 2400 lat temu, więc nie dziwota, że
    Coq też o tym wie. Taktyka zaś to formalny, Coqowy odpowiednik nieformalnego
    sposobu rozumowania. Powiedzenie, że "każda rzecz jest równa samej sobie",
    to właśnie taki nieformalny sposób rozumowania, a taktyka [reflexivity]
    jest jego realizacją. *)

Goal tak = nie.     (* A może "tak" jest równe "nie"? Oby nie! *)
Proof.
  Fail reflexivity. (* "tak" to coś innego niż "nie" i Coq to wie - nie da się go zrobić w wała. *)
Abort.              (* Zakończenie dowodu za pomocą "Abort" oznacza, że się poddajemy. *) 

(** Nie każdy sposób rozumowania jest poprawny, a zatem nie każde użycie taktyki
    kończy się sukcesem. W powyższym przykładzie rozumowanie "tak to to samo co
    nie, bo każda rzecz jest równa samej sobie" jest niepoprawne, a zatem próba
    udowodnienia tego twierdzenia za pomocą taktyki [reflexivity] zawodzi i
    musimy się poddać. Uwaga: komenda [Fail] pozwala nam zakomunikować Coqowi,
    iż spodziewamy się, że przeczytanie tego co po niej następuje zakończy się
    błędem. *)

(** * Obliczenia *)

(** Obliczenia w Coqu są wykonywane w bardzo prosty sposób - wszystko sprowadza
    się do upraszczania wyrażeń. Uczyłeś się pewnie w szkole na matematyce, że
    0 + x = x i że jeżeli mamy jakieś skomplikowane wyrażenie, w którym występuje
    0 + x, to możemy to wyrażenie uprościć do postaci, w której zamiast 0 + x
    występuje samo x.

    Każdy program w Coqu jest po prostu wyrażeniem, a jego obliczanie polega na
    wykonywaniu różnych uproszczeń. Kolejność, w jakiej wykonywane są uproszczenia,
    nie ma wpływu na wynik - zawsze wychodzi ten sam - ale może mieć wpływ na
    liczbę uproszczeń, którą trzeba wykonać. Liczba ta jednak, niezależnie od
    kolejności, zawsze jest skończona i wobec tego prędzej czy później każdy
    program zostaje maksymalnie uproszczony. Ta maksymalnie uproszczona postać
    programu nazywana jest postacią normalną i jest ona wynikiem obliczeń. *)

Goal negacja nie = tak.
Proof.
  cbn.
  reflexivity.
Qed.

(** Taktyka [cbn] realizuje sposób rozumowania "policz wynik działania programu".
    Nazwa pochodzi od angielskiego "call by name" i oznacza pewną konkretną
    kolejność, w której wykonywane są trzy podstawowe rodzaje uproszczeń, które
    zobaczymy za chwilę. *)

Goal negacja tak = nie.
Proof.
  cbv delta.   (* Pierwszym krokiem obliczeń jest odwinięcie definicji. *)
  cbv beta.    (* Kolejnym krokiem jest podstawienie wartości [tak] za argument funkcji. *)
  cbv iota.    (* Ostatnim krokiem jest wykonanie dopasowania i zwrócenie odpowiedniej wartości. *)
  reflexivity.
Qed.

(** Żeby wykonać pojedyncze uproszczenie, zamiast obliczać wszystko od razu,
    używamy taktyki [cbv], po której piszemy nazwę uproszczenia (nazwy pochodzą
    od greckich liter i są mało oświecające). Skrót "cbv" pochodzi z angielskiego
    "call by value" i, podobnie jak "cbn", oznacza pewną konkretną kolejność
    wykonywania uproszczeń.

    Są trzy główne rodzaje uproszczeń:
    - odwinięcie definicji
    - podstawienie wartości za argument funkcji
    - wykonanie dopasowania do wzorca

    Odwinięcie definicji zamienia nazwę (w naszym przypadku [negacja]) na kod,
    który ją definiuje (w naszym przypadku [fun b : bit => match b with ... end]).
    Podstawienie działa tak: jeżeli w funkcji [fun x : A => ... x ...] podstawimy
    [y] za [x], to otrzymujemy w wyniku [... y ...]

    Wykonanie dopasowania polega na sprawdzeniu, który wzorzec pasuje i zwróceniu
    odpowiadającej wartości. Wzorce sprawdzane są od góry do dołu - jeżeli pierwszy
    nie pasuje, sprawdzany jest kolejny i tak aż do skutku. Gwarantuje to nam, że
    w każdej sytuacji dopasować się może co najwyżej jeden wzorzec. Ponieważ
    definicje muszą obsługiwać wszystkie przypadki, mamy także gwarancję, że któryś
    wzorzec w końcu się dopasuje. *)

(** * Niebanalne twierdzenie *)

(** No, wreszcie czas udowodnić coś o naszej negacji. Ale co? Cóż... gdyby tak
    zanegować jakiś bit dwa razy, to powinniśmy w wyniku otrzymać to samo, co
    mieliśmy na początku, czyż nie? *)

Goal forall b : bit,         (* Dla każdego bitu b... *)
  negacja (negacja b) = b.   (* negacja negacji b jest równa b *)
Proof.
  intro dowolne_b.           (* Weźmy dowolny bit *)
  destruct dowolne_b.        (* Analiza przypadków: bit może mieć jedną z dwóch postaci (tak/nie) *)
    cbn. reflexivity.        (* Trochę obliczeń i... udało się! *)
    reflexivity.             (* Nie musimy ręcznie prosić o policzenie - Coq sam wie, żeby to zrobić. *)
Qed.

(** Nasze twierdzenie ma stosować się do każdego bitu [b], a więc nie możemy o
    tym bicie niczego założyć. Żeby to wyrazić, piszemy [forall], czyli po
    polsku "dla każdego".

    Żeby udowodnić coś o każdym bicie [b], wystarczy udowodnić to dla
    dowolnego bitu. Właśnie ten sposób rozumowania realizuje taktyka
    [intro] (argument po [intro] to nazwa, którą chcemy nadać naszemu
    dowolnemu bitowi). Po przeczytaniu linijki [intro dowolne_b.] mamy
    spore zmiany w oknie po prawej - z naszego celu zniknęło [forall
    b : bit], zaś nad kreską pojawiła się linijka [dowolne_b : bit].
    To, co znajduje się nad kreską, to kontekst - widać tam wszystkie
    nasze założenia, hipotezy oraz wszelkie inne obiekty, którymi możemy
    się posługiwać w trakcie dowodu.

    Następnie rozumujemy przez analizę przypadków. Ponieważ zdefiniowaliśmy bit
    mówiąc (a raczej pisząc), że każdy bit to albo [tak] albo [nie], to
    rozpatrzenie tych dwóch przypadków z osobna wystarcza by powiedzieć coś o
    dowolnym bicie. Właśnie ten sposób rozumowania jest realizowany przez
    taktykę [destruct]. W wyniku użycia tej taktyki mamy teraz dwa podcele: w
    pierwszym z nich [dowolne_b] zostało zastąpione przez [tak], a w drugim
    przez [nie]. W pierwszym przypadku wystarczy wykonać nieco obliczeń
    i widać wtedy, że obie strony równości są takie same. Drugi przypadek jest
    analogiczny - co więcej, jeżeli użyjemy tylko taktyki [reflexivity], to
    Coq sam połapie się, że powinien wykonać odpowiednie obliczenia. Uwaga: dla
    czytelności, dowodzenie każdego z podcelów zaczynamy od dwóch spacji wcięcia
    w kodzie.

    Tym sposobem udało nam się udowodnić nasze twierdzenie, choć być może nie
    wzbudza ono w tobie jakiegoś wybitnego entuzjazmu. Wszakże w Pythonie czy
    innym C++, aby upewnić się, że tamtejsza negacja jest poprawna, wystarczy
    napisać dwa testy. Jeżeli oba przechodzą, można ogłosić sukces i nie trzeba
    niczego dowodzić. *)

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
    sądzi, że to, co napisaliśmy powyżej, jest elementem typu [lista] (odpowiedź
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
    [l' : lista], to początkowy bit [b] musi powędrować na koniec wynikowej
    listy - możemy wysłać go tam za pomocą funkcji [na_końcu] - zaś reszta
    listy (czyli [l']) musi zostać rekurencyjnie odwrócona za pomocą funkcji
    [odwróć]. *)

Theorem odwróć_na_końcu :
  forall (b : bit) (l : lista),
    odwróć (na_końcu b l) = na_początku b (odwróć l).
Proof.
  intro b.
  induction l as [| głowa_l ogon_l hipoteza_indukcyjna].
    cbn. reflexivity.
    cbn. rewrite hipoteza_indukcyjna. cbn. reflexivity.
Qed.

(** Czas w końcu udowodnić jakieś twierdzenie. Tym razem zaczynamy od słowa
    kluczowego [Theorem] - jest ono konieczne, jeżeli chcemy móc nazwać nasze
    twierdzenie. A chcemy - żeby móc się do niego później odnosić. Twierdzenie
    nazywamy [odwróć_na_końcu], bo chcemy się przekonać, co się stanie, gdy
    najpierw dostawimy bit [b] na końcu listy [l], a potem całość odwrócimy.
    Odpowiedź jest prosta: oczywiście bit [b] trafi na początek odwróconej
    listy [l].

    Zaczynamy od [intro b], czyli "weźmy dowolne b". Następnym krokiem jest
    [induction l ...], co możemy przeczytać jako "indukcja po l". Indukcja to
    taka analiza przypadków na sterydach - w niektórych przypadkach do naszej
    dyspozycji dostajemy dodatkowo hipotezę indukcyjną. Indukcja jest sposobem
    rozumowania niezbędnym, gdy w grę wchodzą funkcje rekurencyjne: ponieważ
    funkcja rekurencyjna wywołuje samą siebie na mniejszym argumencie, to żeby
    udowodnić coś na jej temat dla jakiegoś argumentu, najpierw trzeba udowodnić
    tę samą własność dla mniejszego argumentu. Widzimy więc, że potrzebne jest
    nam coś w stylu wywołania rekurencyjnego, tylko że chcemy użyć tego czegoś
    do dowodzenia, a nie do definiowania funkcji... i właśnie tym czymś jest
    hipoteza indukcyjna!

    Uwaga: klauzula [as [| głowa_l ogon_l hipoteza_indukcyjna]] pozwala nam
    nadać nazwy rzeczom powstałym z rozłożenia [l] na kawałki oraz hipotezie
    indukcyjnej. W programowaniu funkcyjnym tradycyjnie pierwszy element listy
    nazywa się głową, zaś resztę ogonem, i stąd biorą się nasze nazwy.

    Indukcja pozostawia nam do udowodnienia dwa przypadki. W pierwszym [l]
    jest  postaci [koniec], a dowód jest prosty - po obu stronach równania
    jest to samo. W drugim przypadku same obliczenia już nie wystarczą, ale
    z pomocą przychodzi nam hipoteza indukcyjna, która jest równaniem postaci
    [odwróć (na_końcu b ogon_l) = na_początku b (odwróć ogon_l)] - jest to
    niemal dokładnie ta właściwość, którą chcemy udowodnić, ale dotyczy ona
    ogona [l], a nie samej listy [l].

    Zauważmy, że nasz cel również jest równaniem, zaś po jego lewej stronie
    mamy [na_końcu głowa_l (odwróć (na_końcu b ogon_l))]. Ponieważ występuje
    tutaj wyrażenie [odwróć (na_końcu b ogon_l)], to możemy użyć naszej hipotezy
    indukcyjnej, żeby zastąpić je przez [na_początku b (odwróć ogon_l)]. Żeby
    to zrobić, używamy taktyki [rewrite hipoteza_indukcyjna], która realizuje
    rozumowania polegające na przepisywaniu równań. Na koniec wystarczy trochę
    policzyć i voilà - widać, że obie strony równania są takie same. *)

Theorem odwróć_odwróć :
  forall l : lista,
    odwróć (odwróć l) = l.
Proof.
  induction l as [| głowa_l ogon_l hipoteza_indukcyjna].
    cbn. reflexivity.
    cbn. rewrite odwróć_na_końcu. rewrite hipoteza_indukcyjna. reflexivity.
Qed.

(** Udowodnijmy jeszcze, że dwukrotne odwrócenie listy daje w wyniku tę samą
    listę, co na początku. Dowód, podobnie jak poprzednio, jest przez indukcję
    po [l]. W tym momencie nie powinno nas to już dziwić - ponieważ prawie
    wszystkie funkcje operujące na listach są rekurencyjne, a dowodzenie
    właściwości funkcji rekurencyjnych wymaga rozumowania indukcyjnego, to
    prawie wszystkie dowody dotyczące list będą szły przez indukcję (wyjaśnia
    to też, dlaczego definicje typów zaczynają się od słowa kluczowego
    [Inductive]). Zauważmy, że nie musimy dowodu zaczynać taktyką [intro l] -
    gdy używamy indukcji, Coq sam wie, że powinien najpierw wprowadzić listę
    [l] do kontekstu.

    Mamy do rozpatrzenia dwa przypadki. Gdy [l] jest postaci [koniec], wystarczy
    trochę policzyć by przekonać się, że faktycznie [odwróć (odwróć koniec) = koniec].
    W drugim przypadku po wykonaniu obliczeń musimy pokazać
    [odwróć (na_końcu głowa_l (odwróć ogon_l)) = na_początku głowa_l ogon_l].
    Zauważmy, że możemy skorzystać z udowodnionego uprzednio twierdzenia
    [odwróć_na_końcu], gdyż nasz celu zawiera wyrażenie postaci
    [odwróć (na_końcu ...)]. Ponieważ twierdzenie [odwróć_na_końcu] jest po
    prostu równaniem, możemy użyć go za pomocą taktyki [rewrite]. Gdy już to
    zrobimy, po lewej stronie w naszym celu ukazuje się wyrażenie
    [odwróć (odwróć ogon_l)], które możemy uprościć korzystając z hipotezy
    indukcyjnej. I to by było na tyle, bo po obu stronach równania widzimy
    dokładnie to samo.

    W ten oto sposób udało nam się w Coqu udowodnić właściwość funkcji [odwróć],
    której nie można zagwarantować żadną liczbą testów. Czy to znaczy, że nasza
    funkcja jest poprawna? Cóż, nie do końca... wszakże [odwróć] nie jest jedyną
    funkcją [f : lista -> lista], która spełnia twierdzenie [f (f l) = l]. Żeby
    upewnić się, że [odwróć] to faktycznie ta funkcja, o którą nam chodziło,
    trzeba by udowodnić jeszcze kilka twierdzeń! *)

(** * Dlaczego warto nauczyć się Coqa? *)

(** Uważam, że warto nauczyć się Coqa (byłoby głupio, gdybym uważał inaczej,
    prawda?). Powodów jest kilka.

    Po pierwsze, programowanie funkcyjne ekspanduje i jest go wszędzie coraz
    więcej. Języki funkcyjne używane są coraz powszechniej (zdaje się, że
    najszybciej z nich rośnie Scala). Języki mainstreamowe natomiast w coraz
    większym stopniu pożyczają z języków funkcyjnych nowe konstrukty językowe
    (jeszcze kilka lat temu w C++ czy C## nie było np. funkcji anonimowych),
    style i techniki programowania (przetwarzanie strumieni w Javie), abstrakcje,
    pomysły na biblioteki i API etc. Sprawa ma się tutaj w przybliżeniu dość
    prosto: jeżeli znasz Coqa, to bardzo szybko nauczysz się każdego innego
    języka funkcyjnego oraz w mig zrozumiesz wszelkie zapożyczenia z języków
    funkcyjnych, występujące w innych językach.

    Po drugie, nauczysz się poprawnie i efektywnie rozumować o programach (nie
    tylko tych napisanych w Coqu, ale także w innych językach funkcyjnych i, w
    mniejszym stopniu, także w pozostałych językach). Jest to niesamowicie cenna
    i bardzo praktyczna umiejętność. Rozumowania równaniowe pozwalają połapać
    się podczas refaktoryzowania kodu, czy nasze zmiany przypadkiem nie zmieniły
    znaczenia programu. Umiejętność wymyślania twierdzeń, które w ogóle należy
    udowodnić na temat danej funkcji, świetnie przekłada się później w pracy na
    umiejętność wymyślania dobrych testów. Rozumowania na temat równoważności
    typów przydają się przy projektowaniu interfejsów i API (oraz znowu podczas
    refaktoringu). *)

(** * Ćwiczenia *)

(** Jeżeli dobrnąłeś aż tutaj, to gratuluję - znaczy, że musisz być całkiem
    wytrwały, a na dodatek zainteresowany tematem. Żeby nabyta w trakcie
    czytania wiedza nie uleciała, a entuzjazm nie opadł, proponuję żebyś
    wykonał parę łatwiutkich ćwiczeń.

    Oczywiście jak nie chcesz, to nie musisz robić ćwiczeń - nikt cię nie
    zmusza. To tylko taka dobra rada... *)

(* W tym okienku możesz wpisać swoje rozwiązania zadań. Może się ono wydawać
   małe, ale jak coś wpiszesz, to się powiększy :) *)

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
    #<a class='link' href='https://jscoq.github.io/scratchpad.html'>jsCoq</a>#.
    Polecam - nie trzeba nic instalować i ma rozsądne podpowiadanie składni dla
    początkujących.

    Jeżeli chcesz zacząć dłuższą przygodę z Coqiem, polecam go
    #<a class='link' href='https://coq.inria.fr/download'>zainstalować</a># - śmiga
    wtedy lepiej niż w przeglądarce. Musisz też wybrać sobie jakieś IDE:
    - #<a class='link' href='https://coq.inria.fr/download'>CoqIDE</a># -
      standardowe IDE do Coqa, polecam.
    - #<a class='link' href='https://code.visualstudio.com/'>Visual Studio Code</a>#
      z pluginem dla Coqa - również całkiem spoko.
    - #<a class='link' href='https://www.gnu.org/software/emacs/'>Emacs</a>#
      z pluginem #<a class='link' href='https://proofgeneral.github.io/'>Proof General</a># -
      zdecydowanie nie polecam.
    - W ostateczności można też używać Coqa z poziomu konsoli, ale tym bardziej
      nie polecam. *)

(** ** Materiały dydaktyczne *)

(** Przyda ci się też trochę materiałów dydaktycznych:
    - #<a class='link' href='https://www.youtube.com/watch?v=njgUPWlWYUM&t=6936s'>
      Nagranie z zeszłorocznych dni otwartych</a># (po polsku, ok. 20 min)
    - #<a class='link' href='https://www.youtube.com/watch?v=5e7UdWzITyQ'>
      Nagranie z prezentacji podobnej do naszej</a># (po angielsku, 3 godziny)
    - #<a class='link' href='https://softwarefoundations.cis.upenn.edu/lf-current/toc.html'>
      Książka Software Foundations</a>#, pierwsza połowa pierwszego tomu (po angielsku).
      Jest też #<a class='link' href='https://jscoq.github.io/ext/sf/lf/full/toc.html'>
      wersja śmigająca w jsCoqu</a>#.

    Jeżeli słuchanie/czytanie po angielsku sprawia ci problem, możesz też
    przeczytać pierwsze rozdziały
    #<a class='link' href='https://wkolowski.github.io/CoqBookPL/'>
    mojej własnej twórczości</a> (uwaga: materiał dość niekompletny i trochę
    nie po kolei; nie jest też tak odpicowany, jak niniejsza notatka). *)

(** ** Przydatne linki *)

(** Poniższe linki stanowią dobre punkty wyjścia do rozpoczęcia eksploracji
    Coqowego świata:
    - #<a class='link' href='https://coq.inria.fr'>Strona domowa</a>#
    - #<a class='link' href='https://github.com/coq/coq'>GitHub</a>#
    - #<a class='link' href='https://coq.discourse.group'>Forum</a>#
    - #<a class='link' href='https://coq.zulipchat.com'>Czat</a>#
    - #<a class='link' href='https://stackoverflow.com/questions/tagged/coq'>Q&A</a>#
    - #<a class='link' href='https://proofassistants.stackexchange.com/'>Lepsze Q&A</a>#
    - #<a class='link' href='https://coq.pl-a.net/'>Więcej linków</a>#
    - #<a class='link' href='https://github.com/coq-community/awesome-coq'>Jeszcze więcej linków</a>#

    Na stronie domowej znajdziesz więcej linków i materiałów dydaktycznych. Na
    GitHubie możesz podejrzeć, co Coqowi siedzi we flakach. Forum i tag "coq"
    na StackOverflow służą głównie do zadawania pytań. Ostatnio powstał też
    strona na StackExchange poświęcona Coqowi i językom my podobnym. Nie wiem
    co dzieje się na czacie, ale pewnie też pytania, tylko że szybciej odpowiadają :) *)

(** ** Kontakt *)

(**  Jeżeli masz pytania, pisz śmiało:
    - Ja: 299899@uwr.edu.pl
    - Nie ja: tomasz.drab@cs.uni.wroc.pl *)