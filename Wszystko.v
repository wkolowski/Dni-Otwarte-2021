(** * Scenariusz i kod *)

(**                                                                           |*)

(** Scenariusz:
    0. Powitanie.
    1. Nazwa.
    2. Środowisko jsCoq.
    3. Programowanie funkcyjne.
    4. Meritum.
    5. 
    
*)

(** * Coq a inne języki programowania *)

(** Coq jest mocno wyjątkowym językiem programowania, różniącym się znacznie
    od większości popularnych języków, jak C++ czy Python.
    
    Po pierwsze, Coq jest językiem funkcyjnym. Zamiast iteraować po strukturach
    danych, używamy zazwyczaj funkcji, które biorą inne funkcje jako argumenty.
    Zamiast
    
    Zamiast używać pętli, funkcje
    definiujemy zazwyczaj przez rekursję. Zamiast pętli zamiast przypisania i iteracji używamy rekursji i funkcji,
    które biorą inne funkcje jako argumenty. *)

(** * Proste typy *)

Inductive bit : Type := (* "bit" jest typem *)
    | tak : bit         (* "tak" jest elementem typu "bit" *)
    | nie : bit         (* "nie" jest elementem typu "bit" *)
    .                   (* i nie ma żadnych więcej elementów typu "bit" *)

(** * Proste funkcje *)

Definition negacja : bit -> bit := (* "negacja" to funkcja, która bierze bit i zwraca bit *)
  fun b : bit =>        (* weź jako argument bit nazwany "b" *)
    match b with     (* sprawdźmy, jakiej "b" jest postaci *)
        | tak => nie  (* gdy "b" to "tak", wynikiem funkcji jest "nie" *)
        | nie => tak  (* gdy "b" to "nie", wynikiem funkcji jest "tak" *)
    end.             (* koniec definicji *)

(** * Równość i obliczenia *)

Goal tak = tak. (* Po słowie kluczowym "Goal" piszemy, co chcemy udowodnić. *)
Proof.          (* Dowód zaczynamy od "Proof". *)
  reflexivity.  (* Każda rzecz jest równa samej sobie i Coq o tym wie. *)
Qed.            (* Dowód kończymy słowem "Qed" - od łac. "Quod erat demonstrandum" - "Co należało udowodnić" *)

Goal tak = nie.
Proof.
  Fail reflexivity. (* "tak" to coś innego niż "nie" i Coq to wie - nie da się go zrobić w wała *)
Abort. (* Zakończenie dowodu za pomocą "Abort" oznacza, że się poddajemy. *) 

Goal negacja tak = nie.
Proof.
  cbv delta.   (* Pierwszym krokiem obliczeń jest odwinięcie definicji. *)
  cbn beta.    (* Kolejnym krokiem jest podstawienie wartości "tak" za argument funkcji. *)
  cbn iota.    (* Ostatnim krokiem jest wykonanie dopasowania i zwrócenie odpowiedniej wartości. *)
  reflexivity. 
Qed.

Goal negacja nie = tak.
Proof.
  cbv. (* Oczywiście można obliczyć wszystko za jednym zamachem. *)
  reflexivity.
Qed.

Lemma negacja_negacji :
  forall b : bit, negacja (negacja b) = b.
Proof.
  intro b.    (* Weźmy dowolne b : bit *)
  destruct b. (* Analiza przypadków: b może mieć jedną z dwóch postaci (tak/nie) *)
    cbv. (* Obliczamy wynik. *) reflexivity. (* Udało się. *)
    reflexivity. (* Nie musimy ręcznie prosić o policzenie - Coq sam wie, żeby to zrobić. *)
Qed.

Lemma tylko_dwie_opcje :
  forall b : bit, b = tak \/ b = nie.
Proof.
  intro b. (* Weźmy dowolne b : bit *)
  destruct b. (* Analiza przypadków *)
    left. (* Będziemy dowodzić pierwszej możliwości (tak = tak). *) reflexivity.
    right. (* Chcemy dowodzić drugiej możliwości. *) reflexivity.
Qed.

(** * Przydatne komendy *)

(* [Check] sprawdza typ obiektu. *)
Check tak.

(* [Print] wyświetla definicję obiektu. *)
Print bit.

(* Znajdź wszystkie rzeczy związane z [bit]. *)
Search bit.

(** Listy *)

Inductive lista : Type :=
    | pusta : lista
    | cons  : bit -> lista -> lista.

Definition równe : bit -> bit -> bit :=
  fun b1 b2 : bit =>
    match b1, b2 with
        | tak, tak => tak
        | nie, nie => tak
        | _  , _   => nie
    end.

Definition lub : bit -> bit -> bit :=
    fun b1 b2 : bit =>
      match b1 with
          | tak => tak
          | _   => b2
      end.

Fixpoint zawiera (l : lista) (b : bit) : bit :=
match l with
    | pusta     => nie
    | cons c l' => lub (równe b c) (zawiera l' b)
end.

Fixpoint sklej (l1 l2 : Lista) : List a :=
match l1 with
    | pusta => l2
    | cons n l3 => cons n (sklej l3 l2)
end.



(** * Dlaczego warto nauczyć się Coqa? *)

(** Języki funkcyjne ekspandują. *)


(** * Kim jesteśmy, dokąd zmierzamy? *)

(** Najłatwiej jest zapoznać się z Coqiem używając przeglądarkowego środowiska
    jsCoq (https://jscoq.github.io/scratchpad.html). Polecam - nie trzeba nic
    instalować i ma rozsądne podpowiadanie składni dla początkujących.

    Jeżeli chcecie zacząć dłuższą przygodę z Coqiem, polecam go zainstalować
    (https://coq.inria.fr/) - śmiga wtedy lepiej niż w przeglądarce. Musicie
    też wybrać sobie jakieś IDE:
    1. CoqIDE (https://coq.inria.fr/) - standardowe IDE do Coqa, polecam.
    2. Visual Studio Code (https://code.visualstudio.com/) z pluginem dla
       Coqa - również całkiem spoko.
    3. Emacs (https://www.gnu.org/software/emacs/) z pluginem Proof General
       (https://proofgeneral.github.io/) - nie polecam.
    4. W ostateczności można też używać Coqa z poziomu konsoli, ale tym
       bardziej nie polecam.

    Przyda się też troche materiałów dydaktycznych:
    1. Nagranie z zeszłorocznych dni otwartych (po polsku, ok. 20 min):
       https://www.youtube.com/watch?v=njgUPWlWYUM&t=6936s
    2. Nagranie z prezentacji podobnej do naszej (po angielsku, 3 godziny):
       https://www.youtube.com/watch?v=5e7UdWzITyQ
    3. Książka Software Foundations, pierwsza połowa pierwszego tomu
       (po angielsku): https://softwarefoundations.cis.upenn.edu/lf-current/toc.html
    
    Jeżeli słuchanie/czytanie po angielsku sprawia wam problem, możecie też przeczytać
    pierwsze rozdziały mojej własnej twórczości: https://wkolowski.github.io/CoqBookPL/
    (uwaga, dość niekompletna i trochę nie po kolei).
    
    Przydatne linki:
    1. Strona domowa: https://coq.inria.fr/
    2. GitHub: https://github.com/coq/coq
    3. Forum: https://coq.discourse.group/
    4. Czat: https://coq.zulipchat.com/login/
    5. Q&A: https://stackoverflow.com/questions/tagged/coq
    
    Jeżeli macie pytania, piszcie (asekuracyjnie podaje uczelniane maile):
    1. Ja: 299899@uwr.edu.pl
    2. Nie ja: tomasz.drab@cs.uni.wroc.pl *)