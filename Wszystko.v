(** Coq *)

Inductive bool : Type :=
    | tak : bool
    | nie : bool.

Definition negacja : bool -> bool :=
  fun b : bool =>
    match b with
        | tak => nie
        | nie => tak
    end.

Eval cbv in negacja tak.

Eval cbv delta in negacja tak.

Eval cbv delta beta in negacja tak.

Eval cbv delta beta iota in negacja tak.

Goal tak = tak.
Proof.
  reflexivity.
Qed.

Lemma negacja_negacji :
  forall b : bool, negacja (negacja b) = b.
Proof.
  intro dowolne_b.
  destruct dowolne_b.
    cbv. reflexivity.
    trivial.
Qed.

Lemma tak_lub_nie :
  forall b : bool, b = tak \/ b = nie.
Proof.
  intro dowolne_b.
  destruct dowolne_b.
    left. reflexivity.
    right. reflexivity.
Qed.




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
