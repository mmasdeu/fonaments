import Verbose.Catalan.Help
import Mathlib.Tactic

/-
TUTORIAL DE LEAN

Seminari de Fonaments, curs 2023-24
-/

/-
L'objectiu del seminari és entendre com es treballa amb un assistent de demostracions.

En aquest cas, aprendrem LEAN.

Ens trobarem amb enunciats de resultats que ens són familiars de classe, i l'objectiu serà
introduir la demostració a l'ordinador, de manera que verifiqui que tots els passos que fem
són correctes.

El llenguatge que farem servir està escrit en català, però és bastant rígid, així que haurem
de tenir molt de compte en com escrivim, i no deixar-nos ni puntuació, ni accents,...
-/

/-
A la dreta de la pantalla veurem l'"Infoview", que ens mostra l'estat de la demostració al lloc
on tinguem el cursor. Hi veurem les hipòtesis i la conclusió a la què volem arribar.

Per poder avançar en la demostració farem servir "tàctiques", que són les frases que escrivim
i que LEAN verifica. Segons què vulguem fer en cada pas haurem d'escollir una tàctica o altra.
Seguidament veurem les tàctiques que farem servir en aquest seminari.
-/

/- ∀ a l'objectiu
  Si a l'objectiu hi ha un ∀, la tàctica `Sigui...` ens donarà un element arbitrari. Observeu
  les diferents variacions que hi ha.
-/

example (P : ℕ → Prop) : ∀ x, P x := by
  Sigui x
  sorry

example (P : ℕ → Prop) : ∀ x, (x ≠ 3) → P x := by
  Sigui x ≠ 3
  sorry

example (P : ℕ → Prop) : ∀ x, (x ≠ 3) → P x := by
  Sigui x tal que h
  sorry

example (P : ℕ → ℕ  → Prop) : ∀ x y, (x ≠ y) → P x y := by
  Siguin x y tals que h
  sorry


/- ∀ a una hipòtesi
  Si una hipòtesi té un ∀, podem *especialitzar-la* a un valor determinat.
  També podem aplicar-la a un valor i així obtenim una nova hipòtesi (un cas particular).
-/

example (P : ℕ → Prop) (h : ∀ x, P x) : False := by
  ajuda
  sorry

example (P : ℕ → Prop) (h : ∀ x, P x) : False := by
  Per h aplicat a 2 obtenim h'
  sorry


/-  ∃ a l'objectiu:
  Si volem demostrar un objectiu de la forma "∃ x, ...", hem de proporcionar l'x que funciona.
  Això ho fem escrivint "Vegem que 3 funciona", per exemple.
-/

example : ∃ x : ℕ, x > 5 := by
  Vegem que 7 funciona
  sorry


/- ∃ a una hipòtesi
  Quan una hipòtesi ens garanteix l'existència d'un element amb unes determinades propietats,
  podem obtenir aquest element (potser farà servir l'axioma de l'elecció) escrivint:

    Per h obtenim x tal que hx

  o bé

    Per h aplicat a 3 obtenim x tal que hx
-/
example (h : ∃ x, x > 3) : False := by
  Per h obtenim x tal que hx
  sorry

example (h : ∀ y : ℕ, ∃ x, x > y) : False := by
  Per h aplicat a 5 obtenim x tal que hx
  sorry

-- En aquest example, la paraula `noncomputable` és necessària perquè fem servir l'axioma de l'elecció
noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Per h triem g tal que (H : ∀ (y : ℕ), f (g y) = y)
  exact g

/- → a l'objectiu
  El símbol P → Q significa "P implica Q". Si tenim un objectiu d'aquest tipus, podem
  començar suposant P cert, i demostrar Q. Això es fa amb la tàctica `Suposem que`
  (el `que` és opcional). Hem de donar un nom a la hipòtesi (al fet que P sigui cert),
  i això ho indiquem amb un nom qualsevol seguit de `:`, com a l'exemple.
-/

example (P Q : Prop) : P → Q := by
  Suposem que h : P
  sorry

/- → a una hipòtesi:
  Si volem fer servir una hipòtesi del tipus P → Q, hem de tenir una demostració de P
  (i aleshores podrem concloure Q). Si hP és una demostració de P, podem dir
  `Per h aplicat a hP obtenim hQ` i obtindrem una demostració hQ de Q.
-/

example (a : ℕ) (h : a > 2 → a^2 > 4) (hP : a > 2) : a^2 > 4 := by
  Per h aplicat a hP obtenim hQ
  sorry

/- ↔ a l'objectiu:
  Si l'objectiu és si i només si, demostrem la doble implicació amb:
    Demostrem/Vegem primer que P → Q
    ...
    Demostrem/Vegem ara que Q → P
  Nota: Si l'enunciat és massa complicat, podem escriure:

  Demostrem primer que _ <--- una barra baixa!

  (LEAN és prou llest per saber quin enunciat toca).
-/

example (x y : ℕ) : x > y ↔ y < x := by
  Demostrem primer que x > y → y < x
  {
    sorry
  }
  Demostrem ara que _
  {
    sorry
  }

/- ↔ a una hipòtesi
  Quan tenim una equivalència (o una igualtat, funciona igual) a una hipòtesi, podem reescriure
  l'ocurrència de l'esquerra per la de la dreta fent servir la tàctica:

  Reescrivim mitjançant/via h (at h')

  El paràmetre opcional `at h'` indica que volem fer la substitució a la hipòtesi `h'`
  i no a l'objectiu. Fixeu-vos que diu `at` i no `a`!
-/

example (x y : ℕ)  (h : x > y ↔ y < x)  : x > y:= by
  Reescrivim via h
  sorry
  done

example (x y : ℕ)  (h : x > y ↔ y < x)  (h2 : x > y → x = 3): x > y:= by
  Reescrivim via h at h2
  sorry


/- ∧ a l'objectiu:
  De manera molt semblant a quan ens trobem amb una equivalència, cal demostrar les dues proposicions,
  i es fa amb la mateixa tàctica.
-/
example (P Q : Prop) : P ∧ Q := by
  Demostrem primer que Q
  {
    sorry
  }
  Demostrem ara que P
  {
    sorry
  }

/- ∧ a una hipòtesi:
  Quan tenim una conjunció en una hipòtesi, realment tenim dues (o més hipòtesis combinades).
  Si les volem per separat, ho fem escrivint:

  Per h obtenim h1 h2 h3...

-/

example (h : P ∧ Q ∧ R) : False := by
  Per h obtenim hP hQ hR
  sorry

/- ∨ a  l'objectiu:
  Per demostrar una disjunció, haurem de decidir quin dels dos enunciats volem (o sabem) demostrar.
  Ho especificarem amb "Demostrem que ...", i ja no ens caldrà demostrar l'altre (òbviament!)
-/

example : 2 < 3 ∨ 3 < 2 := by
  Demostrem que 2 < 3
  sorry

/- ∨ a una hipòtesi:
  Si volem utilitzar una hipòtesi disjuntiva, la demostració es dividirà en dos (o més) casos, segons
  quina de les proposicions sigui certa. Ho escriurem amb

  Dividim h en casos

-/

example (x y : ℕ) (h : x > y ∨ y < x) : False := by
  Dividim h en casos
  {
    sorry -- x > y
  }
  {
    sorry -- y < x
  }
  done


/- Separació en casos

  Si volem fer una demostració per casos, podem triar un enunciat i dividir en casos segons
  si aquest enunciat és cert o fals. Això es fa amb la tàctica
  `Dividim en casos segons si ... o no`, com a l'exemple:
-/

example (n : ℕ) : n^2 >= 0 := by
  Dividim en casos segons si h : n > 0 o no
  {
    sorry
  }
  {
    sorry
  }

/- Demostració per inducció

LEAN ens permet també fer demostracions per inducció (i inducció forta) amb els següents esquemes:

-/

example : ∀ n, n < 5 := by
  Demostrem per inducció que h: ∀ n, n < 5
  {
    sorry -- case base
  }
  {
    sorry -- cas inductiu
  }
  Apliquem h

example : ∀ n, n < 5 := by
  Demostrem-ho per inducció
  {
    sorry -- case base
  }
  {
    sorry -- cas inductiu
  }
  done

example : ∀ n, n < 5 := by
  Demostrem-ho per inducció forta en n
  Suposem HI
  sorry
  done

/- Demostració per reducció a l'absurd

  Podem fer una demostració per reducció a l'absurd escrivint

  Procedim per reducció a l'absurd

  Si volem tenir accés a la negació de l'objectiu inicial, hem de fer:

  Suposem per reducció a l'absurd que hc : P

  on `hc` és el nom que volem donar, i `P` és equivalent a la negació de l'objectiu inicial

-/


example (n : ℕ) : n^2 >= 0 := by
  Procedim per reducció a l'absurd
  sorry
  done

example (n : ℕ) : n^2 >= 0 := by
  Suposem per reducció a l'absurd que hc : n^2 < 0
  sorry
  done


/- Simplificar negacions
  A vegades (per exemple en demostracions per contradicció) volem simplificar alguna
  proposició lògica, on apareixen negacions combinades amb quantificadors. Veiem en els
  següents exemples com funciona la tàctica

  Simplifiquem les negacions (at h)
-/

example : ¬ ∀ x, 3 ≤ x := by
  Simplifiquem les negacions
  sorry
  done

example (h : ¬ ∀ x, 3 ≤ x) : ∃ x, x < 3 := by
  Simplifiquem les negacions at h
  exact h


/- Fets / afirmacions

  Sovint és útil demostrar passos intermitjos durant la demostració. L'esquema següent
  ens permet fer-ho (`Fet` i `Afirmació` són equivalents, i també `Tenim`). Fixem-nos que
  el bloc on demostrem el fet ha d'estar delimitat per claus.

-/

example (n : ℕ) : n ≥ 5 := by
  Fet h : n = 5
  {
    sorry
  }
  linarith
  done

example (n : ℕ) : n ≥ 5 := by
  Afirmació h : n = 5
  {
    sorry
  }
  linarith
  done

/- Sigui/Considerem/Definim/Denotem ... := ...
  A vegades convé donar nom a una expressió complicada. Ho fem amb les frases equivalents
  `Sigui`, `Considerem`, `Definim`, o `Denotem`. Després de la variable hem d'utilitzar
  el símbol `:=`.
-/
example : False := by
  Sigui  a := 3
  sorry
  done

example (b : ℕ) : False := by
  Considerem  a := 3 * b + 1
  sorry
  done

/- Cadenes d'igualtats / desigualtats / equivalències

  Un altre tipus de demostració és la que surt d'encadenar (per transitivitat) una
  cadena d'igualtats o desigualtats. L'esquema que es fa servir en aquest cas
  és bastant gràfic: al costat de cada (des)igualtat hi hem de posar la justificació.

  Les preposicions `de` i `per` signifiquen coses diferents: si volem fer servir una tàctica,
  fem servir `per`, mentre que si tenim el terme explícit fem servir `de`.
-/


example : 3 < 10 := by
  Calc  3 ≤ 4   per linarith -- si tenim una tàctica
        _ < 5   de Nat.lt.base 4 -- si tenim un terme explícit
        _ ≤ 2*5 per linarith
        _ = 10  de rfl



/- Raonament invers
  Si volem demostrar Q i sabem un teorema que diu P → Q, n'hi ha prou amb demostar P
  (ull! pot ser que P sigui impossible de demostrar amb les hipòtesis que tenim disponibles!).
  Per fer aquest tipus de raonament, fem servir el següent esquema.
-/

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Per h n'hi ha prou amb demostrar P
  sorry


/- Concloure demostracions a partir d'hipòtesis existents
  Quan l'objectiu segueix directament d'una hipòtesi `h` i càlculs trivials, podem intentar
  demostrar-lo escrivint

  Concloem amb h
-/

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Per h n'hi ha prou amb demostrar P
  Concloem amb h'

/- Altres tàctiques

  Hi ha moltes altres tàctiques, i algunes ens poden ser útils en diferents parts. Per exemple,
  la tàctica `nlinarith` demostra objectius que involucren igualtats o desigualtats. La
  tàctica `group` demostra identitats que es satisfan en qualsevol grup (additiu o multiplicatiu),
  la tàctica `ring` fa el mateix per anells,...

  També hi ha tàctiques que busquen resultats ja coneguts. La més senzilla s'anomena `exact?`, i
  busca si hi ha algun teorema que demostra l'objectiu exactament, fent servir
  les hipòtesis disponibles.
-/

