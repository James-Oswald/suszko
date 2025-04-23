import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card

section Language

/-
Parse Trees under a set of connectives:
IMPLEMENTATION NOTES: Putting the (a : α) after the : is required! See:
https://proofassistants.stackexchange.com/questions/4326/defining-a-parameterized-property-in-lean-4
-/
inductive ParseTree
  {α : Type}
  (c : (n : Nat) -> (Set ((Fin n -> α) → α))) :
  (a : α) -> Type
where
| node {a : α} {n : Nat} (f : (Fin n -> α) → α) (args : (Fin n -> α)) :
  c n f -> (∀ (i : Fin n), ParseTree c (args i)) ->
  f args = a -> ParseTree c a

/-
Kadlecikova 2025 page 11:
"A language L ... is the set of formulae built on the
non-empty set of atoms (Atom) and the propositional
connectives (C), with the set of sentences of L the
smallest set including Atom and closed under the
connectives from C."
-/
class Language (α : Type) where
  -- Equality of formulae is decidable
  α_deq : DecidableEq α
  -- Data: The set of atoms and connectives in the language
  -- Atoms are treated as 0-place connectives
  cons (n : Nat) : Set ((Fin n -> α) → α)
  -- Condition: The set of atoms is non-empty
  atoms_ne : (cons 0).Nonempty
  -- The language is closed under the connectives
  -- IE, every element of the language has parse tree
  -- under the connectives
  -- PROOF HINT: In Lean, we typically define languages as inductive types,
  -- thus we prove typically prove this via induction on the
  -- structure of the underlying type
  -- COMMENT: This places no restriction that the parse
  -- tree is unique, which probably violates the spirit of
  -- the definition of a language
  cons_parsable : ∀ (a : α), Nonempty (ParseTree cons a)

-- The following are helpers to bundle real connectives
-- often in the form of α -> ...n -> α into
-- functions of type (Fin n → α) -> α
def Language.bundleZero {α} (f : α) : (Fin 0 → α) -> α :=
  λ _ => f

instance {α}: Coe α ((Fin 0 → α) -> α) where
  coe := Language.bundleZero

def Language.bundleOne {α} (f : α -> α) : (Fin 1 → α) -> α :=
  λ f1 => f (f1 0)

instance {α}: Coe (α -> α) ((Fin 1 → α) -> α) where
  coe := Language.bundleOne

-- Bundle a two place connective into a Fin 2 function
def Language.bundleTwo {α} (f : α -> α -> α) : (Fin 2 → α) -> α :=
  λ f2 => f (f2 0) (f2 1)

instance {α}: Coe (α -> α -> α) ((Fin 2 → α) -> α) where
  coe := Language.bundleTwo

-- The Language of propositional logic
inductive PropFormula : Type
| atom : String -> PropFormula
| not : PropFormula -> PropFormula
| and : PropFormula -> PropFormula -> PropFormula
deriving Inhabited, DecidableEq, Repr

def PropFormula.connectives (n : Nat) : Set ((Fin n -> PropFormula) -> PropFormula) :=
  match n with
    | 0 => {↑(PropFormula.atom s) | s : String}
    | 1 => {↑PropFormula.not}
    | 2 => {↑PropFormula.and}
    | _ => ∅

lemma PropFormula.atoms_ne : (PropFormula.connectives 0).Nonempty := by
  simp only [Set.Nonempty, Set.mem_setOf_eq];
  exists (λ _ => PropFormula.atom "a")
  exists "a"

lemma PropFormula.cons_parsable : ∀ (a : PropFormula), Nonempty (ParseTree PropFormula.connectives a) :=
by
    intro f
    induction f
    . case atom s =>
      apply Nonempty.intro
      apply ParseTree.node (Language.bundleZero (PropFormula.atom s)) (λ _ => PropFormula.atom s)
      . simp only [PropFormula.connectives, setOf, exists_apply_eq_apply]
      . apply Fin.elim0
      . rfl
    . case not f ih =>
      apply Nonempty.intro
      have ih := Classical.choice ih
      apply ParseTree.node (Language.bundleOne PropFormula.not) (λa => f)
      . rfl
      . intro i
        exact ih
      . simp only [Language.bundleOne]
    . case and f1 f2 ih1 ih2 =>
      apply Nonempty.intro
      have ih1 := Classical.choice ih1
      have ih2 := Classical.choice ih2
      apply ParseTree.node (Language.bundleTwo PropFormula.and) (λa => match a with | 0 => f1| 1 => f2)
      . rfl
      . intro i
        match i with
        | 0 => exact ih1
        | 1 => exact ih2
      . simp only [Language.bundleTwo]

instance : Language PropFormula where
  α_deq := inferInstance
  cons := PropFormula.connectives
  atoms_ne := PropFormula.atoms_ne
  cons_parsable := PropFormula.cons_parsable
