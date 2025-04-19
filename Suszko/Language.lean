import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card


inductive ParseTree {α : Type} (c : (n : Nat) -> (Set ((Fin n → α) → α))) (a : α) where
| leaf : (f : (Fin 0 → α) → α) -> c 0 f -> (arg : (Fin 0 → α)) -> f arg = a -> ParseTree c a
| node :
  (n : Nat) -> (f : (Fin n → α) → α) -> c n f ->
  (args : (Fin n → α)) -> ((i : Fin n) → ParseTree c (args i)) ->
  f arg = a -> ParseTree c a



section Language
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
  -- Data: The set of atoms in the language
  atoms : Set α
  -- Condition: The set of atoms is non-empty
  atoms_ne : atoms.Nonempty
  -- Condition: atoms are a subset of the sentences
  atoms_subset : atoms ⊆ @Set.univ α
  -- Data: sets of n-place connectives, indexed by their arity
  cons (n : Nat) : Set (Vector α n → α)
  -- Condition: The language is closed under the connectives
  -- i.e. we can construct all possible sentences from the
  -- connectives and the atoms
  sents_subset : sorry
    --∀ a : α : ∃

-- The following are helpers to bundle real connectives
-- often in the form of α -> ...n -> α into
-- functions of type (Fin n → α) -> α

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
| or : PropFormula -> PropFormula -> PropFormula
| impl : PropFormula -> PropFormula -> PropFormula
| iff : PropFormula -> PropFormula -> PropFormula
deriving Inhabited, DecidableEq, Repr


instance : Language PropFormula where
  α_deq := inferInstance
  atoms := {PropFormula.atom _}
  atoms_ne := ⟨PropFormula.atom "a", rfl⟩
  atoms_subset := by simp only [Set.subset_univ]
  cons n :=
    match n with
      | 0 => ∅
      | 1 => {↑PropFormula.not}
      | 2 => {↑PropFormula.and, ↑PropFormula.or, ↑PropFormula.impl, ↑PropFormula.iff}
      | _ => ∅
  sents_subset := by
    intro n f a a_1
    simp_all only [Set.mem_univ]
    sorry

end Language
