
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card

/-
Kadlecikova 2025 page 11:
"A language L ... is the set of formulae built on the
non-empty set of atoms (Atom) and the propositional
connectives (C), with the set of sentences of L the
smallest set including Atom and closed under the
connectives from C."
-/
structure Lang where
  {α : Type}
  [α_deq : DecidableEq α]
  atoms : Set α
  atoms_ne : atoms.Nonempty
  sents : Set α
  atoms_subset : atoms ⊆ sents
  -- sets of n-place connectives, indexed by their arity
  cons (n : Nat) : Set ((Fin n → α) → α)
  -- The language is closed under the connectives
  sents_subset : ∀ n, ∀ f ∈ cons n, ∀a, f a ∈ sents

/-
Implementation notes:
We need this dumb instance so that Lean can generate
the definition of the union of finite sets of sentences.
-/
instance {l : Lang} : DecidableEq l.α := l.α_deq

/-
Kadlecikova 2025 page 11 Def 6 (from Shramko & Wansing):
A valuation system Vs (a symmetric matrix) for the propositional
language L is a triple ⟨V, D, F⟩, with:
• V a non-empty set with at least two elements,
• D a non-empty proper subset of V, and
• F = {f_c_1 , ..., f_c_m } a set of functions such that f_i is an
n-place function on V for each n-place connective c_i.
-/
structure ValuationSystem (l : Lang) where
  -- The underlying type of truth values
  α : Type
  α_dec : DecidableEq α
  -- The Non-empty Set of truth values
  V : Set α
  -- If V is finite, it has at least two elements
  V_geq_2 [Fintype V] : Finset.card V.toFinset ≥ 2
  V_ne : V.Nonempty
  -- The Non-empty subset of designated values
  D : Set α
  D_ne : D.Nonempty
  D_subset : D ⊂ V
  -- F n is the set of n-place functions on V, and we impose
  -- a condition that all n-place functions have a bijection (F_bij)
  -- to the set of n-place connectives on the language.
  F (n : Nat) :          Set ((args : Fin n → α) → α)
  F_bij (n : Nat) :      ((Fin n → l.α) → l.α) → ((Fin n → α) → α)
  F_bij_cond (n : Nat) : Set.BijOn (F_bij n) (l.cons n) (F n)



structure AtomValuation
  {l : Lang}
  (vs : ValuationSystem l)
where
  -- The function that maps atoms to the valuation set
  a : l.α → vs.α
  -- The image of the atom valuation function is a
  -- subset of the valuation set
  a_image : Set.MapsTo a l.atoms vs.V

/-
Kadlecikova 2025 page 11 Def 7 (from Shramko & Wansing):
A valuation function v_a : L -> V is defined as adhering
to the following constraints:
1. ∀p ∈ Atom, v_a(p) = a(p);
2. ∀ci ∈ C, va(ci(A1, ..., An)) = fi(va(A1), ..., va(An))
-/
structure ValuationFunction
  {l : Lang}
  {vs : ValuationSystem l}
  (va : AtomValuation vs)
where
  -- In the above formalism the valuation of the atoms
  -- is parameterized out, we probably need to do this?
  -- The function that maps atoms to the valuation set
  -- The actual valuation function
  v : l.α → vs.α
  --v_img : v '' l.sents ⊆ vs.V
  v_image : Set.MapsTo v l.sents vs.V

  -- conditions on the valuation functions
  -- 1. ∀p ∈ Atom, v_a(p) = a(p);
  v_atoms : ∀ p ∈ l.atoms, v p = va.a p
  -- 2. ∀ci ∈ C, va(ci(A1, ..., An)) = fi(v_a(A1), ..., v_a(An))
  v_cons {n} : ∀ ci ∈ l.cons n, ∀ A, v (ci A) = vs.F_bij n ci (v ∘ A)

/-
Kadlecikova 2025 page 11 Def 8
A symmetric model MS = ⟨VS, v_a⟩ allows us to define entailment in the
symmetric model: Γ ⊨MS ∆ iff ∀γ ∈ Γ : va(γ) ∈ D ⇒ va(∆) ∩ D ≠ ∅
-/
structure SymmetricModel (l : Lang) where
  vs : ValuationSystem l
  v  : (a : AtomValuation vs) -> ValuationFunction a

/-
Implementation notes:
Unclear if i am allowed to place parenthesis where i did,
the more natural interpretation from the symbols is
∀ γ ∈ Γ, ((M.v.v γ) ∈ M.vs.D -> (M.v.v '' Δ) ∩ M.vs.D ≠ ∅)
but this makes things annoying and the slides seem to suggest this
is a valid interpretation.
-/
def entails_Ms {l : Lang}
  (M : SymmetricModel l)
  (a : AtomValuation M.vs)
  (Γ Δ : Finset l.α)
: Prop :=
  let v_a := (M.v a).v;
  (∀ γ ∈ Γ, (v_a γ) ∈ M.vs.D) -> (v_a '' Δ) ∩ M.vs.D ≠ ∅
-- note that v_a '' Δ is the image of the set Δ under v_a

notation Γ "⊨MS[" M "|" a "]" Δ => entails_Ms M a Γ Δ

-- The type of consequence relations over a language l.
abbrev ConsequenceRelation (l : Lang) := Finset l.α -> Finset l.α -> Prop

/-
Kadlecikova 2025 page 13 Def 9
A logic is an ordered pair ⟨L, ⊨⟩, where
• L is the propositional language as above, and
• ⊨ is defined in any appropriate way. Here, let ⊨ be ⊨MS .
-/
structure Logic where
  l : Lang
  cr : ConsequenceRelation l

/-
Kadlecikova 2025 page 13
A logic is trivial if for any Γ, ∆ : Γ ⊨ ∆.
-/
def Trivial (l : Logic) : Prop :=
  ∀ Γ Δ, l.cr Γ Δ

/-
A consequence relation is Tarskian if it meets these conditions:
1. If Γ ⊨ φ then Γ, ∆ ⊨ φ Monotonicity
2. φ ⊨ φ Reflexivity
3. If for every δ ∈ ∆: Γ ⊨ δ and ∆ ⊨ ψ then Γ ⊨ ψ Transitivity
-/
/-
Implementation notes:
Im interpreting lowercase greek letters as singleton sets since
Jitka's work only uses set-set consequence relations.
-/
def ConsequenceRelation.Monotonic (cr : ConsequenceRelation l) : Prop :=
  ∀ Γ Δ ϕ, cr Γ {ϕ} -> cr (Γ ∪ Δ) {ϕ}

def ConsequenceRelation.Rfl (cr : ConsequenceRelation l) : Prop :=
  ∀ ϕ, cr {ϕ} {ϕ}

def ConsequenceRelation.Trans (cr : ConsequenceRelation l) : Prop :=
  ∀ Γ Δ ψ, (∀ δ ∈ Δ, cr Γ {δ}) ∧ cr Δ {ψ} -> cr Γ {ψ}

def Tarskian (cr : ConsequenceRelation l) : Prop :=
  cr.Monotonic ∧ cr.Rfl ∧ cr.Trans


lemma eMS_mono: ConsequenceRelation.Monotonic (entails_Ms M a) := by
  rw [ConsequenceRelation.Monotonic]
  intros Γ Δ ϕ h
  simp_all only [entails_Ms]
  intro a
  simp_all only [Finset.mem_union, true_or, implies_true,
    Finset.coe_singleton, Set.image_singleton, ne_eq,
    Set.singleton_inter_eq_empty, not_not, forall_const,
    not_true_eq_false, not_false_eq_true]


lemma eMS_rfl: ConsequenceRelation.Rfl (entails_Ms M a) := by
  rw [ConsequenceRelation.Rfl]
  intro ϕ
  simp_all only [entails_Ms]
  intro a
  simp_all only [Finset.mem_singleton, forall_eq,
    Finset.coe_singleton, Set.image_singleton,
    ne_eq, Set.singleton_inter_eq_empty,
    not_true_eq_false, not_false_eq_true]

lemma eMS_trans : ConsequenceRelation.Trans (entails_Ms M a) := by
  rw [ConsequenceRelation.Trans]
  intros Γ Δ ψ
  simp only [entails_Ms]
  intro a a_1
  simp_all only [implies_true, Finset.coe_singleton,
    Set.image_singleton, ne_eq, Set.singleton_inter_eq_empty,
    not_not, forall_const, not_true_eq_false, not_false_eq_true]

theorem eMS_tarskian : Tarskian (entails_Ms M a) :=
  ⟨eMS_mono, eMS_rfl, eMS_trans⟩
