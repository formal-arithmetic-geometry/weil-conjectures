module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Discrete.Basic

/-! # Finite-cell left dg modules

Source: Stacks Project, dga.tex, Tag 09R3, proposition-compact (2),
and Tag 0FQ0 for the left-module convention
(blueprint: def-sfb-dg-finite-cell-module).

The terminal site with the trivial topology presents sheaves on a point.
Its integer ring sheaf makes the existing sheaf dg interface apply to ordinary
associative unital dg algebras over the integers.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SheafDg

/-- The integer coefficient sheaf on the terminal site. Its sole value is ULift Z;
all restrictions are identities, and every presheaf is a sheaf for the trivial topology.
Source: Stacks, dga.tex, definition-dga; sdga.tex, definition-dga on a point
(blueprint: def-sfb-dg-finite-cell-module). -/
def pointIntegers : Sheaf (⊥ : GrothendieckTopology (Discrete PUnit)) CommRingCat.{u} :=
  ⟨(Functor.const _).obj (CommRingCat.of (ULift.{u} ℤ)), Presheaf.isSheaf_bot _⟩

variable {B : Type v} [Category.{w} B] [EssentiallySmall.{u} B]
  {J : GrothendieckTopology B} {S : Sheaf J CommRingCat.{u}}

/-- A finite filtration by dg submodules, from zero to P, with finite sums of
integer shifts of the regular module as quotients. The monomorphisms identify
all stages with submodules of P through their composites and the terminal iso.
Stage 0 is F_(-1), stage j+1 is F_j. Finite sums may have no summands.
Source: Stacks, dga.tex, Tag 09R3, proposition-compact (2), left-module convention
(blueprint: def-sfb-dg-finite-cell-module). -/
def HasFiniteCellFiltration (A : Algebra S) (P : LeftModule A) : Prop :=
  ∃ (t : ℕ) (F : Fin (t + 2) → LeftModule A)
    (f : ∀ j : Fin (t + 1), F j.castSucc ⟶ F j.succ),
    (∀ j : Fin (t + 1), Mono (f j)) ∧ IsZero (F 0) ∧
      Nonempty (F (Fin.last (t + 1)) ≅ P) ∧
      ∀ j : Fin (t + 1), ∃ (n : ℕ) (k : Fin n → ℤ),
        Nonempty (cokernel (f j) ≅ ∐ (fun a : Fin n ↦ shift A (k a) (regular A)))

end CategoryTheory.SheafDg
