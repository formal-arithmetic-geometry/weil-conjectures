/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage

/-!
# Strict-perfect packages

Let `C` be a preadditive category and `Λ` an object of `C` (the structure sheaf of a ringed topos,
the monoidal unit of a category of sheaves of modules). A *finite projective* object is a retract
of a finite direct sum `Λᴺ = ⨁ Λ`. A *strict-perfect package* for a cochain complex `F` is the
datum of bounds outside of which `F` vanishes and, for every degree `r`, of an integer `N_r` and
of maps `i_r : F^r ⟶ Λ^{N_r}` and `p_r : Λ^{N_r} ⟶ F^r` with `p_r ∘ i_r = 1`. This is blueprint
`def-weil-pbc-strict-perfect-coefficient-package`.

The associated idempotents `e_r = i_r ∘ p_r` of `Λ^{N_r}` satisfy `e_r² = e_r`, `p_r e_r = p_r`
and `e_r i_r = i_r`.

If `C` is abelian, the image in the derived category of a complex with a strict-perfect package
lies in every triangulated subcategory which is stable under retracts and contains `Λ`
(`CochainComplex.StrictPerfectPackage.prop_Q_obj`): the stupid filtration reduces it to its
terms, which are retracts of finite sums of copies of `Λ`.
-/

@[expose] public noncomputable section

namespace CochainComplex

open CategoryTheory Limits

section Package

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C]

/-- A *strict-perfect package* (blueprint `def-weil-pbc-strict-perfect-coefficient-package`)
for a cochain complex `F` with respect to an object `Λ`: bounds `lo` and `hi` such that `F` is
strictly concentrated in degrees `[lo, hi]`, and for every degree `r` an integer `N_r` together
with a presentation of `F^r` as a retract of `Λ^{N_r} = ⨁ Λ`, that is, maps
`i_r : F^r ⟶ Λ^{N_r}` and `p_r : Λ^{N_r} ⟶ F^r` with `p_r ∘ i_r = 1`. -/
structure StrictPerfectPackage (Λ : C) (F : CochainComplex C ℤ) where
  /-- A lower bound for the degrees in which `F` does not vanish. -/
  lo : ℤ
  /-- An upper bound for the degrees in which `F` does not vanish. -/
  hi : ℤ
  isStrictlyGE : F.IsStrictlyGE lo
  isStrictlyLE : F.IsStrictlyLE hi
  /-- The rank `N_r` of the finite free object `Λ^{N_r}` of which `F^r` is a retract. -/
  rank (r : ℤ) : ℕ
  /-- The presentation of `F^r` as a retract of `Λ^{N_r}`, with `i_r = (retract r).i` and
  `p_r = (retract r).r`. -/
  retract (r : ℤ) : Retract (F.X r) (⨁ fun _ : Fin (rank r) ↦ Λ)

namespace StrictPerfectPackage

variable {Λ : C} {F : CochainComplex C ℤ} (P : StrictPerfectPackage Λ F)

attribute [instance] isStrictlyGE isStrictlyLE

/-- The idempotent `e_r = i_r ∘ p_r` of `Λ^{N_r}` attached to the retraction of `F^r`. -/
def idem (r : ℤ) : (⨁ fun _ : Fin (P.rank r) ↦ Λ) ⟶ ⨁ fun _ : Fin (P.rank r) ↦ Λ :=
  (P.retract r).r ≫ (P.retract r).i

@[reassoc (attr := simp)]
lemma idem_idem (r : ℤ) : P.idem r ≫ P.idem r = P.idem r := by
  simp [idem]

/-- `p_r ∘ e_r = p_r`. -/
@[reassoc (attr := simp)]
lemma idem_r (r : ℤ) : P.idem r ≫ (P.retract r).r = (P.retract r).r := by
  simp [idem]

/-- `e_r ∘ i_r = i_r`. -/
@[reassoc (attr := simp)]
lemma i_idem (r : ℤ) : (P.retract r).i ≫ P.idem r = (P.retract r).i := by
  simp [idem]

end StrictPerfectPackage

end Package

section Derived

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] {Λ : C}
  {F : CochainComplex C ℤ} (P : StrictPerfectPackage Λ F)

namespace StrictPerfectPackage

include P in

/-- Let `S` be a triangulated subcategory of `D(C)`, closed under isomorphisms and stable under
retracts, which contains `Λ` placed in degree `0`. Then it contains every complex admitting a
strict-perfect package with respect to `Λ`. -/
lemma prop_Q_obj (S : ObjectProperty (DerivedCategory C)) [S.IsTriangulated]
    [S.IsClosedUnderIsomorphisms] [S.IsStableUnderRetracts]
    (hΛ : S ((DerivedCategory.singleFunctor C 0).obj Λ)) :
    S (DerivedCategory.Q.obj F) := by
  have hS : (S.inverseImage DerivedCategory.Qh) ((HomotopyCategory.quotient C _).obj F) :=
    HomotopyCategory.mem_subcategory_of_strictly_bounded _ F P.lo P.hi fun n _ _ ↦ by
      change S ((DerivedCategory.singleFunctor C 0).obj (F.X n))
      refine S.prop_of_retract ((P.retract n).map (DerivedCategory.singleFunctor C 0)) ?_
      exact S.prop_of_iso ((DerivedCategory.singleFunctor C 0).mapBiproduct _).symm
        (S.prop_of_isLimit_fan (biproduct.isLimit _) fun _ ↦ hΛ)
  exact S.prop_of_iso ((DerivedCategory.quotientCompQhIso C).app F) hS

end StrictPerfectPackage

end Derived

end CochainComplex
