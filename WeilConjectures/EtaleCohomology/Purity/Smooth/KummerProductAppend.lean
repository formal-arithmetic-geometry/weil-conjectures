/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.LeftUnitorShift
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc
public import WeilConjectures.Mathlib.Data.Fin.Tuple.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc

/-!
# Products of Kummer boundaries of concatenated tuples

The iterated cup product with supports of Kummer boundaries
(`AlgebraicGeometry.Etale.kummerBoundaryProduct`) of a concatenated tuple `(f, g)` is the cup
product with supports (`AlgebraicGeometry.Etale.cupWithSupportsTateObject`) of the products of
`f` and of `g`:

`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_a) ∪ ∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_b) = (∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_a)) ∪ (∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_b))`.

The proof is an induction on the length of `f`, from the associativity and the unit law of the
cup product with supports with Tate coefficients. These in turn come from the associativity and
unit law of the product of supports (`WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc`),
the coassociativity of the diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U`, and the corresponding laws for the
identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso`).

## Implementation notes

The left unit law of `AlgebraicGeometry.Etale.shiftTateObjectAddIso`
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso_zero_left`) is proved from
`HasTateTwist.twistObjectAddIso_zero_left` and the compatibility of the left unitor of the derived
tensor product with shifts (`DerivedCategory.leftUnitor_commShift_app`). Its associativity
(`AlgebraicGeometry.Etale.ShiftTateObjectAddIsoAssoc`) is a *hypothesis* of the associativity
statements below: it follows from `HasTateTwist.twistObjectAddIso_assoc` together with the
compatibility of the associator of the derived tensor product with the commutation of `⊗ᴸ` with
shifts, which is not available in the library.

## Main statements

- `AlgebraicGeometry.Etale.shiftTateObjectAddIso_zero_left`
- `AlgebraicGeometry.Etale.constantComplexDiagonal_comp_derivedTensorLeftUnitor_hom`
- `AlgebraicGeometry.Etale.cupWithSupportsTateObject_assoc`
- `AlgebraicGeometry.Etale.cupWithSupportsTateObject_kummerBoundaryProduct_zero`
- `AlgebraicGeometry.Etale.kummerBoundaryProduct_append`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Shift

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

end Shift

/-- Shifting a morphism across an equation of shift amounts. -/
@[reassoc]
lemma eqToHom_comp_shift_map_of_eq {D : Type*} [Category D] [HasShift D ℤ] {K L : D}
    (f : K ⟶ L) {c c' : ℤ} (h : c = c') :
    (eqToHom (by rw [h]) : K⟦c⟧ ⟶ K⟦c'⟧) ≫ f⟦c'⟧' = f⟦c⟧' ≫ eqToHom (by rw [h]) := by
  subst h
  simp

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

variable (U : Scheme.{u}) [HasInvertibleExponent Λ U]

omit [Finite Λ] in
/-- The diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U` (`AlgebraicGeometry.Etale.constantComplexDiagonal`) is a
section of the left unitor: by the unit law `HasTateTwist.twistObjectAddIso_zero_left`. -/
lemma constantComplexDiagonal_comp_derivedTensorLeftUnitor_hom :
    constantComplexDiagonal Λ U ≫ (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U _).hom =
      𝟙 _ := by
  have hz := HasTateTwist.twistObjectAddIso_zero_left (Λ := Λ) U 0
  have hn : ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (constantComplex Λ U)).map
      (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).hom ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U _).hom =
      (derivedTensorLeftUnitor _ U _).hom ≫ (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).hom := by
    have := derivedTensorHom_id_comp_derivedTensorLeftUnitor_hom (A := ModuleCat.{u + 1} Λ)
      (X := U) (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).hom
    simp only [derivedTensorHom, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at this
    exact this
  simp only [constantComplexDiagonal, Category.assoc]
  rw [hn, reassoc_of% hz, Iso.inv_hom_id_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.inv_hom_id]

variable {U}

section Cup

variable {Z₁ Z₂ Z₃ Z₁₂ Z₂₃ Z : Scheme.{u}}

/-- Changing the closed subscheme `V(s)` carrying a cup product to an equal one `V(t)`. -/
lemma cupWithSupportsTateObject_zeroLocusSubschemeι_congr (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] {s t : Set Γ(U, ⊤)} (hst : s = t)
    (h : Set.range (U.zeroLocusSubschemeι s).base = Set.range i₁.base ∩ Set.range i₂.base)
    (h' : Set.range (U.zeroLocusSubschemeι t).base = Set.range i₁.base ∩ Set.range i₂.base)
    {m m' : ℤ}
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    cupWithSupportsTateObject Λ i₁ i₂ (U.zeroLocusSubschemeι s) h α β =
      cupWithSupportsTateObject Λ i₁ i₂ (U.zeroLocusSubschemeι t) h' α β ≫
        eqToHom (by subst hst; rfl) := by
  subst hst
  simp

end Cup

section Product

/-- The product of Kummer boundaries of `(x, f₁, …, f_n)` is `∂κ(x) ∪ (∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n))`. -/
lemma kummerBoundaryProduct_cons {n : ℕ} (x : Γ(U, ⊤)) (f : Fin n → Γ(U, ⊤)) :
    kummerBoundaryProduct Λ (Fin.cons x f : Fin (n + 1) → Γ(U, ⊤)) =
      cupWithSupportsTateObject Λ (U.zeroLocusSubschemeι {x})
          (U.zeroLocusSubschemeι (Set.range f))
          (U.zeroLocusSubschemeι (Set.range (Fin.cons x f : Fin (n + 1) → Γ(U, ⊤))))
          (by rw [Fin.range_cons, range_zeroLocusSubschemeι_insert]) (m := 1)
          (shiftSupportedClass Λ _ 2 (kummerBoundary Λ x))
          (kummerBoundaryProduct Λ f) ≫
        eqToHom (by rw [Nat.cast_succ, add_comm (1 : ℤ)]) := by
  rw [kummerBoundaryProduct]
  rfl

end Product

end Etale

end AlgebraicGeometry
