/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# K-flat resolutions and the derived tensor product of étale sheaves

The derived tensor product `- ⊗ᴸ -` of `D(X_ét)` (`AlgebraicGeometry.Etale.derivedTensor`) is
the left derived bifunctor of the tensor product of complexes of étale sheaves along the K-flat
left derivability structure. This file records its description and two basic properties:

* `K₁ ⊗ᴸ K₂` is computed by `P ⊗ K₂` for any K-flat complex `P` representing `K₁`
  (`AlgebraicGeometry.Etale.derivedTensorQhIsoOfKFlat`);
* a quasi-isomorphism between K-flat complexes stays a quasi-isomorphism after tensoring with
  any complex, so that this does not depend on the K-flat model
  (`AlgebraicGeometry.Etale.quasiIso_whiskerLeft_of_kFlat`);
* the derived tensor product is triangulated in each variable
  (`AlgebraicGeometry.Etale.isTriangulated_derivedTensor`).

This is the étale counterpart of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.
TensorResolution`.

## References

* [Stacks, Tag 06YT]
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

open Functor.LaxMonoidal in
/-- The derived tensor product is computed by K-flat models: if the complex `P` is K-flat, then
`Qh(P) ⊗ᴸ Qh(K₂) ≅ Qh(P ⊗ K₂)`, the comparison map being the lax monoidal structure of
`Qh : K(X_ét) ⥤ D(X_ét)`. -/
noncomputable def derivedTensorQhIsoOfKFlat
    (P K₂ : HomotopyCategory (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))
    (hP : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P) :
    ((derivedTensor A X).obj (DerivedCategory.Qh.obj P)).obj (DerivedCategory.Qh.obj K₂) ≅
      DerivedCategory.Qh.obj (P ⊗ K₂) :=
  have := isIso_μNatTrans_Qh_app_app_of_kFlat_left P K₂ hP
  asIso (((μNatTrans (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology A))).app P).app K₂)

/-- For complexes of `A`-valued sheaves on the small étale site of `X`, a quasi-isomorphism
`α : P ⟶ Q` between K-flat complexes induces a quasi-isomorphism `F ⊗ P ⟶ F ⊗ Q` for every
complex `F`. -/
theorem quasiIso_whiskerLeft_of_kFlat
    {P Q : HomotopyCategory (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)}
    (α : P ⟶ Q) (hα : HomotopyCategory.quasiIso _ _ α)
    (hP : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P)
    (hQ : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat Q)
    (F : HomotopyCategory (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)) :
    HomotopyCategory.quasiIso _ _ (F ◁ α) := by
  have := IsGrothendieckAbelian.hasColimits (C := Sheaf X.smallEtaleTopology A)
  have : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology A) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have (Y : Sheaf X.smallEtaleTopology A) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj Y) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Y)
      (NatIso.ofComponents (fun Z ↦ β_ Y Z) (by intros; simp [curriedTensor]))
  exact MorphismProperty.whiskerLeft_of_kFlat _ α hα hP hQ F

/-- The derived tensor product is triangulated in each variable: for every `K ∈ D(X_ét)`, both
`M ↦ K ⊗ᴸ M` and `M ↦ M ⊗ᴸ K` are triangulated functors `D(X_ét) ⥤ D(X_ét)`. -/
theorem isTriangulated_derivedTensor (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj K).IsTriangulated ∧ ((derivedTensor A X).flip.obj K).IsTriangulated :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Etale
