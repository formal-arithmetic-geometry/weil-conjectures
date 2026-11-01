/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.EtaleTateSheafPow

/-!
# The identification `Λ_X(1) ≅ (tateSheafPow Λ X 1)[0]` in degree one

`Etale.tateObjectNatIsoSingleFunctor_one_hom`: the identification
`Λ_X(1) ≅ (tateSheafPow Λ X 1)[0]` (`Etale.tateObjectNatIsoSingleFunctor`) is
`Λ_X(1) ≅ (μ_n ⊗ Λ)[0]` (`Etale.tateTwistObjectOneIso`) followed by the identification of the
sheaves `μ_n ⊗ Λ ≅ tateTwistSheaf Λ X 1 ≅ tateSheafPow Λ X 1`.

The proof is one application of the generic `CategoryTheory.Iso.trans_mapIso_hom_eq`: rewriting
on these terms is expensive for the kernel.
-/

@[expose] public section

universe u

open CategoryTheory

/-- For `i : T ≅ F.obj P` and isomorphisms `N : P ≅ Q`, `O : P ≅ R`, the composite
`i ≪≫ F.mapIso N` factors through `i ≪≫ F.mapIso O`. -/
lemma CategoryTheory.Iso.trans_mapIso_hom_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {T : D} {P Q R : C} (i : T ≅ F.obj P) (N : P ≅ Q) (O : P ≅ R) :
    (i ≪≫ F.mapIso N).hom = (i ≪≫ F.mapIso O).hom ≫ F.map (O.inv ≫ N.hom) := by
  simp [← Functor.map_comp]

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) [HasInvertibleExponent Λ X]
  [NeZero (ringChar Λ)]

/-- In degree one, `Λ_X(1) ≅ (tateSheafPow Λ X 1)[0]` is `Λ_X(1) ≅ (μ_n ⊗ Λ)[0]`
(`tateTwistObjectOneIso`) followed by `μ_n ⊗ Λ ≅ tateTwistSheaf Λ X 1 ≅ tateSheafPow Λ X 1`. -/
lemma tateObjectNatIsoSingleFunctor_one_hom :
    (tateObjectNatIsoSingleFunctor Λ X 1).hom =
      (tateTwistObjectOneIso X Λ).hom ≫ (DerivedCategory.singleFunctor _ 0).map
        ((tateTwistSheafOneIso X Λ).inv ≫ (tateTwistSheafNatIso Λ X 1).hom) :=
  Iso.trans_mapIso_hom_eq _ (tateTwistObjectIsoSingleFunctor Λ X 1) _ _

end AlgebraicGeometry.Etale
