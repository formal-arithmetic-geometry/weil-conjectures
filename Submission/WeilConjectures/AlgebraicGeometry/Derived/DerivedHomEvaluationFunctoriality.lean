/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Functoriality of local derived morphism evaluation

Source: Stacks Tags 09B1, 0946, 09BE and 0F63. Transpose the local comparison
identities under the two adjunctions, then cancel the bijective sheafification unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
  (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
private noncomputable abbrev originFunctor (X : Scheme.{u}) :=
  presheafToSheaf X.smallEtaleTopology (Type (u + 1)) ⋙ comparisonSetUpperStar X

private noncomputable abbrev originAdjunction (X : Scheme.{u}) :=
  (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).comp
    (proEtaleSiteComparison X)

private theorem hom_transpose (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    ((originAdjunction X).homEquiv _ _) (derivedHomSheafComparison X B A D) =
      derivedComparisonHomPresheafMap X B A D := by
  change ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _)
    (((proEtaleSiteComparison X).homEquiv _ _) (derivedHomSheafComparison X B A D)) = _
  rw [derivedHomSheafComparison, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem iso_transpose (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    ((originAdjunction X).homEquiv _ _) (derivedIsoSheafComparison X B A D) =
      derivedComparisonIsoPresheafMap X B A D := by
  change ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _)
    (((proEtaleSiteComparison X).homEquiv _ _) (derivedIsoSheafComparison X B A D)) = _
  rw [derivedIsoSheafComparison, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem iso_hom (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    derivedIsoSheafComparison X B A D ≫
        (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map
          (derivedLocalIsoToHomPresheaf (J := ProEt.topology X) (B := B)
            (A := (derivedComparison X B).obj A) (D := (derivedComparison X B).obj D)) =
      (originFunctor X).map
        (derivedLocalIsoToHomPresheaf (J := X.smallEtaleTopology) (B := B)
          (A := A) (D := D)) ≫ derivedHomSheafComparison X B A D := by
  apply ((originAdjunction X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    iso_transpose, hom_transpose]
  ext V f
  have hn := toSheafify_naturality (ProEt.topology X)
    (derivedLocalIsoToHomPresheaf (J := ProEt.topology X) (B := B)
      (A := (derivedComparison X B).obj A) (D := (derivedComparison X B).obj D))
  exact (ConcreteCategory.congr_hom (congr_app hn (op ((toProEt X).obj V.unop)))
    (derivedComparisonLocalIso X B A D V.unop f)).symm

end AlgebraicGeometry.Scheme
