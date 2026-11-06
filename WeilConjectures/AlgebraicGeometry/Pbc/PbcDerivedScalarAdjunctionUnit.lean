/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients

/-!
# The derived scalar adjunction on arbitrary complexes

Source: Stacks Tags 06YY and 0DVC
(blueprint: def-weil-pbc-bounded-constructible-tower).

The derived scalar extension/restriction adjunction is characterized by its unit formula
on K-flat complexes. Using K-flat resolutions and naturality, the formula holds for every
complex. When ordinary scalar extension is exact, the universal derived counit is
invertible at every complex.

## Main results

* `pbcModules_exists_kFlatResolution`: K-flat quasi-isomorphic resolutions.
* `pbcComplexCounit_naturality`: naturality of the cochain counit.
* `pbcDerivedScalarAdjunction_unit_app`: the unit formula for every complex.
* `pbcComplexCounit_isIso_of_preservesFiniteLimits`: the counit is invertible when
  scalar extension is exact.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)

/-- Every complex of module sheaves has a K-flat quasi-isomorphic resolution.
Source: Stacks Tag 06YF (blueprint: def-weil-pbc-bounded-constructible-tower). -/
theorem pbcModules_exists_kFlatResolution (P : CochainComplex (pbcModules X R) ℤ) :
    ∃ (K : CochainComplex (pbcModules X R) ℤ) (s : K ⟶ P),
      CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R) K ∧
        QuasiIso s := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨K, s, hK, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  exact ⟨K, s, hK, hs⟩

/-- The universal derived counit on cochain representatives is natural in chain maps.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-bounded-constructible-tower). -/
theorem pbcComplexCounit_naturality {K L : CochainComplex (pbcModules X R) ℤ} (a : K ⟶ L) :
    (pbcDerivedExtend φ).map (DerivedCategory.Q.map a) ≫ pbcComplexCounit φ L =
      pbcComplexCounit φ K ≫
        DerivedCategory.Q.map (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).map a) :=
  (Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (pbcDerivedExtend φ) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) (pbcExtensionCounit φ) ≫
    Functor.whiskerRight ((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft ((pbcExtend φ).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom).naturality a

/-- The unit of the derived scalar adjunction is the localized ordinary unit on every
complex, not only on K-flat complexes.
Source: Stacks Tags 06YY and 0DVC (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: choose a K-flat resolution s : K → P. Both sides are natural in P, they agree on K
by the defining property of the derived adjunction, and Q(s) is invertible. -/
theorem pbcDerivedScalarAdjunction_unit_app (P : CochainComplex (pbcModules X R) ℤ) :
    (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P) := by
  obtain ⟨K, s, hK, hs⟩ := pbcModules_exists_kFlatResolution P
  have hKu : (pbcDerivedScalarAdjunction φ).unit.app (DerivedCategory.Q.obj K) ≫
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ K) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app K) :=
    (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec K hK
  rw [← cancel_epi (DerivedCategory.Q.map s)]
  have hu := (pbcDerivedScalarAdjunction φ).unit.naturality (DerivedCategory.Q.map s)
  have hc := congrArg (pbcDerivedRestrict φ).map (pbcComplexCounit_naturality φ s)
  have hf := (pbcRestrict φ).mapDerivedCategoryFactors_hom_naturality
    (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).map s)
  have hη := (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).naturality s
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hu hη
  rw [Functor.map_comp, Functor.map_comp] at hc
  rw [reassoc_of% hu, reassoc_of% hc]
  erw [hf, reassoc_of% hKu]
  rw [← Functor.map_comp, ← Functor.map_comp]
  erw [hη]
  rfl

/-- If ordinary scalar extension is exact, then the universal derived counit is invertible
at every complex.
Source: Stacks Tags 06YY and 06YF (blueprint: def-weil-pbc-bounded-constructible-tower).
Proof: choose a K-flat resolution s : K → P. The counit is invertible at K, and it is
natural in s. Derived extension inverts Q(s), and exact extension preserves the
quasi-isomorphism s. -/
theorem pbcComplexCounit_isIso_of_preservesFiniteLimits [PreservesFiniteLimits (pbcExtend φ)]
    (P : CochainComplex (pbcModules X R) ℤ) :
    IsIso (pbcComplexCounit φ P) := by
  obtain ⟨K, s, hK, hs⟩ := pbcModules_exists_kFlatResolution P
  have : IsIso (pbcComplexCounit φ K) := by
    have := pbcExtensionCounit_isIso φ K hK
    unfold pbcComplexCounit
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} (pbcExtend φ) :=
    (pbcScalarAdjunction φ).leftAdjoint_preservesColimits
  have : IsIso ((pbcDerivedExtend φ).map (DerivedCategory.Q.map s) ≫ pbcComplexCounit φ P) := by
    rw [pbcComplexCounit_naturality φ s]
    infer_instance
  exact IsIso.of_isIso_comp_left ((pbcDerivedExtend φ).map (DerivedCategory.Q.map s)) _

end AlgebraicGeometry.Scheme
