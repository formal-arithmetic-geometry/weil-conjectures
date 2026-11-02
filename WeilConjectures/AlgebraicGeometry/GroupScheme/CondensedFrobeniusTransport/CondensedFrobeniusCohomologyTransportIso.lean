/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-! # Canonical Frobenius transport with condensed coefficients

Source: latest blueprint, `def-weil-global-geometric-frobenius`, first arrow in each
cohomology display, and `lem-trf-frobenius-operator-compact-description`.
(blueprint: lem-weil-frobenius-cohomology-transport-iso)

All categories are the ordinary unbounded derived categories of modules over the actual
pulled-back condensed ring. The compactification is the base change of the chosen model.
The exchange maps are the published adjunction mates, and the point insertion uses the
canonical coefficient comparison, rather than a chosen isomorphism of vector spaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedFrobeniusTransport

attribute [local instance] IsAlgClosure.isAlgClosed

variable (D : FiniteFieldDatum.{u})

/-- Spec of geometric field Frobenius, with the inverse Spec of arithmetic Frobenius.
Source: latest blueprint `def-weil-frobenius-detailed`.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def pointFrobenius : Spec (.of D.k) ≅ Spec (.of D.k) :=
  letI := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]

/-- The specified compactification, obtained by base change from k₀ to k.
Source: latest blueprint, the compact-support composite.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
abbrev compactification (c₀ : Compactification Y₀.hom) :
    Compactification (D.geometricFiber Y₀).hom :=
  c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Frobenius on the middle scheme of this very compactification.
Source: latest blueprint, compact-support exchange square.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def middleFrobenius (c₀ : Compactification Y₀.hom) :
    (compactification D Y₀ c₀).Z ≅ (compactification D Y₀ c₀).Z :=
  letI := Fintype.ofFinite D.k₀
  { hom := D.galoisMap c₀.g
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
    inv := D.galoisMap c₀.g
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
    hom_inv_id := (D.galoisMap_inverse c₀.g _).1
    inv_hom_id := (D.galoisMap_inverse c₀.g _).2 }

/-- The three squares used in the specified exchanges commute.
Source: latest blueprint, first arrows of `def-weil-global-geometric-frobenius`.
(blueprint: lem-weil-frobenius-cohomology-transport-iso)
Proof: each Frobenius fixes the model projection and acts by Spec γ on the field
projection. The proper square follows directly from the second projection formula.
For the open square both composites have first projection j₀ after the model projection
and second projection Spec γ after the field projection; pullback uniqueness identifies
them. The structure square is the same second projection formula for Y₀. -/
theorem squares (c₀ : Compactification Y₀.hom) :
    CommSq (D.geometricFrobenius Y₀).hom (D.geometricFiber Y₀).hom
      (D.geometricFiber Y₀).hom (pointFrobenius D).hom ∧
    CommSq (middleFrobenius D Y₀ c₀).hom (compactification D Y₀ c₀).g
      (compactification D Y₀ c₀).g (pointFrobenius D).hom ∧
    CommSq (D.geometricFrobenius Y₀).hom (compactification D Y₀ c₀).i
      (compactification D Y₀ c₀).i (middleFrobenius D Y₀ c₀).hom := by
  sorry

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- Exact point evaluation with restriction along the recorded scalar-section map,
derived on the ordinary module categories. Its scalar ring ΓΛ is canonically Λ(*).
Source: latest blueprint, `def-weil-ordinary-compact-cohomology`.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
abbrev pointSections := (condensedRingCoefficientSections Λ.X (Spec (.of D.k))).rightDerivedFunctor

/-- Restriction N(s,1) → N(s,g_s) with the canonical coefficient identification.
The point-pullback equivalence and its composition comparison normalize this map:
`upperStarIsoIdOfIsSepClosed` is the inverse restriction. Exact pullback identifies
its derived functor with termwise pullback; whiskering gives the map on point sections.
Source: latest blueprint, the first arrow before the Weil structure is applied.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def insertion : pointSections D Λ ≅
    moduleObjectDerivedPullback Λ.X (pointFrobenius D).hom ⋙ pointSections D Λ :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X (pointFrobenius D).hom ≪≫
      Functor.mapDerivedCategoryNatIso
        (upperStarIsoIdOfIsSepClosed Λ.X (pointFrobenius D).hom) ≪≫
      Functor.mapDerivedCategoryIdIso _).symm) _

/-- The canonical ordinary adjunction mate, with no supplied comparison map.
Source: latest blueprint, the ordinary cohomology transport composite.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def ordinaryExchange (c₀ : Compactification Y₀.hom) :=
  FrobeniusSquareExchange.direct Λ (D.geometricFiber Y₀).hom
    (squares D Y₀ c₀).1

/-- Natural ordinary transport Γ_s(e_*) after insertion along g_s.
Source: latest blueprint, first arrow in the ordinary display.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def ordinaryTransport (c₀ : Compactification Y₀.hom) :
    condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom ⟶
      moduleObjectDerivedPullback Λ.X (D.geometricFrobenius Y₀).hom ⋙
        condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom :=
  Functor.whiskerLeft (moduleObjectDerivedPushforward Λ.X (D.geometricFiber Y₀).hom)
      (insertion D Λ).hom ≫
    Functor.whiskerRight (ordinaryExchange D Y₀ Λ c₀) (pointSections D Λ)

/-- Natural compact transport Γ_s(e_!) after insertion along g_s, for the fixed c.
Source: latest blueprint, first arrow in the compact-support display.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def compactTransport (c₀ : Compactification Y₀.hom) :
    condensedRingCompactCoefficientComplex Λ.X (compactification D Y₀ c₀) ⟶
      moduleObjectDerivedPullback Λ.X (D.geometricFrobenius Y₀).hom ⋙
        condensedRingCompactCoefficientComplex Λ.X (compactification D Y₀ c₀) :=
  Functor.whiskerLeft
      (rightDerivedLowerShriekOfCompactification Λ.X (compactification D Y₀ c₀))
      (insertion D Λ).hom ≫
    Functor.whiskerRight (compactExchange D Y₀ Λ c₀) (pointSections D Λ)

end WeilConjectures.CondensedFrobeniusTransport
