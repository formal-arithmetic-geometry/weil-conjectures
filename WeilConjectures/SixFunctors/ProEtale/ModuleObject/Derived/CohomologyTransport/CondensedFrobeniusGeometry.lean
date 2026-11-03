/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed

/-! # The geometric Frobenius square

The coefficient-independent square is reused with distinct helper names from
CondensedGeometricFrobeniusTransport; its original declarations remain intact.
Source: latest blueprint, geometric-Frobenius transport square
(blueprint: lem-trf-condensed-frobenius-geometry-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- The semilinear square attached to geometric Frobenius on a finite-field fibre.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: lem-trf-condensed-frobenius-geometry-square). -/
def condensedFrobeniusGeometry (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    Geometry D.k := by
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let Y := (D.geometricFiber Y₀).left
  let aY : Y ⟶ Spec (.of D.k) := (D.geometricFiber Y₀).hom
  let γ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  let b : Spec (.of D.k) ≅ Spec (.of D.k) :=
    Scheme.Spec.mapIso γ.toRingEquiv.toCommRingCatIso.op
  let gY : Y ⟶ Y := (D.geometricFrobenius Y₀).hom
  have w : gY ≫ aY = aY ≫ b.hom := by
    dsimp [gY, aY, b, WeilConjectures.FiniteFieldDatum.geometricFrobenius,
      WeilConjectures.FiniteFieldDatum.galoisMap,
      WeilConjectures.FiniteFieldDatum.geometricFiber]
    exact (D.galoisMap_projections Y₀.hom γ).2
  letI : IsSeparated aY := by
    dsimp [aY, WeilConjectures.FiniteFieldDatum.geometricFiber]
    apply MorphismProperty.pullback_snd
    infer_instance
  letI : LocallyOfFiniteType aY := by
    dsimp [aY, WeilConjectures.FiniteFieldDatum.geometricFiber]
    apply MorphismProperty.pullback_snd
    infer_instance
  letI : QuasiCompact aY := by
    dsimp [aY, WeilConjectures.FiniteFieldDatum.geometricFiber]
    apply MorphismProperty.pullback_snd
    infer_instance
  exact
    { X := Y
      X' := Y
      a := aY
      a' := aY
      b := b
      h := ⟨gY, (D.geometricFrobenius Y₀).inv,
        (D.geometricFrobenius Y₀).hom_inv_id, (D.geometricFrobenius Y₀).inv_hom_id⟩
      comm := w
      separated := inferInstance
      finiteType := inferInstance
      quasiCompact := inferInstance
      separated' := inferInstance
      finiteType' := inferInstance
      quasiCompact' := inferInstance }


end AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
