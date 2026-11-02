/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison

/-! Faithful cancellation of the site comparison in the ordinary antecedent.
(blueprint: new-lem-pur-coordinate-ordinary-boundary-antecedent-faithful-transport).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- Equality after the site comparison and its shift comparison descends to the
ordinary etale equality.

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md, the
transport of compositions and counits to finite etale-origin objects; Bhatt-Scholze,
Proposition 5.2.6 (full faithfulness of the comparison on bounded-below objects)
(blueprint: new-lem-pur-coordinate-ordinary-boundary-antecedent-faithful-transport).

Proof: the shift comparison of `nu` is an isomorphism, hence a monomorphism; cancelling
it leaves equality of the `nu`-images of the two maps
`i_* Λ[0] ⟶ (gysinEtaleInput)[2]`. Both objects are bounded below (degree `0`, and
`n - 2` for an input bounded below at `n`). On bounded-below objects the comparison
inverse image is fully faithful (sk-prop-sf-comparison, `boundedBelowComparison`),
so the two maps agree. -/
theorem coordinateOrdinary_boundaryAntecedent_faithfulTransport
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (c : Ext ((Etale.lowerStar (Modules P) (zeroSection T)).obj (P.constantEtale T))
      (P.twistEtale h (Line T)) 2)
    (b : (DerivedCategory.singleFunctor (EtSheaves P T) 0).obj
      (P.constantEtale T) ⟶ P.boundaryEtaleValue h T)
    (hb :
      (nu P (Line T)).map
          (((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor
            0).inv.app (P.constantEtale T) ≫
            (Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map b ≫
            P.boundaryEtaleCounit h T) ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app
          (P.gysinEtaleInput h T).obj =
      (nu P (Line T)).map c.hom ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app
          (P.gysinEtaleInput h T).obj) :
    ((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor
      0).inv.app (P.constantEtale T) ≫
      (Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map b ≫
      P.boundaryEtaleCounit h T = c.hom := by
  have hmap := (cancel_mono _).1 hb
  obtain ⟨-, ⟨hf⟩, -⟩ := boundedBelowComparison (Line T) P.Coefficient
  let K : DerivedCategory.Plus (EtSheaves P (Line T)) :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj
      ((Etale.lowerStar (Modules P) (zeroSection T)).obj (P.constantEtale T)), 0, inferInstance⟩
  obtain ⟨n, hn⟩ := (P.gysinEtaleInput h T).property
  let M : DerivedCategory.Plus (EtSheaves P (Line T)) :=
    ⟨(P.gysinEtaleInput h T).obj⟦(2 : ℤ)⟧, n - 2,
      DerivedCategory.TStructure.t.isGE_shift _ n 2 (n - 2) (by omega)⟩
  have hinj :=
    ((hf.comp (ObjectProperty.fullyFaithfulι _)).homEquiv (X := K) (Y := M)).injective
  have h0 := ((ObjectProperty.fullyFaithfulι
      ((DerivedCategory.TStructure.t (C := EtSheaves P (Line T))).plus)).homEquiv
        (X := K) (Y := M)).surjective
  obtain ⟨x, hx⟩ := h0
    (((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor
      0).inv.app (P.constantEtale T) ≫
      (Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map b ≫
      P.boundaryEtaleCounit h T)
  obtain ⟨y, hy⟩ := h0 c.hom
  have hxy : x = y := hinj (by
    change (nu P (Line T)).map ((ObjectProperty.fullyFaithfulι _).homEquiv x) =
      (nu P (Line T)).map ((ObjectProperty.fullyFaithfulι _).homEquiv y)
    rw [hx, hy]
    exact hmap)
  rw [← hx, ← hy, hxy]

end WeilConjectures.PurityFiniteSetting
