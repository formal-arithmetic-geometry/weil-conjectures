/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius

/-! # Geometric fibre finite subargument

Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-l2-growth/
lem-wf-l2-upper.proof.md, opening sentence.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Endofunctor
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The constructible heart has exact finite-dimensional geometric fibres, with unit coordinates.
Source: latest blueprint lem-wf-l2-upper.proof.md, opening sentence
(blueprint: lem-wf-condensed-fibres-point-finiteness).

Proof: Cartesian coefficient pullback is exact and additive. The constructible-heart
inclusion preserves finite limits and colimits. Evaluation at Spec(k) is exact since
its pro-etale covers split. Factor z through the unique stratum containing its image.
Pull the stratum's finite constant local model through a splitting of its point cover.
The resulting finite presentation over the coefficient field is finite dimensional.
The regular-module pullback comparison and constant-section evaluation identify its
unit fibre with the lifted coefficient field. These identifications include the zero
module and require no nonzero-rank assumption. -/
theorem condensed_fibres_point_finiteness
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    fibreFunctorAssertions
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber Y₀).left)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k)
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l)
        (D.geometricFiber Y₀).left)) := by
  sorry

end WeilConjectures
