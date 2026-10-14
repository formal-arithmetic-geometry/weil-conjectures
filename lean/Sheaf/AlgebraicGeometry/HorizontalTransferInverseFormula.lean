/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.HorizontalDualityMateComparisons
public import Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate

/-! # Canonical isomorphism transfer from its inverse formula

Source: Stacks Project, Tags 0D5S, 0D5T and 08HY.
(blueprint: lem-sc-horizontal-transfer-inverse-formula).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

/-- Identify the equivalence-unit transfer by its adjunction-unit inverse formula.
Source: Stacks Project, Tags 0D5S, 0D5T and 08HY.
(blueprint: lem-sc-horizontal-transfer-inverse-formula)

Proof: Substitute k = k₀. Write L for pullback along e.hom, Rq for direct
image along q, η for the pinned adjunction unit, U for ev.unitIso, and δ for
the restricted conjugate d (including transport along hp). The fully faithful
QCoh inclusions map the restricted adjunction units and counits to the ambient
ones. Expanding conjugation into units and counits therefore shows that δ is
exactly the transport from R(p) to R(e.hom) followed by Rq used in li.
Consequently the constructed transfer component at D is
δ.hom at L(D), followed by Rq applied to ri.hom at L(D), then Rq applied to
U.inv at D. The supplied inverse component of j is Rq applied to η at D,
followed by δ.inv at L(D). Compose j.inv with the constructed transfer:
δ.inv and δ.hom cancel. By unit_rightAdjointUniq_hom_app, η at D followed
by ri.hom at L(D) equals U.hom at D. Functoriality of Rq and cancellation
of U.hom with U.inv make the composite the identity. The ambient computation
reflects through the faithful QCoh inclusion. Precompose with j.hom and cancel
j.hom followed by j.inv, obtaining k.app D = j.hom.app D.
The argument uses only functorial and adjunction identities and applies also to
identity arrows, empty schemes and zero objects. No base-change map is used. -/
theorem horizontal_transfer_eq_of_inverse_formula
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P Q Z : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (e : P ≅ Q) (q : Q ⟶ Z) (p : P ⟶ Z)
    [QuasiCompact q] [QuasiSeparated q] [QuasiCompact p] [QuasiSeparated p]
    (hp : e.hom ≫ q = p) :
    let ev := horizontalMateEquivalence e
    let ri := (horizontalMateAdjunction e.hom).rightAdjointUniq ev.toAdjunction
    let li := eqToIso (congrArg qcDirectImage hp.symm) ≪≫
      horizontalMatePushComp e.hom q ≪≫
      Functor.isoWhiskerRight ri (horizontalMatePushforward q)
    let k₀ : TwoSquare (horizontalMatePullback e.hom) (horizontalMatePushforward q)
        (horizontalMatePushforward p) (𝟭 (schemeDerivedQCohCategory Z)) :=
      .mk _ _ _ _ <|
        (Functor.isoWhiskerLeft (horizontalMatePullback e.hom) li).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight ev.unitIso.inv (horizontalMatePushforward q) ≫
          (Functor.leftUnitor (horizontalMatePushforward q)).hom ≫
          (Functor.rightUnitor (horizontalMatePushforward q)).inv
    let a := fun {A B : Scheme.{u}} (r : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction r
        (hAdd := (Classical.choose exists_derivedPullbackComposition) r)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) r)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) r))
    let d := conjugateIsoEquiv (a p) ((a q).comp (a e.hom))
      (horizontalMateAmbientComp e.hom q ≪≫
        eqToIso (congrArg (fun r ↦ derivedPullback.{u, w} r) hp))
    ∀ (k : TwoSquare (horizontalMatePullback e.hom) (horizontalMatePushforward q)
        (horizontalMatePushforward p) (𝟭 (schemeDerivedQCohCategory Z))), k = k₀ →
    ∀ (j : qcPullback e.hom ⋙ qcDirectImage p ≅ qcDirectImage q),
      (∀ D : schemeDerivedQCohCategory Q,
        (schemeDerivedQCohProperty Z).ι.map (j.inv.app D) =
          (schemeDerivedDirectImage q).map ((a e.hom).unit.app D.obj) ≫
            d.inv.app ((derivedPullback e.hom).obj D.obj)) →
      ∀ D : schemeDerivedQCohCategory Q, k.app D = j.hom.app D := by sorry

end AlgebraicGeometry
