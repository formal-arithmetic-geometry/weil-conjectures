/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleDerivedQuotientInterchange
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOpenProjectionFaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleProperProjectionFaces

/-!
# Compact-support projection from strict étale transports

Source: Zheng, Construction 5.15 and Lemma 5.22
(blueprint: lem-pur-strict-etale-isomorphic-stage-projection).

This is the geometric mate assembly after exact coefficient transports have been
constructed.  It leaves coefficient transport construction to a separate node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- Assemble normalized compact-support and quotient projection data from exact
finite-level transports.

Proof: tensor-unit normalization gives the inverse-image coefficient squares;
transposing them along the recorded open and proper adjunctions gives the mate
fields of the compact-support transport.  The quotient tensor interchange has
the same composite ring map on both sides, so its normalized derived square is
canonical.  Whiskering the open and proper faces and using associativity yields
the evaluation and quotient cubes in `StrictEtaleTransportProjection`.
Source: Zheng, Construction 5.15 and Lemma 5.22
(blueprint: lem-pur-strict-etale-projection-from-equivalences).
-/
theorem nonempty_strictEtaleTransportProjection_of_equivalences
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (_hTX : ∀ n, (TX.level n).derived.IsEquivalence)
    (_hTY : ∀ n, (TY.level n).derived.IsEquivalence)
    (_hTZ : ∀ n, (TZ.level n).derived.IsEquivalence) :
    Nonempty (StrictEtaleTransportProjection a c SA SB TX TY TZ) := by
  obtain ⟨qX⟩ := nonempty_strictEtaleTransportQuotient TX
  obtain ⟨qY⟩ := nonempty_strictEtaleTransportQuotient TY
  obtain ⟨qZ⟩ := nonempty_strictEtaleTransportQuotient TZ
  obtain ⟨os, op, ol, hom, hoe, hoc⟩ :=
    nonempty_strictEtaleOpenProjectionFaces a c SA SB TX TZ _hTX _hTZ qX qZ
  obtain ⟨ps, pp, pl, hpm, hpe, hpc⟩ :=
    nonempty_strictEtaleProperProjectionFaces a c SA SB TZ TY _hTZ _hTY qZ qY
  let compact : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ :=
    ⟨{ openSquare := os
       properSquare := ps
       openComparison := op.symm
       properComparison := pp }, hom, hpm⟩
  let level n : SA.levelFunctor (index n) ⋙ (TY.level n).derived ≅
      (TX.level n).derived ⋙ SB.levelFunctor n :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (pl n) ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (ol n) _ ≪≫
        Functor.associator _ _ _
  refine ⟨{
    compact := compact
    level := level
    quotientX := qX
    quotientY := qY
    evaluation := ?_
    quotient_cube := ?_ }⟩
  · intro n K
    have hp := hpe n (SA.derivedOpen.obj K)
    have ho := congrArg (SB.properDerived.level n).direct.map (hoe n K)
    have np := (pl n).hom.naturality
      ((SA.openDerivedEvaluation (index n)).hom.app K)
    have ne := (SB.properDerived.directEvaluation n).hom.naturality (op.hom.app K)
    simp only [Functor.comp_map, Functor.map_comp] at hp ho np ne
    have np' :
        (TY.level n).derived.map ((SA.properDerived.level (index n)).direct.map
          ((SA.openDerivedEvaluation (index n)).hom.app K)) ≫
          (pl n).hom.app ((SA.levelDerivedOpen (index n)).obj
            ((SA.PX.evaluation (index n)).obj K)) =
        (pl n).hom.app ((SA.PZ.evaluation (index n)).obj (SA.derivedOpen.obj K)) ≫
          (SB.properDerived.level n).direct.map
            ((TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K)) := by
      simpa only [Functor.comp_obj] using np
    have hcalc :
        (TY.derivedEvaluation n).hom.app
            (SA.properDerived.system.direct.obj (SA.derivedOpen.obj K)) ≫
          (TY.level n).derived.map
            ((SA.properDerived.directEvaluation (index n)).hom.app
              (SA.derivedOpen.obj K)) ≫
          (TY.level n).derived.map ((SA.properDerived.level (index n)).direct.map
            ((SA.openDerivedEvaluation (index n)).hom.app K)) ≫
          (pl n).hom.app ((SA.levelDerivedOpen (index n)).obj
            ((SA.PX.evaluation (index n)).obj K)) ≫
          (SB.properDerived.level n).direct.map
            ((ol n).hom.app ((SA.PX.evaluation (index n)).obj K)) =
        (SB.PY.evaluation n).map (pp.hom.app (SA.derivedOpen.obj K)) ≫
          (SB.PY.evaluation n).map (SB.properDerived.system.direct.map (op.hom.app K)) ≫
          (SB.properDerived.directEvaluation n).hom.app
            (SB.derivedOpen.obj (TX.derived.obj K)) ≫
          (SB.properDerived.level n).direct.map
            ((SB.openDerivedEvaluation n).hom.app (TX.derived.obj K)) ≫
          (SB.properDerived.level n).direct.map
            ((SB.levelDerivedOpen n).map ((TX.derivedEvaluation n).hom.app K)) := by
      rw [reassoc_of% np', reassoc_of% hp, ho]
      rw [reassoc_of% ne]
    simpa only [compact, level, StrictEtaleCompactSupport.functor,
      StrictEtaleCompactSupport.levelFunctor, StrictEtaleCompactSupport.evaluation,
      StrictEtaleCompactSupportTransport.projection,
      StrictEtaleCompactSupportTransport.openComparison,
      StrictEtaleCompactSupportTransport.properComparison,
      Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Functor.comp_obj, Functor.comp_map,
      Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc] using hcalc
  · intro QA QB m n h K
    have ho := congrArg (SB.properDerived.level n).direct.map (hoc QA QB h K)
    have hp := hpc QA QB h ((SA.levelDerivedOpen (index m)).obj K)
    have nb := (QB.proper h).hom.naturality ((ol m).inv.app K)
    have na := (pl n).inv.naturality
      ((QA.openProjection (index.monotone h)).hom.app K)
    simp only [Functor.comp_map, Functor.map_comp] at ho hp nb na
    have hcalc :
        (SB.properDerived.level n).direct.map
            ((SB.levelDerivedOpen n).map ((qX.derived h).hom.app K)) ≫
          (SB.properDerived.level n).direct.map
            ((QB.openProjection h).hom.app ((TX.level m).derived.obj K)) ≫
          (QB.proper h).hom.app
            ((SB.levelDerivedOpen m).obj ((TX.level m).derived.obj K)) ≫
          (SB.PY.scalar h).derived.map ((SB.properDerived.level m).direct.map
            ((ol m).inv.app K)) ≫
          (SB.PY.scalar h).derived.map
            ((pl m).inv.app ((SA.levelDerivedOpen (index m)).obj K)) =
        (SB.properDerived.level n).direct.map
            ((ol n).inv.app ((SA.PX.scalar (index.monotone h)).derived.obj K)) ≫
          (pl n).inv.app ((SA.levelDerivedOpen (index n)).obj
            ((SA.PX.scalar (index.monotone h)).derived.obj K)) ≫
          (TY.level n).derived.map ((SA.properDerived.level (index n)).direct.map
            ((QA.openProjection (index.monotone h)).hom.app K)) ≫
          (TY.level n).derived.map
            ((QA.proper (index.monotone h)).hom.app
              ((SA.levelDerivedOpen (index m)).obj K)) ≫
          (qY.derived h).hom.app
            ((SA.properDerived.level (index m)).direct.obj
              ((SA.levelDerivedOpen (index m)).obj K)) := by
      rw [← reassoc_of% nb, reassoc_of% ho, hp, reassoc_of% na]
    simpa only [level, StrictEtaleCompactSupport.levelFunctor,
      StrictEtaleQuotientProjection.projection, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, isoWhiskerLeft_inv, isoWhiskerRight_inv,
      whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
      Functor.comp_obj, Functor.comp_map, Functor.map_comp,
      Category.id_comp, Category.comp_id, Category.assoc] using hcalc

end AlgebraicGeometry
