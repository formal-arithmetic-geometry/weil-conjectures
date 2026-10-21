/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.ResidueField

/-! # Existence of the local strict-henselization map

Source: Stacks Project, Tags 03PS, 03Q9 and 04GU
(blueprint: lem-weil-pbc-strict-henselization-map-exists).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

namespace Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Extend the affine limit cone and its marked-point equations along the initial inclusion.
The affine-to-full cone transport follows the private construction in
`Sheaf.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality`; the last clause records
that every chosen refinement arrow is pointed. -/
private theorem fullPointedStrictHenselizationCone
    {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (p : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme s)
    (hp : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
      p ≫ (Scheme.strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) ≫
        (Spec (Opposite.unop ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left) :
    let D := CategoryOfElements.π (pointSmallEtale s).fiber ⋙
      Etale.forget S ⋙ Over.forget S
    ∃ π : (Functor.const _).obj (strictHenselizationScheme s) ⟶ D,
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      (∀ j, π.app j ≫ j.1.hom = strictHenselizationStructuralMap s) ∧
      ∀ j, p ≫ π.app j = j.2.left := by
  classical
  let N := (equivSmallModel.{v} (strictHenselizationNeighbourhoods s)).inverse
  let Q := N ⋙ Functor.Elements.precomp (AffineEtale.Spec S) (pointSmallEtale s).fiber
  let D := CategoryOfElements.π (pointSmallEtale s).fiber ⋙
    Etale.forget S ⋙ Over.forget S
  have : Q.Initial := (strictHenselization_properties s).1
  let A := Q ⋙ D
  have hAff (j : SmallModel.{v} (strictHenselizationNeighbourhoods s)) :
      IsAffine (A.obj j) := by
    change IsAffine (Spec _)
    infer_instance
  let _ : ∀ j, IsAffine (A.obj j) := hAff
  let E := (opOpEquivalence
    (SmallModel.{v} (strictHenselizationNeighbourhoods s))).symm
  let cR := (strictHenselizationCone s).whisker E.functor
  let α : A ⟶ E.functor ⋙ (strictHenselizationAffineDiagram s).op ⋙ Scheme.Spec :=
    Functor.whiskerLeft A ΓSpec.adjunction.unit
  have hIso (j : SmallModel.{v} (strictHenselizationNeighbourhoods s)) :
      IsIso (α.app j) := by
    let : IsAffine (A.obj j) := hAff j
    exact inferInstanceAs (IsIso (ΓSpec.adjunction.unit.app (A.obj j)))
  let : IsIso α := NatIso.isIso_of_isIso_app α
  let e := asIso α
  let c := (Cone.postcompose e.inv).obj cR
  have hc : IsLimit c :=
    (IsLimit.postcomposeInvEquiv e _).symm
      ((strictHenselization_properties s).2.2.some.whiskerEquivalence E)
  have hleg (j : SmallModel.{v} (strictHenselizationNeighbourhoods s)) :
      c.π.app j = (strictHenselizationCone s).π.app
        (Opposite.op (Opposite.op j)) ≫ Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv := by
    dsimp [c, cR]
    change _ ≫ (inv α).app j = _
    rw [NatIso.isIso_inv_app]
    change _ ≫ inv (A.obj j).toSpecΓ = _
    congr 1
    change (Spec _).isoSpec.inv = _
    exact isoSpec_Spec_inv _
  have hq (j : SmallModel.{v} (strictHenselizationNeighbourhoods s)) :
      c.π.app j ≫ (Q.obj j).1.hom = strictHenselizationStructuralMap s := by
    rw [hleg]
    exact ((exists_strictHenselizationStructuralMap s).choose_spec j)
  let c' := (Functor.Initial.extendCone (F := Q) (G := D)).obj c
  have hpoint (j : SmallModel.{v} (strictHenselizationNeighbourhoods s)) :
      p ≫ c.π.app j = (N.obj j).2.left := by
    rw [hleg]
    simpa only [Scheme.isoSpec_Spec_inv] using hp j
  refine ⟨c'.π, ⟨(Functor.Initial.isLimitExtendConeEquiv Q c).symm hc⟩, ?_, ?_⟩
  · intro j
    change (c.π.app (Functor.Initial.lift Q j) ≫
      D.map (Functor.Initial.homToLift Q j)) ≫ j.1.hom = _
    rw [Category.assoc]
    change c.π.app (Functor.Initial.lift Q j) ≫
      (Functor.Initial.homToLift Q j).1.left ≫ j.1.hom = _
    rw [MorphismProperty.Over.w]
    exact hq _
  · intro j
    change p ≫ (c.π.app (Functor.Initial.lift Q j) ≫
      D.map (Functor.Initial.homToLift Q j)) = _
    rw [← Category.assoc, hpoint]
    have h := (Functor.Initial.homToLift Q j).2
    exact congrArg (fun x ↦ x.left) h

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on pointed neighbourhoods, with its canonical pullback-lift point. -/
private noncomputable def pointedPullback
    {S T : Scheme.{v}} {g : T ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (hst : s = t ≫ g) :
    (pointSmallEtale s).fiber.Elements ⥤ (pointSmallEtale t).fiber.Elements := by
  let F := MorphismProperty.Over.pullback @Etale ⊤ g
  let α : (pointSmallEtale s).fiber ⟶ F ⋙ (pointSmallEtale t).fiber :=
    { app := fun j ↦ ↾(fun v : (pointSmallEtale s).fiber.obj j ↦ Over.homMk
        (pullback.lift v.left t (by exact (Over.w v).trans hst))
        (by simp [F, MorphismProperty.Over.pullback]))
      naturality := by
        intro j k a
        apply ConcreteCategory.ext
        apply TypeCat.Fun.ext
        funext v
        apply Over.OverMorphism.ext
        change pullback.lift (v.left ≫ a.left) t _ =
          pullback.lift v.left t _ ≫ pullback.lift
            (pullback.fst j.hom g ≫ a.left) (pullback.snd j.hom g) _
        apply pullback.hom_ext <;> simp [Category.assoc] }
  exact α.mapElements ⋙ Functor.Elements.precomp F (pointSmallEtale t).fiber

end Scheme

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Existence of a local map over the base with the prescribed pointed residue map.
Source: Stacks Project, paragraph after Tag 03PS, Tags 03Q9 and 04GU
(blueprint: lem-weil-pbc-strict-henselization-map-exists).

Proof: Transport the canonical limit cones through the affine spectrum
identifications and extend them to all pointed etale neighbourhoods along the
initial affine-neighbourhood inclusion. The supplied factorizations persist:
each extended leg is an affine leg followed by a pointed refinement morphism.
Pullback along g sends a pointed S-neighbourhood to a pointed T-neighbourhood;
the point of the pullback is the pullback lift of its marked point and barT.
Compose the T-cone's legs at these pullbacks with their first projections.
Pullback functoriality and cone naturality make these maps a cone on the full
S-neighbourhood diagram. Its limit gives f from the T strict henselization to
the S strict henselization. The pullback square and the structural equations
of the extended cones prove the required base square. Limit extensionality,
the pointed equations of those cones, and pullback.lift_fst prove that the
Omega-point of T followed by f equals the Omega-point of S. Full faithfulness
of Spec now gives the ring map h and the required equality into Omega. That
equality identifies the composite of h with the T residue embedding with the
S residue embedding, which is local; isLocalHom_of_comp therefore makes h local.
This is the inverse-limit construction of Tag 03Q9 and functoriality of Tag 04GU.
The extra hypotheses hOmegaS and hOmegaT are unused because the pointed
factorizations are supplied; the signature is retained unchanged.
-/
theorem strictHenselizationMapExists
    {S T : Scheme.{v}} (g : T ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barT : Spec (.of Ω) ⟶ T) (barS : Spec (.of Ω) ⟶ S)
    (hbar : barS = barT ≫ g)
    [Algebra (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω]
    [Algebra (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω]
    (hΩS : algebraMap (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barS)).hom)
    (hΩT : algebraMap (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barT)).hom)
    [IsLocalRing (Scheme.strictHenselizationRing barS)]
    [IsLocalRing (Scheme.strictHenselizationRing barT)]
    (σS : IsLocalRing.ResidueField (Scheme.strictHenselizationRing barS) ≃+*
      separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)
    (σT : IsLocalRing.ResidueField (Scheme.strictHenselizationRing barT) ≃+*
      separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)
    (hσS : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σS.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselizationRing barS)))) ≫
          (Scheme.strictHenselizationCone barS).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).2.left)
    (hσT : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σT.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselizationRing barT)))) ≫
          (Scheme.strictHenselizationCone barT).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).2.left) :
    ∃ h : Scheme.strictHenselizationRing barS ⟶ Scheme.strictHenselizationRing barT,
      IsLocalHom h.hom ∧
      Spec.map h ≫ Scheme.strictHenselizationStructuralMap barS =
        Scheme.strictHenselizationStructuralMap barT ≫ g ∧
      (((IntermediateField.val
          (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σS.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselizationRing barS))) =
        ((((IntermediateField.val
          (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σT.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselizationRing barT)))).comp h.hom := by
  classical
  let ψS := (((IntermediateField.val
    (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σS.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing barS)))
  let ψT := (((IntermediateField.val
    (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σT.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing barT)))
  let pS := Spec.map (CommRingCat.ofHom ψS)
  let pT := Spec.map (CommRingCat.ofHom ψT)
  obtain ⟨πs, ⟨hs⟩, hqs, hps⟩ :=
    Scheme.fullPointedStrictHenselizationCone barS pS hσS
  obtain ⟨πt, _, hqt, hpt⟩ :=
    Scheme.fullPointedStrictHenselizationCone barT pT hσT
  let PB := Scheme.pointedPullback hbar
  let D := CategoryOfElements.π (Scheme.pointSmallEtale barS).fiber ⋙
    Scheme.Etale.forget S ⋙ Over.forget S
  let π : (Functor.const _).obj (Scheme.strictHenselizationScheme barT) ⟶ D :=
    { app := fun j ↦ πt.app (PB.obj j) ≫ pullback.fst j.1.hom g
      naturality := by
        intro j k a
        simp only [Functor.const_obj_map]
        have hn := (Cone.mk _ πt).w (PB.map a)
        change πt.app (PB.obj j) ≫ (PB.map a).1.left = πt.app (PB.obj k) at hn
        have ha : (PB.map a).1.left ≫ pullback.fst k.1.hom g =
            pullback.fst j.1.hom g ≫ a.1.left := by
          change pullback.lift (pullback.fst j.1.hom g ≫ a.1.left)
            (pullback.snd j.1.hom g) _ ≫ pullback.fst k.1.hom g = _
          exact pullback.lift_fst _ _ _
        change πt.app (PB.obj k) ≫ pullback.fst k.1.hom g =
          (πt.app (PB.obj j) ≫ pullback.fst j.1.hom g) ≫ a.1.left
        rw [Category.assoc, ← ha, ← Category.assoc, hn] }
  let c := Cone.mk _ π
  let f := hs.lift c
  have hf : f ≫ Scheme.strictHenselizationStructuralMap barS =
      Scheme.strictHenselizationStructuralMap barT ≫ g := by
    let j : (Scheme.pointSmallEtale barS).fiber.Elements :=
      Classical.choice (IsCofiltered.nonempty (C :=
        (Scheme.pointSmallEtale barS).fiber.Elements))
    rw [← hqs j, ← Category.assoc, hs.fac c j]
    change (πt.app (PB.obj j) ≫ pullback.fst j.1.hom g) ≫ j.1.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ g) (hqt (PB.obj j))
  have hp : pT ≫ f = pS := by
    apply hs.hom_ext
    intro j
    rw [Category.assoc, hs.fac c j, hps]
    change pT ≫ (πt.app (PB.obj j) ≫ pullback.fst j.1.hom g) = _
    rw [← Category.assoc, hpt]
    change pullback.lift j.2.left barT _ ≫ pullback.fst j.1.hom g = j.2.left
    exact pullback.lift_fst _ _ _
  let h : Scheme.strictHenselizationRing barS ⟶ Scheme.strictHenselizationRing barT :=
    Spec.preimage f
  have hh : Spec.map h = f := Spec.map_preimage f
  have hres : ψS = ψT.comp h.hom := by
    have heq : CommRingCat.ofHom ψS = h ≫ CommRingCat.ofHom ψT := by
      apply Spec.map_injective
      change pS = Spec.map (h ≫ CommRingCat.ofHom ψT)
      rw [Spec.map_comp, hh]
      exact hp.symm
    exact congrArg CommRingCat.Hom.hom heq
  have hlocal : IsLocalHom h.hom := by
    have : IsLocalHom (ψT.comp h.hom) := hres ▸ inferInstance
    exact isLocalHom_of_comp h.hom ψT
  exact ⟨h, hlocal, hh ▸ hf, hres⟩

end AlgebraicGeometry
