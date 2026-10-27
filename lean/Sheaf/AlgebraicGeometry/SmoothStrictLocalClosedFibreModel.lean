/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.Paper.StrictHenselizationFunctoriality
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.SmoothStrictLocalBaseModel
import Sheaf.AlgebraicGeometry.QuotientBaseChangeAffineModel
import Sheaf.AlgebraicGeometry.QuotientBaseChangeStrictLocalRing
import Sheaf.AlgebraicGeometry.GeometricStrictLocalStalkPresentation
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.RingTheory.StrictHenselizationRegular

/-! # The closed fibre of a smooth strict-local morphism

Source: Stacks Project, Tags 05WS, 04HX, 01VB, 00TT, 06LJ and 06LN
(blueprint: lem-trf-smooth-strict-local-closed-fibre-model).

The residue quotient is constructed using the kernel of geometric evaluation. The theorem
identifies this ideal with the maximal ideal, so the constructions need no local-ring
instance supplied as an extra hypothesis. A pointed-algebra presentation on the geometric
strict local ring gives its canonical identification with the algebraic strict henselization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The specified strict-local base change `W`.
Source: Stacks Project, Tag 01VB
(blueprint: lem-trf-smooth-strict-local-closed-fibre-model). -/
noncomputable def smoothStrictLocalBase {V S : Scheme.{u}} (f : V ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) : Scheme.{u} :=
  pullback f (strictHenselizationStructuralMap (v ≫ f))

/-- The residue quotient, with its canonical embedding into the geometric field given by
`RingHom.kerLift`. The theorem identifies the defining ideal with the maximal ideal.
Source: Stacks Project, Tag 04HX
(blueprint: lem-trf-smooth-strict-local-closed-fibre-model). -/
noncomputable def smoothStrictLocalResidue {V S : Scheme.{u}} (f : V ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) : CommRingCat.{u} :=
  .of (strictHenselizationRing (v ≫ f) ⧸ RingHom.ker (strictHenselizationPointEvaluation (v ≫ f)))

/-- The closed fibre `Z = W ×[Spec A] Spec κ`, including its scheme structure.
Source: Stacks Project, Tags 01VB and 05WS
(blueprint: lem-trf-smooth-strict-local-closed-fibre-model). -/
noncomputable def smoothStrictLocalClosedFibre {V S : Scheme.{u}} (f : V ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) : Scheme.{u} :=
  pullback (pullback.snd f (strictHenselizationStructuralMap (v ≫ f)))
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (RingHom.ker (strictHenselizationPointEvaluation (v ≫ f))))))

/-- The extended base maximal ideal in `B`, using the canonical functorial ring map.
Source: Stacks Project, Tag 05WS
(blueprint: lem-trf-smooth-strict-local-closed-fibre-model). -/
noncomputable def smoothStrictLocalClosedFibreIdeal {V S : Scheme.{u}} (f : V ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) :
    Ideal (strictHenselizationRing v) :=
  Ideal.map (Spec.preimage (strictHenselizationMap f v)).hom
    (RingHom.ker (strictHenselizationPointEvaluation (v ≫ f)))

/-- The quotient closed fibre and its canonical algebraic strict-local presentation.
Source: Stacks Project, Tags 05WS, 04HX, 01VB, 00TT, 06LJ and 06LN
(blueprint: lem-trf-smooth-strict-local-closed-fibre-model).

Proof:
1. The smooth strict-local base-model theorem supplies the local base ring, evaluation
   kernel, smooth projection, and the two compatible algebraic comparison isomorphisms.
2. The residue quotient is a field because the evaluation kernel is maximal. Factor
   evaluation through this quotient and lift the base-model point to the closed fibre.
   Smoothness and the closed immersion follow by base change.
3. `quotient_base_change_affine_model` gives the quotient on every affine chart, including
   its projection equation. It is proved from the adopted quotient-pushout theorem.
4. Compose the two base-model comparisons to get eW. Its spectrum is the inverse of the
   strict-local projection, and it preserves evaluation. Uniqueness of the canonical
   pointed strict-local morphism gives the A-action equation.
5. `quotient_base_change_strict_local_ring` applies the Cartesian closed-immersion theorem
   and the affine quotient model. Transport its extended ideal through eW, using the
   A-action equation. The formula for `Ideal.quotientEquiv` on representatives gives eQ
   and its compatibility with the canonical quotient map.
6. `geometric_strict_local_stalk_presentation` supplies the ordinary-stalk presentation
   with its structural and evaluation equations. The existing `IsRegular.of_smooth`
   makes the ordinary stalk regular, hence Noetherian. The presentation witnesses
   `IsStrictHenselization`, so strict-henselization regularity makes the geometric ring
   regular as well. No Noetherianity is imposed on S.
-/
theorem smooth_strict_local_closed_fibre_model {V S : Scheme.{u}} (f : V ⟶ S) [Smooth f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) :
    ∃ (_ : IsLocalRing (strictHenselizationRing (v ≫ f))),
      RingHom.ker (strictHenselizationPointEvaluation (v ≫ f)) =
        IsLocalRing.maximalIdeal (strictHenselizationRing (v ≫ f)) ∧
      IsField (smoothStrictLocalResidue f v) ∧
      ∃ zbar : Spec (.of Ω) ⟶ smoothStrictLocalClosedFibre f v,
        zbar ≫ pullback.fst _ _ ≫ pullback.fst f
          (strictHenselizationStructuralMap (v ≫ f)) = v ∧
        zbar ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
          (RingHom.kerLift (strictHenselizationPointEvaluation (v ≫ f)))) ∧
        Smooth (pullback.snd
          (pullback.snd f (strictHenselizationStructuralMap (v ≫ f)))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (RingHom.ker (strictHenselizationPointEvaluation (v ≫ f))))))) ∧
        IsClosedImmersion (pullback.fst
          (pullback.snd f (strictHenselizationStructuralMap (v ≫ f)))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (RingHom.ker (strictHenselizationPointEvaluation (v ≫ f))))))) ∧
        (∀ (D : CommRingCat.{u}) (j : Spec D ⟶ smoothStrictLocalBase f v)
          [IsOpenImmersion j],
          ∃ e : pullback (pullback.fst _ _ : smoothStrictLocalClosedFibre f v ⟶
              smoothStrictLocalBase f v) j ≅
            Spec (.of (D ⧸ Ideal.map (Spec.preimage (j ≫ pullback.snd f
              (strictHenselizationStructuralMap (v ≫ f)))).hom
                (RingHom.ker (strictHenselizationPointEvaluation (v ≫ f))))),
            e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) =
              pullback.snd _ j) ∧
        ∃ eW : strictHenselizationRing (zbar ≫ pullback.fst _ _) ≃+*
            strictHenselizationRing v,
          Spec.map (CommRingCat.ofHom eW.toRingHom) ≫
              strictHenselizationStructuralMap (zbar ≫ pullback.fst _ _) ≫
              pullback.fst f (strictHenselizationStructuralMap (v ≫ f)) =
            strictHenselizationStructuralMap v ∧
          (strictHenselizationPointEvaluation v).comp eW.toRingHom =
            strictHenselizationPointEvaluation (zbar ≫ pullback.fst _ _) ∧
          eW.toRingHom.comp (Spec.preimage
            (strictHenselizationStructuralMap (zbar ≫ pullback.fst _ _) ≫
              pullback.snd f (strictHenselizationStructuralMap (v ≫ f)))).hom =
            (Spec.preimage (strictHenselizationMap f v)).hom ∧
          ∃ eQ : (strictHenselizationRing v ⧸ smoothStrictLocalClosedFibreIdeal f v) ≃+*
              strictHenselizationRing zbar,
            eQ.toRingHom.comp (Ideal.Quotient.mk (smoothStrictLocalClosedFibreIdeal f v)) =
              (Spec.preimage (strictHenselizationMap (pullback.fst _ _) zbar)).hom.comp
                eW.symm.toRingHom ∧
            IsRegularLocalRing ((smoothStrictLocalClosedFibre f v).presheaf.stalk
              (zbar (IsLocalRing.closedPoint Ω))) ∧
            IsRegularLocalRing (strictHenselizationRing zbar) ∧
            ∃ (_ : Algebra (IsLocalRing.ResidueField
                    ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω)))) Ω),
              algebraMap (IsLocalRing.ResidueField
                    ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω)))) Ω =
                  (descResidueField (stalkClosedPointTo zbar)).hom ∧
              ∃ (_ : Algebra ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω)))
                  (separableClosure (IsLocalRing.ResidueField
                    ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω)))) Ω))
                (_ : IsScalarTower ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω)))
                  (IsLocalRing.ResidueField ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω))))
                  (separableClosure (IsLocalRing.ResidueField
                    ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω)))) Ω))
                (_ : Algebra ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω))) (strictHenselizationRing zbar))
                (P : Algebra.StrictHenselizationPresentationIn.{u, u}
                  ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω)))
                  (separableClosure (IsLocalRing.ResidueField
                    ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω)))) Ω) (strictHenselizationRing zbar)),
                Spec.map (CommRingCat.ofHom (algebraMap
                    ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                      (zbar (IsLocalRing.closedPoint Ω))) (strictHenselizationRing zbar))) ≫
                    (smoothStrictLocalClosedFibre f v).fromSpecStalk
                      (zbar (IsLocalRing.closedPoint Ω)) =
                  strictHenselizationStructuralMap zbar ∧
                (separableClosure (IsLocalRing.ResidueField
                    ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                    (zbar (IsLocalRing.closedPoint Ω)))) Ω).subtype.comp P.residueMap =
                  strictHenselizationPointEvaluation zbar := by
  classical
  let A := strictHenselizationRing (v ≫ f)
  let I := RingHom.ker (strictHenselizationPointEvaluation (v ≫ f))
  let p := pullback.snd f (strictHenselizationStructuralMap (v ≫ f))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let w := SmoothStrictLocalBaseModel.geometricPoint f v
  obtain ⟨hp, hA, hB, hwpoint, hflat, hloc, hloc', hker, hker', hnoeth,
    hiso, hproj, aΩ, haΩ, aK, tower, H, hH, aH, P, hlH, θ, β,
    hβlocal, hβmap, hβeval, hθstruct, hθeval, hβspec⟩ :=
    SmoothStrictLocalBaseModel.smooth_strictLocal_base_model f v
  let := hA
  have hfield : IsField (smoothStrictLocalResidue f v) := by
    apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mp
    change (RingHom.ker (strictHenselizationPointEvaluation (v ≫ f))).IsMaximal
    rw [hker]
    exact IsLocalRing.maximalIdeal.isMaximal A
  let := hfield.toField
  have hw : w ≫ p = Spec.map (CommRingCat.ofHom
      (strictHenselizationPointEvaluation (v ≫ f))) := by
    exact pullback.lift_snd _ _ _
  have hwv : w ≫ pullback.fst f (strictHenselizationStructuralMap (v ≫ f)) = v := by
    exact pullback.lift_fst _ _ _
  let r := Spec.map (CommRingCat.ofHom
    (RingHom.kerLift (strictHenselizationPointEvaluation (v ≫ f))))
  have hr : r ≫ q = w ≫ p := by
    rw [hw, ← Spec.map_comp]
    congr 1
  let z : Spec (.of Ω) ⟶ smoothStrictLocalClosedFibre f v := pullback.lift w r hr.symm
  have hzw : z ≫ pullback.fst p q = w := pullback.lift_fst _ _ _
  have hzr : z ≫ pullback.snd p q = r := pullback.lift_snd _ _ _
  have hsmooth : Smooth (pullback.snd p q) := by
    let : Smooth p := hp
    infer_instance
  have hclosed : IsClosedImmersion (pullback.fst p q) := by
    let : IsClosedImmersion q :=
      IsClosedImmersion.spec_of_quotient_mk I
    infer_instance
  have hcharts : ∀ (D : CommRingCat.{u}) (j : Spec D ⟶ smoothStrictLocalBase f v)
      [IsOpenImmersion j],
      ∃ e : pullback (pullback.fst p q) j ≅
          Spec (.of (D ⧸ Ideal.map (Spec.preimage (j ≫ p)).hom I)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = pullback.snd _ j := by
    intro D j _
    exact quotient_base_change_affine_model A p I D j
  let e : strictHenselizationRing w ≃+* strictHenselizationRing v := θ.trans β.symm
  have heval : (strictHenselizationPointEvaluation v).comp e.toRingHom =
      strictHenselizationPointEvaluation w := by
    rw [← hβeval, ← hθeval]
    ext c
    let ε : H →+* Ω :=
      (separableClosure (IsLocalRing.ResidueField
        (SmoothStrictLocalBaseModel.ordinaryLocalRing f v)) Ω).subtype.comp P.residueMap
    change ε (β (β.symm (θ c))) = ε (θ c)
    exact congrArg ε (β.apply_symm_apply _)
  let er : strictHenselizationRing w ⟶ strictHenselizationRing v :=
    CommRingCat.ofHom e.toRingHom
  let br : strictHenselizationRing v ⟶ CommRingCat.of H := CommRingCat.ofHom β.toRingHom
  let tr : strictHenselizationRing w ⟶ CommRingCat.of H := CommRingCat.ofHom θ.toRingHom
  have hbr : IsIso br := by
    exact (inferInstance : IsIso β.toCommRingCatIso.hom)
  have hespec : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      SmoothStrictLocalBaseModel.strictProjection f v = 𝟙 _ := by
    change Spec.map er ≫ SmoothStrictLocalBaseModel.strictProjection f v = 𝟙 _
    apply (cancel_epi (Spec.map br)).mp
    rw [← Category.assoc, ← Spec.map_comp]
    have hc : er ≫ br = tr := by
      ext c
      change β (β.symm (θ c)) = θ c
      exact β.apply_symm_apply _
    rw [hc, Category.comp_id]
    exact hβspec.symm
  have hestruct : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      strictHenselizationStructuralMap w ≫
        pullback.fst f (strictHenselizationStructuralMap (v ≫ f)) =
      strictHenselizationStructuralMap v := by
    rw [← hproj, ← Category.assoc, hespec, Category.id_comp]
  have heaction : e.toRingHom.comp
      (Spec.preimage (strictHenselizationStructuralMap w ≫ p)).hom =
        (Spec.preimage (strictHenselizationMap f v)).hom := by
    have heq : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        strictHenselizationStructuralMap w ≫ p = strictHenselizationMap f v := by
      apply (strictHenselizationMap_existsUnique f v).unique
      · constructor
        · change Spec.map er ≫ strictHenselizationStructuralMap w ≫
              pullback.snd f (strictHenselizationStructuralMap (v ≫ f)) ≫
              strictHenselizationStructuralMap (v ≫ f) = _
          rw [← pullback.condition]
          simpa only [Category.assoc] using congrArg (fun h ↦ h ≫ f) hestruct
        · change (Spec.map (CommRingCat.ofHom
              (strictHenselizationPointEvaluation v) : strictHenselizationRing v ⟶ .of Ω) ≫
              Spec.map er) ≫ strictHenselizationStructuralMap w ≫ p = _
          rw [← Spec.map_comp]
          have hc : er ≫ (CommRingCat.ofHom
              (strictHenselizationPointEvaluation v) : strictHenselizationRing v ⟶ .of Ω) =
              (CommRingCat.ofHom (strictHenselizationPointEvaluation w) :
                strictHenselizationRing w ⟶ .of Ω) :=
            CommRingCat.hom_ext heval
          rw [hc]
          simpa only [Category.assoc] using
            (congrArg (fun h ↦ h ≫ p) (strictHenselizationClosedLift_over w)).trans hw
      · exact (Classical.choose_spec (strictHenselizationMap_existsUnique f v)).1
    apply congrArg CommRingCat.Hom.hom
    change Spec.preimage (strictHenselizationStructuralMap w ≫ p) ≫ er =
      Spec.preimage (strictHenselizationMap f v)
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact heq
  have heWdata : ∃ eW : strictHenselizationRing (z ≫ pullback.fst p q) ≃+*
      strictHenselizationRing v,
      Spec.map (CommRingCat.ofHom eW.toRingHom) ≫
          strictHenselizationStructuralMap (z ≫ pullback.fst p q) ≫
          pullback.fst f (strictHenselizationStructuralMap (v ≫ f)) =
        strictHenselizationStructuralMap v ∧
      (strictHenselizationPointEvaluation v).comp eW.toRingHom =
        strictHenselizationPointEvaluation (z ≫ pullback.fst p q) ∧
      eW.toRingHom.comp (Spec.preimage
          (strictHenselizationStructuralMap (z ≫ pullback.fst p q) ≫ p)).hom =
        (Spec.preimage (strictHenselizationMap f v)).hom := by
    rw [hzw]
    exact ⟨e, hestruct, heval, heaction⟩
  obtain ⟨eW, heWstruct, heWeval, heWaction⟩ := heWdata
  obtain ⟨e₀, he₀⟩ := quotient_base_change_strict_local_ring A p I z
  let J := Ideal.map (Spec.preimage
    (strictHenselizationStructuralMap (z ≫ pullback.fst p q) ≫ p)).hom I
  have hJ : smoothStrictLocalClosedFibreIdeal f v = Ideal.map eW.toRingHom J := by
    dsimp [smoothStrictLocalClosedFibreIdeal, J, I]
    rw [Ideal.map_map]
    exact congrArg (fun h ↦ Ideal.map h _) heWaction.symm
  let eQ := (Ideal.quotientEquiv J (smoothStrictLocalClosedFibreIdeal f v) eW hJ).symm.trans e₀
  have heQ : eQ.toRingHom.comp (Ideal.Quotient.mk (smoothStrictLocalClosedFibreIdeal f v)) =
      (Spec.preimage (strictHenselizationMap (pullback.fst p q) z)).hom.comp
        eW.symm.toRingHom := by
    ext b
    change e₀ ((Ideal.quotientEquiv J _ eW hJ).symm
      (Ideal.Quotient.mk _ b)) = _
    rw [Ideal.quotientEquiv_symm_mk]
    exact DFunLike.congr_fun he₀ (eW.symm b)
  have hreg : IsRegularLocalRing ((smoothStrictLocalClosedFibre f v).presheaf.stalk
      (z (IsLocalRing.closedPoint Ω))) := by
    let : Smooth (pullback.snd p q) := hsmooth
    let : IsRegular (smoothStrictLocalClosedFibre f v) := IsRegular.of_smooth
      (k := smoothStrictLocalResidue f v) (pullback.snd p q)
    infer_instance
  let aΩ_z : Algebra (IsLocalRing.ResidueField
      ((smoothStrictLocalClosedFibre f v).presheaf.stalk
        (z (IsLocalRing.closedPoint Ω)))) Ω :=
    (descResidueField (stalkClosedPointTo z)).hom.toAlgebra
  let : Algebra (IsLocalRing.ResidueField
      ((smoothStrictLocalClosedFibre f v).presheaf.stalk
        (z (IsLocalRing.closedPoint Ω)))) Ω := aΩ_z
  let aK_z : Algebra ((smoothStrictLocalClosedFibre f v).presheaf.stalk
      (z (IsLocalRing.closedPoint Ω)))
      (separableClosure (IsLocalRing.ResidueField
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω)))) Ω) :=
    ((algebraMap (IsLocalRing.ResidueField
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω))))
      (separableClosure (IsLocalRing.ResidueField
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω)))) Ω)).comp
      (algebraMap ((smoothStrictLocalClosedFibre f v).presheaf.stalk
        (z (IsLocalRing.closedPoint Ω)))
        (IsLocalRing.ResidueField
          ((smoothStrictLocalClosedFibre f v).presheaf.stalk
            (z (IsLocalRing.closedPoint Ω)))))).toAlgebra
  let : Algebra ((smoothStrictLocalClosedFibre f v).presheaf.stalk
      (z (IsLocalRing.closedPoint Ω)))
      (separableClosure (IsLocalRing.ResidueField
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω)))) Ω) := aK_z
  have tz : IsScalarTower ((smoothStrictLocalClosedFibre f v).presheaf.stalk
      (z (IsLocalRing.closedPoint Ω)))
      (IsLocalRing.ResidueField ((smoothStrictLocalClosedFibre f v).presheaf.stalk
        (z (IsLocalRing.closedPoint Ω))))
      (separableClosure (IsLocalRing.ResidueField
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω)))) Ω) := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  have haΩ_z : algebraMap (IsLocalRing.ResidueField
      ((smoothStrictLocalClosedFibre f v).presheaf.stalk
        (z (IsLocalRing.closedPoint Ω)))) Ω =
      (descResidueField (stalkClosedPointTo z)).hom := by
    exact RingHom.algebraMap_toAlgebra _
  obtain ⟨H_z, hH_z, aH_z, Pz, hlH_z, θz, hPstruct_z, hPeval_z⟩ :=
    geometricStrictLocal_stalk_presentation z haΩ_z
  let : CommRing H_z := hH_z
  let : Algebra ((smoothStrictLocalClosedFibre f v).presheaf.stalk
      (z (IsLocalRing.closedPoint Ω))) H_z := aH_z
  let : IsLocalRing H_z := hlH_z
  let aStrict : Algebra ((smoothStrictLocalClosedFibre f v).presheaf.stalk
      (z (IsLocalRing.closedPoint Ω))) (strictHenselizationRing z) :=
    (θz.symm.toRingHom.comp (algebraMap
      ((smoothStrictLocalClosedFibre f v).presheaf.stalk
        (z (IsLocalRing.closedPoint Ω))) H_z)).toAlgebra
  let : Algebra ((smoothStrictLocalClosedFibre f v).presheaf.stalk
      (z (IsLocalRing.closedPoint Ω))) (strictHenselizationRing z) := aStrict
  let θA : strictHenselizationRing z ≃ₐ[
      (smoothStrictLocalClosedFibre f v).presheaf.stalk
        (z (IsLocalRing.closedPoint Ω))] H_z :=
    { θz with
      commutes' := by
        intro a
        change θz (θz.symm (algebraMap
          ((smoothStrictLocalClosedFibre f v).presheaf.stalk
            (z (IsLocalRing.closedPoint Ω))) H_z a)) = algebraMap
          ((smoothStrictLocalClosedFibre f v).presheaf.stalk
            (z (IsLocalRing.closedPoint Ω))) H_z a
        simp }
  let Pstrict : Algebra.StrictHenselizationPresentationIn.{u, u}
      ((smoothStrictLocalClosedFibre f v).presheaf.stalk
        (z (IsLocalRing.closedPoint Ω)))
      (separableClosure (IsLocalRing.ResidueField
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω)))) Ω) (strictHenselizationRing z) :=
    { cocone := Pz.cocone
      isColimit := Pz.isColimit
      identification := Pz.identification ≪≫ (CommAlgCat.isoMk θA).symm }
  have hPres : Pstrict.residueMap = Pz.residueMap.comp θz.toRingHom := by
    change ((CommAlgCat.isoMk θA).hom ≫ Pz.identification.inv ≫
      Pz.isColimit.desc (Algebra.strictHenselizationPointingCoconeIn
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω)))
        (separableClosure (IsLocalRing.ResidueField
          ((smoothStrictLocalClosedFibre f v).presheaf.stalk
            (z (IsLocalRing.closedPoint Ω)))) Ω))).hom.toRingHom = _
    change ((Pz.identification.inv ≫ Pz.isColimit.desc
      (Algebra.strictHenselizationPointingCoconeIn
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω)))
        (separableClosure (IsLocalRing.ResidueField
          ((smoothStrictLocalClosedFibre f v).presheaf.stalk
            (z (IsLocalRing.closedPoint Ω)))) Ω))).hom.toRingHom.comp
      θz.toRingHom) = _
    rfl
  have hPstruct : Spec.map (CommRingCat.ofHom
      (algebraMap ((smoothStrictLocalClosedFibre f v).presheaf.stalk
        (z (IsLocalRing.closedPoint Ω))) (strictHenselizationRing z))) ≫
      (smoothStrictLocalClosedFibre f v).fromSpecStalk
        (z (IsLocalRing.closedPoint Ω)) = strictHenselizationStructuralMap z := by
    calc
      Spec.map (CommRingCat.ofHom
          (algebraMap ((smoothStrictLocalClosedFibre f v).presheaf.stalk
            (z (IsLocalRing.closedPoint Ω))) (strictHenselizationRing z))) ≫
          (smoothStrictLocalClosedFibre f v).fromSpecStalk
            (z (IsLocalRing.closedPoint Ω)) =
          Spec.map (CommRingCat.ofHom θz.symm.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap
              ((smoothStrictLocalClosedFibre f v).presheaf.stalk
                (z (IsLocalRing.closedPoint Ω))) H_z)) ≫
            (smoothStrictLocalClosedFibre f v).fromSpecStalk
              (z (IsLocalRing.closedPoint Ω)) := by
                rw [← Category.assoc, ← Spec.map_comp]
                rfl
      _ = Spec.map (CommRingCat.ofHom θz.symm.toRingHom) ≫
            Spec.map (CommRingCat.ofHom θz.toRingHom) ≫
            strictHenselizationStructuralMap z := by rw [hPstruct_z]
      _ = strictHenselizationStructuralMap z := by
        rw [← Category.assoc, ← Spec.map_comp]
        rw [← CommRingCat.ofHom_comp]
        simp
  have hPeval :
      (separableClosure (IsLocalRing.ResidueField
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω)))) Ω).subtype.comp Pstrict.residueMap =
        strictHenselizationPointEvaluation z := by
    rw [hPres]
    exact hPeval_z
  let := hreg
  have hstrict : Algebra.IsStrictHenselization
      ((smoothStrictLocalClosedFibre f v).presheaf.stalk (z (IsLocalRing.closedPoint Ω)))
      (separableClosure (IsLocalRing.ResidueField
        ((smoothStrictLocalClosedFibre f v).presheaf.stalk
          (z (IsLocalRing.closedPoint Ω)))) Ω) (strictHenselizationRing z) :=
    ⟨Pstrict.cocone, ⟨Pstrict.isColimit⟩, ⟨Pstrict.identification⟩⟩
  have hregsh : IsRegularLocalRing (strictHenselizationRing z) :=
    (Algebra.isRegularLocalRing_iff_strictHenselization _ _ _ hstrict).mp hreg
  refine ⟨hA, hker, hfield, z, ?_, hzr, hsmooth, hclosed, hcharts,
    eW, heWstruct, heWeval, heWaction, eQ, heQ, hreg, hregsh,
    aΩ_z, haΩ_z, aK_z, tz, aStrict, Pstrict, hPstruct, hPeval⟩
  rw [← Category.assoc, hzw, hwv]

end AlgebraicGeometry.Scheme
