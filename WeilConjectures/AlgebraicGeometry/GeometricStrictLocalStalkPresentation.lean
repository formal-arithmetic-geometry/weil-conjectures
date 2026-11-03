/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedLift
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.RingTheory.ProEtale.IndEtale
import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.RingTheory.HenselianEtaleRetraction
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties

/-! # A geometric strict localization as a strict henselization of its ordinary stalk

Source: Stacks Project, Tags 04HX and 01HV
(blueprint: lem-trf-geometric-strict-local-stalk-presentation).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Present the geometric strict local ring using the actual scheme stalk as base.
Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), and Tag 01HV
(lemma-spec-sheaves).
(blueprint: lem-trf-geometric-strict-local-stalk-presentation).

Proof: keep the geometric strict local ring S itself as H. Its structural map sends
its closed point to the image of x, so the map on stalks gives C → S and its
factorization through Spec C. The canonical evaluation S → Ω factors surjectively
through K. Cancellation of the monomorphism Spec C → X shows that this evaluation
respects the C-algebra structure determined by hΩ.
Choose an affine open Spec R containing the image of x. The ring C is a localization
of R, hence ind-etale over R; S is ind-etale over R by the affine-chart theorem.
Relative cancellation for ind-etale maps makes S ind-etale over C.
Every K-pointed etale C-algebra has a unique lift into the henselian local ring S.
These lifts form a cocone. Take a filtered etale C-algebra presentation of S and
point its stages by evaluation into K. Each lifted pointed etale C-algebra factors
through a stage, since it is finitely presented. Cocone naturality gives the
universal property on all pointed etale algebras, and restriction to the filtered
presentation gives uniqueness. Descending the pointing cocone recovers S → K.
This defines P directly; theta is the identity, so both required compatibilities
are the already established structural and evaluation equations. -/
theorem geometricStrictLocal_stalk_presentation
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω]
    (hΩ : algebraMap
      (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω =
        (descResidueField (stalkClosedPointTo x)).hom)
    [Algebra (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))
      (separableClosure
        (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω)]
    [IsScalarTower (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))
      (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω))))
      (separableClosure
        (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω)] :
    ∃ (H : Type u) (_ : CommRing H)
      (_ : Algebra (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω))) H)
      (P : Algebra.StrictHenselizationPresentationIn
        (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))
        (separableClosure
          (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω) H)
      (_ : IsLocalRing H) (θ : strictHenselizationRing x ≃+* H),
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ strictHenselizationStructuralMap x =
        Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω))) H)) ≫
            X.fromSpecStalk (x (IsLocalRing.closedPoint Ω)) ∧
      (separableClosure
        (IsLocalRing.ResidueField
          (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω).subtype.comp
          (P.residueMap.comp θ.toRingHom) = strictHenselizationPointEvaluation x := by
  classical
  let z := x (IsLocalRing.closedPoint Ω)
  let C := X.presheaf.stalk z
  let K := separableClosure (IsLocalRing.ResidueField C) Ω
  let S := strictHenselizationRing x
  let : Algebra (X.residueField z) Ω :=
    (inferInstance : Algebra (IsLocalRing.ResidueField C) Ω)
  obtain ⟨hl, hs, hclosed, _⟩ := AlgebraicGeometry.strictHenselizationResidue x hΩ
  let := hl
  let := hs
  let f : Spec S ⟶ X := strictHenselizationStructuralMap x
  have hclosed' : f (IsLocalRing.closedPoint S) = z := hclosed
  have hz : Inseparable z (f (IsLocalRing.closedPoint S)) := by
    rw [hclosed']
  let a : C ⟶ S := (X.presheaf.stalkCongr hz).hom ≫ stalkClosedPointTo f
  have ha : Spec.map a ≫ X.fromSpecStalk z = f := by
    have hc : Spec.map (X.presheaf.stalkCongr hz).hom ≫
        X.fromSpecStalk z = X.fromSpecStalk (f (IsLocalRing.closedPoint S)) := by
      simp only [TopCat.Presheaf.stalkCongr_hom, SpecMap_stalkSpecializes_fromSpecStalk]
    dsimp only [a]
    rw [Spec.map_comp, Category.assoc, hc]
    exact Spec_stalkClosedPointTo_fromSpecStalk f
  let : Algebra C S := a.hom.toAlgebra
  let ε : S →+* K := strictHenselizationPointEvaluationToSep x hΩ
  have heval : K.subtype.comp ε = strictHenselizationPointEvaluation x := rfl
  have hbaseΩ : (strictHenselizationPointEvaluation x).comp a.hom =
      (stalkClosedPointTo x).hom := by
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk z)).mp
    change Spec.map (a ≫ CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫
      X.fromSpecStalk z = Spec.map (stalkClosedPointTo x) ≫ X.fromSpecStalk z
    rw [Spec.map_comp, Category.assoc, ha, strictHenselizationClosedLift_over,
      Spec_stalkClosedPointTo_fromSpecStalk]
  have hbase : ε.comp (algebraMap C S) = algebraMap C K := by
    apply RingHom.ext
    intro c
    apply Subtype.ext
    change strictHenselizationPointEvaluation x (a.hom c) =
      (algebraMap C K c : Ω)
    rw [IsScalarTower.algebraMap_apply C (IsLocalRing.ResidueField C) K]
    change strictHenselizationPointEvaluation x (a.hom c) =
      algebraMap (IsLocalRing.ResidueField C) Ω (IsLocalRing.residue C c)
    rw [hΩ]
    exact DFunLike.congr_fun hbaseΩ c
  let εa : S →ₐ[C] K := { __ := ε, commutes' := DFunLike.congr_fun hbase }
  have hsurj : Function.Surjective εa :=
    strictHenselizationPointEvaluationToSep_surjective x hΩ
  have hker : RingHom.ker εa.toRingHom = IsLocalRing.maximalIdeal S :=
    IsLocalRing.ker_eq_maximalIdeal ε hsurj
  obtain ⟨U, hU, hzU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := z) (U := ⊤) (by trivial)
  let R := Γ(X, U)
  let g := X.presheaf.germ U z hzU
  let : Algebra R C := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzU⟩
  have hloc : IsLocalization (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl C :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  let := hloc
  have : Algebra.IndZariski R C :=
    Algebra.IndZariski.of_isLocalization (R := R) C (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
  have hC : Algebra.IndEtale R C := inferInstance
  let b : R ⟶ S := g ≫ a
  let : Algebra R S := b.hom.toAlgebra
  have hb : Spec.map b ≫ hU.fromSpec = f := by
    rw [show b = g ≫ a from rfl, Spec.map_comp, Category.assoc]
    change Spec.map a ≫ hU.fromSpecStalk hzU = f
    rw [hU.fromSpecStalk_eq_fromSpecStalk hzU]
    exact ha
  have hS : Algebra.IndEtale R S :=
    smallStrictHenselization_indEtale_of_affine_chart x R hU.fromSpec
      ⟨hU.primeIdealOf ⟨z, hzU⟩, hU.fromSpec_primeIdealOf ⟨z, hzU⟩⟩
      (Iso.refl _) b.hom (by
        change Spec.map b ≫ hU.fromSpec = 𝟙 (Spec S) ≫ f
        rw [Category.id_comp]
        exact hb)
  let aR : C →ₐ[R] S := { __ := a.hom, commutes' := fun _ ↦ rfl }
  have hind : a.hom.IndEtale :=
    RingHom.indEtale_principalZariski_stability.2.2.2.2.2.2.2.1 R C S hC hS aR
  have : Algebra.IndEtale C S := (RingHom.IndEtale.algebraMap_iff C S).mp hind
  obtain ⟨P, hP⟩ :=
    Algebra.strictHenselizationPresentationIn_of_henselian_indEtale C K S εa hsurj hker
  refine ⟨S, inferInstance, inferInstance, P, inferInstance, RingEquiv.refl _, ?_, ?_⟩
  · change Spec.map (𝟙 S) ≫ f = Spec.map a ≫ X.fromSpecStalk z
    rw [Spec.map_id, Category.id_comp]
    exact ha.symm
  · change K.subtype.comp (P.residueMap.comp (RingHom.id S)) = _
    rw [RingHom.comp_id, hP]
    exact heval


end AlgebraicGeometry.Scheme
