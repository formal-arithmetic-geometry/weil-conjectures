/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedHenselianLisseRigidity
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftMap
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.RingTheory.ProEtale.HenselianClosedLift
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedWContractibleProjectiveCalculus
import all WeilConjectures.RingTheory.WContractibleGeometricCriterion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Prescribed scalar models on henselian lifts of a finite closed covering

Source: Hemo--Richarz--Scholbach, Theorem 4.13, finite-component paragraph and
Corollary 4.4(2); Bhatt--Scholze, Definition 2.2.10 and Lemmas 2.2.12, 6.1.1
(blueprint: lem-zl-condensed-finite-closed-model-lifts).

The lift is the published small filtered colimit `Algebra.ClosedLift`. The restriction
of an isomorphism uses the canonical composition and scalar-realization comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The structure morphism of the specified closed lift, with its actual colimit algebra.
Source: BS Definition 2.2.10 and Lemma 6.1.1; HRS Theorem 4.13
(blueprint: lem-zl-condensed-finite-closed-model-lifts). -/
def closedModelLiftMap (A Cbar : Type u) [CommRing A] [CommRing Cbar] [Algebra A Cbar] :
    Spec (.of (Algebra.ClosedLift A Cbar)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Algebra.ClosedLift A Cbar)))

/-- The closed-fiber morphism induced by the retained colimit map to the input algebra.
Its composite with `closedModelLiftMap` is the given A-algebra structure map on spectra,
since `Algebra.ClosedLift.toAlgHom` is an A-algebra homomorphism.
Source: BS Definition 2.2.10 and Lemma 2.2.12; HRS Theorem 4.13
(blueprint: lem-zl-condensed-finite-closed-model-lifts). -/
def closedModelFiberMap (A Cbar : Type u) [CommRing A] [CommRing Cbar] [Algebra A Cbar] :
    Spec (.of Cbar) ⟶ Spec (.of (Algebra.ClosedLift A Cbar)) :=
  Spec.map (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom A Cbar).toRingHom)

/-- Restrict a scalar-model isomorphism using the canonical derived composition comparison
and the canonical comparison for scalar realization. In particular the target is the
prescribed realization of the same P, with no choice of a comparison isomorphism.
Source: HRS Section 3 pullback paragraph, Corollary 4.4(2), Theorem 4.13
(blueprint: lem-zl-condensed-finite-closed-model-lifts). -/
def closedModelRestriction
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (A Cbar : Type u) [CommRing A] [CommRing Cbar] [Algebra A Cbar]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
        (condensedRingObj Λ.X (Spec (.of A)))))
    (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)))
    (e : (CondensedRing.upperStar Λ.X (closedModelLiftMap A Cbar)).mapDerivedCategory.obj K ≅
      (condensedScalarRealization Λ.X (Spec (.of (Algebra.ClosedLift A Cbar)))).obj P) :
    (CondensedRing.upperStar Λ.X
      (closedModelFiberMap A Cbar ≫ closedModelLiftMap A Cbar)).mapDerivedCategory.obj K ≅
        (condensedScalarRealization Λ.X (Spec (.of Cbar))).obj P :=
  (Functor.mapDerivedCategoryNatIso
    (CondensedRing.upperStarComp Λ.X (closedModelFiberMap A Cbar)
      (closedModelLiftMap A Cbar))).app K ≪≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar Λ.X (closedModelLiftMap A Cbar))
      (CondensedRing.upperStar Λ.X (closedModelFiberMap A Cbar))).app K ≪≫
    (CondensedRing.upperStar Λ.X (closedModelFiberMap A Cbar)).mapDerivedCategory.mapIso e ≪≫
    (CondensedRing.discreteScalarExtensionPullbackIso Λ.X (closedModelFiberMap A Cbar)).app P

private def derivedPullbackComp
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CondensedRing.upperStar Λ.X (f ≫ g)).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ.X g).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ.X f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ.X f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private def derivedPullbackId
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    (CondensedRing.upperStar Λ.X (𝟙 X)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ.X X) ≪≫
    Functor.mapDerivedCategoryIdIso _

private theorem derivedPullback_fullyFaithful_of_isIso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Nonempty (CondensedRing.upperStar Λ.X f).mapDerivedCategory.FullyFaithful := by
  let F := (CondensedRing.upperStar Λ.X f).mapDerivedCategory
  let G := (CondensedRing.upperStar Λ.X (inv f)).mapDerivedCategory
  let e : _ ≌ _ := CategoryTheory.Equivalence.mk F G
    ((derivedPullbackId Λ Y).symm ≪≫
      Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarCongr Λ.X (by simp)) ≪≫
      derivedPullbackComp Λ (inv f) f)
    ((derivedPullbackComp Λ f (inv f)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarCongr Λ.X (by simp)) ≪≫
      derivedPullbackId Λ X)
  exact ⟨e.fullyFaithfulFunctor⟩

/-- The henselian ind-etale lifts of given w-contractible covers of a finite closed
covering carry the prescribed scalar models, with a unique lift of each prescribed
isomorphism; their finite disjoint union is an affine fpqc cover.
Source: HRS Theorem 4.13, finite-component paragraph, Corollary 4.4(2);
BS Definition 2.2.10 and Lemmas 2.2.12, 6.1.1
(blueprint: lem-zl-condensed-finite-closed-model-lifts).

Proof:
1. For each a the small index category of `Algebra.ClosedLift` is filtered
   (lem-exc-closed-lift-filtered). Its terms are finitely presented etale A-algebras,
   so its colimit is ind-etale. Lem-exc-closed-lift-reduction identifies the specified
   reduction with Cbar a; lem-zl-henselian-indetale-closed-lift makes the pair henselian.
2. Use this reduction to identify the closed fiber with the given w-contractible W_a.
   Lem-zl-condensed-henselian-lisse-rigidity gives w-contractibility of V_a and full
   faithfulness of closed-fiber inverse image on dualizable objects.
3. Lem-zl-condensed-lisse-proetale-locality preserves dualizability of K on V_a and
   gives the canonical scalar pullback comparison. Since P_a is perfect, the scalar
   model is dualizable by lem-zl-condensed-wcontractible-projective-calculus.
4. Fullness lifts alpha_a and its inverse. Faithfulness makes their composites identities
   and makes every other lift equal to this one. This proves existence and uniqueness
   with exactly the comparisons used in `closedModelRestriction`.
5. Lem-weil-pbc-ind-etale-stability makes V_a -> X weakly etale, hence flat.
   Faithful flatness of A/I_a -> Cbar a gives surjectivity on spectra by
   lem-weil-pbc-faithfully-flat-surjective-spectrum. The retained A-algebra map factors
   W_a -> X through V_a, so the image of V_a contains the closed subset cut out by I_a.
6. The closed subsets cover X. Thus the finite disjoint union is surjective. It is affine
   by lem-weil-pbc-affine-morphism-permanence; its map to the affine X is affine by
   lem-weil-pbc-morphism-affine-schemes-affine and hence quasi-compact. On each open
   summand its stalk maps are those of V_a -> X, so it is flat.
7. For an affine open U of X, its inverse image in each affine V_a is affine, and these
   finitely many affine opens jointly cover U. This is def-weil-pbc-proetale-covering.
   The argument never identifies different P_a. If the index set is empty, the closed
   covering hypothesis forces X empty, and the same assertions hold for the empty cover.
   No assertion about arbitrary closed subschemes of w-contractible schemes is used. -/
theorem condensed_finite_closed_model_lifts
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (A : Type u) [CommRing A] (ι : Type v) [Finite ι] (I : ι → Ideal A)
    (hcover : ∀ x : PrimeSpectrum A, ∃ a : ι, I a ≤ x.asIdeal)
    (Cbar : ι → Type u) [∀ a : ι, CommRing (Cbar a)]
    [∀ a : ι, Algebra A (Cbar a)] [∀ a : ι, Algebra (A ⧸ I a) (Cbar a)]
    [∀ a : ι, IsScalarTower A (A ⧸ I a) (Cbar a)]
    [∀ a : ι, Algebra.IndEtale (A ⧸ I a) (Cbar a)]
    [∀ a : ι, Module.FaithfullyFlat (A ⧸ I a) (Cbar a)]
    [∀ a : ι, IsWContractibleRing (Cbar a)]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
        (condensedRingObj Λ.X (Spec (.of A))))) (hK : IsDualizable K)
    (P : ι → DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)))
    (hP : ∀ a : ι, DerivedCategory.IsPerfectRingComplex (P a))
    (α : ∀ a : ι, (CondensedRing.upperStar Λ.X
      (closedModelFiberMap A (Cbar a) ≫ closedModelLiftMap A (Cbar a))).mapDerivedCategory.obj K ≅
        (condensedScalarRealization Λ.X (Spec (.of (Cbar a)))).obj (P a)) :
    (∀ a : ι,
      Algebra.IndEtale A (Algebra.ClosedLift A (Cbar a)) ∧
      Function.Bijective (Algebra.ClosedLift.reduction A (Cbar a) (I a)) ∧
      HenselianRing (Algebra.ClosedLift A (Cbar a))
        ((I a).map (algebraMap A (Algebra.ClosedLift A (Cbar a)))) ∧
      IsWContractibleRing (Algebra.ClosedLift A (Cbar a)) ∧
      (∃! e :
        (CondensedRing.upperStar Λ.X (closedModelLiftMap A (Cbar a))).mapDerivedCategory.obj K ≅
          (condensedScalarRealization Λ.X (Spec (.of (Algebra.ClosedLift A (Cbar a))))).obj (P a),
        closedModelRestriction Λ A (Cbar a) K (P a) e = α a) ∧
      WeaklyEtale (closedModelLiftMap A (Cbar a)) ∧
      Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I a)))) ⊆
        Set.range (closedModelLiftMap A (Cbar a))) ∧
    IsAffine (∐ fun a : ι ↦ Spec (.of (Algebra.ClosedLift A (Cbar a)))) ∧
    Surjective (Sigma.desc (fun a : ι ↦ closedModelLiftMap A (Cbar a))) ∧
    Flat (Sigma.desc (fun a : ι ↦ closedModelLiftMap A (Cbar a))) ∧
    QuasiCompact (Sigma.desc (fun a : ι ↦ closedModelLiftMap A (Cbar a))) ∧
    Presieve.ofArrows (fun a : ι ↦ Spec (.of (Algebra.ClosedLift A (Cbar a))))
      (fun a : ι ↦ closedModelLiftMap A (Cbar a)) ∈ Scheme.proetalePrecoverage (Spec (.of A)) := by
  classical
  have halg (a : ι) :
      Algebra.IndEtale A (Algebra.ClosedLift A (Cbar a)) ∧
      Function.Bijective (Algebra.ClosedLift.reduction A (Cbar a) (I a)) ∧
      HenselianRing (Algebra.ClosedLift A (Cbar a))
        ((I a).map (algebraMap A (Algebra.ClosedLift A (Cbar a)))) :=
    ⟨inferInstance, Algebra.ClosedLift.bijective_reduction A (Cbar a) (I a),
      Algebra.ClosedLift.henselianRing A (Cbar a) (I a)⟩
  have hmodels (a : ι) :
      IsWContractibleRing (Algebra.ClosedLift A (Cbar a)) ∧
      (∃! e :
        (CondensedRing.upperStar Λ.X (closedModelLiftMap A (Cbar a))).mapDerivedCategory.obj K ≅
          (condensedScalarRealization Λ.X
            (Spec (.of (Algebra.ClosedLift A (Cbar a))))).obj (P a),
        closedModelRestriction Λ A (Cbar a) K (P a) e = α a) := by
    let C := Algebra.ClosedLift A (Cbar a)
    let J := (I a).map (algebraMap A C)
    let r : (C ⧸ J) ≃+* Cbar a := RingEquiv.ofBijective
      (Algebra.ClosedLift.reduction A (Cbar a) (I a)) (halg a).2.1
    have : HenselianRing C J := (halg a).2.2
    have : IsWContractibleRing (C ⧸ J) := RingHom.wContractible_of_ringEquiv r.symm
    have hw : IsWContractibleRing C :=
      (CondensedRing.henselian_lisse_rigidity Λ.X C J).2.1.mpr inferInstance
    have : IsWContractibleRing C := hw
    let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    let t := Spec.map (CommRingCat.ofHom r.toRingHom)
    have : IsIso t := by
      change IsIso (Scheme.Spec.map r.toCommRingCatIso.hom.op)
      infer_instance
    have hfac : t ≫ q = closedModelFiberMap A (Cbar a) := by
      rw [← Spec.map_comp]
      rfl
    obtain ⟨e, ⟨he⟩⟩ :=
      ((CondensedRing.henselian_lisse_rigidity Λ.X C J).2.2 hw).2.2
    let D := IsDualizable (C := DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of C))) Ab.{u + 1})
        (condensedRingObj Λ.X (Spec (.of C)))))
    let F := (CondensedRing.upperStar Λ.X q).mapDerivedCategory
    let G := (CondensedRing.upperStar Λ.X t).mapDerivedCategory
    let H := (CondensedRing.upperStar Λ.X (closedModelFiberMap A (Cbar a))).mapDerivedCategory
    let incl := ObjectProperty.ι D
    let ff : (incl ⋙ F).FullyFaithful :=
      (e.fullyFaithfulFunctor.comp (ObjectProperty.fullyFaithfulι _)).ofIso he
    obtain ⟨gg⟩ := derivedPullback_fullyFaithful_of_isIso Λ t
    let hh : (incl ⋙ H).FullyFaithful :=
      ((ff.comp gg).ofIso
        ((Functor.associator incl F G) ≪≫
          Functor.isoWhiskerLeft incl ((derivedPullbackComp Λ t q).symm ≪≫
            Functor.mapDerivedCategoryNatIso
              (CondensedRing.upperStarCongr Λ.X hfac))))
    let M := (CondensedRing.upperStar Λ.X (closedModelLiftMap A (Cbar a))).mapDerivedCategory.obj K
    let N := (condensedScalarRealization Λ.X (Spec (.of C))).obj (P a)
    have hM : D M := condensed_derivedPullback_preserves_dualizable Λ _ K hK
    have : IsWContractibleRing Γ(Spec (.of C), ⊤) :=
      RingHom.wContractible_of_ringEquiv (Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv.symm
    obtain ⟨σ, _, hσ, _⟩ :=
      (CondensedRing.condensed_wcontractible_projective_calculus Λ (Spec (.of C))).2.2.2.2.2
    have hN : D N := (hσ (P a) (hP a)).2
    let m : ObjectProperty.FullSubcategory D := ⟨M, hM⟩
    let n : ObjectProperty.FullSubcategory D := ⟨N, hN⟩
    let b : H.obj M ≅ H.obj N :=
      ((derivedPullbackComp Λ (closedModelFiberMap A (Cbar a))
        (closedModelLiftMap A (Cbar a))).app K).symm ≪≫
      α a ≪≫
      ((CondensedRing.discreteScalarExtensionPullbackIso Λ.X
        (closedModelFiberMap A (Cbar a))).app (P a)).symm
    obtain ⟨z, hz⟩ := (hh.isoEquiv (X := m) (Y := n)).surjective b
    let z' : M ≅ N := incl.mapIso z
    have hz' : H.mapIso z' = b := hz
    refine ⟨hw, z', ?_, ?_⟩
    · apply Iso.ext
      have hzH := congrArg Iso.hom hz'
      dsimp [closedModelRestriction, b, derivedPullbackComp] at hzH ⊢
      rw [hzH]
      simp
    · intro w hw
      apply Iso.ext
      have hwH : H.mapIso w = b := by
        apply Iso.ext
        have hwH := congrArg Iso.hom hw
        dsimp [closedModelRestriction] at hwH
        dsimp [b, derivedPullbackComp]
        have := congrArg
          (fun k ↦ ((derivedPullbackComp Λ (closedModelFiberMap A (Cbar a))
            (closedModelLiftMap A (Cbar a))).app K).inv ≫ k ≫
            ((CondensedRing.discreteScalarExtensionPullbackIso Λ.X
              (closedModelFiberMap A (Cbar a))).app (P a)).inv) hwH
        simpa [derivedPullbackComp] using this
      exact congrArg (fun f ↦ incl.map f)
        (hh.map_injective (f := (ObjectProperty.fullyFaithfulι D).preimage (X := m) (Y := n) w.hom)
          (g := z.hom) (by
            change H.map w.hom = H.map z'.hom
            exact congrArg Iso.hom (hwH.trans hz'.symm)))
  have hweak (a : ι) : WeaklyEtale (closedModelLiftMap A (Cbar a)) := by
    dsimp [closedModelLiftMap]
    infer_instance
  have hrange (a : ι) :
      Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I a)))) ⊆
        Set.range (closedModelLiftMap A (Cbar a)) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := A ⧸ I a) (B := Cbar a) p
    refine ⟨(closedModelFiberMap A (Cbar a)) q, ?_⟩
    change PrimeSpectrum.comap (algebraMap A (Algebra.ClosedLift A (Cbar a)))
      (PrimeSpectrum.comap (Algebra.ClosedLift.toAlgHom A (Cbar a)).toRingHom q) =
        PrimeSpectrum.comap (Ideal.Quotient.mk (I a))
          (PrimeSpectrum.comap (algebraMap (A ⧸ I a) (Cbar a)) q)
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
    congr 1
    ext x
    simp [IsScalarTower.algebraMap_apply A (A ⧸ I a) (Cbar a),
      Ideal.Quotient.algebraMap_eq]
  have hsurj : ∀ x : Spec (.of A), ∃ a : ι,
      x ∈ Set.range (closedModelLiftMap A (Cbar a)) := by
    intro x
    obtain ⟨a, ha⟩ := hcover x
    refine ⟨a, hrange a ?_⟩
    change x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I a)))
    rw [range_comap_of_surjective (A ⧸ I a) (Ideal.Quotient.mk (I a))
      Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact ha
  have : ∀ a : ι, Flat (closedModelLiftMap A (Cbar a)) := fun a ↦ (hweak a).1
  have : IsAffine (∐ fun a : ι ↦ Spec (.of (Algebra.ClosedLift A (Cbar a)))) :=
    inferInstance
  have : Surjective (Sigma.desc (fun a : ι ↦ closedModelLiftMap A (Cbar a))) := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha⟩ := hsurj x
    exact Set.mem_iUnion.mpr ⟨a, ha⟩
  have : Flat (Sigma.desc (fun a : ι ↦ closedModelLiftMap A (Cbar a))) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  refine ⟨fun a ↦ ⟨(halg a).1, (halg a).2.1, (halg a).2.2,
    (hmodels a).1, (hmodels a).2, hweak a, hrange a⟩,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  let E : PreZeroHypercover (Spec (.of A)) :=
    ⟨ι, fun a ↦ Spec (.of (Algebra.ClosedLift A (Cbar a))),
      fun a ↦ closedModelLiftMap A (Cbar a)⟩
  have : ∀ a, QuasiCompact (E.f a) := fun _ ↦ inferInstance
  have hE : QuasiCompactCover E :=
    ⟨fun {U} hU ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun a ↦ (E.f a).isSpectralMap) (fun x _ ↦ hsurj x) U.2 hU.isCompact⟩
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hE,
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mpr ⟨hsurj, hweak⟩⟩

end AlgebraicGeometry.ProEtale
