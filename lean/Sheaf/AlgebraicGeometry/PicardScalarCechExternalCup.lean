/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.AlgebraicGeometry.PicardScalarCechComparison
public import Sheaf.AlgebraicGeometry.PicardExternalCechCupComponent
import Sheaf.AlgebraicGeometry.PicardModuleCechExternalCup
import Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility
import Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison

/-! # Scalar Cech external cup and canonical comparison

Source: Stacks Project, Tags 01FD, 07MB, 0FKV, and 0BED.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] moduleCohomologyPullback

set_option maxHeartbeats 800000 in
-- Comparing the scalar and module homology carriers needs additional unification.
/-- Core scalar Cech compatibility for genuine covers.
Source: Stacks, Tags 01FD, 07MB, 0FKV and 0BED.
(blueprint: lem-sc-picard-scalar-cech-external-cup-core).
Proof: Eliminate the degree equality, extract the three ordinary comparison
witnesses, and choose the uniquely characterized module cup. Naturality of cycle
inclusion and the homology projection identifies the image cycle and class.
Apply the module Cech comparison in that bidegree, then the scalar/module pullback
and cup identifications. The cover hypotheses are necessary to make comparisons
canonical; the earlier unrestricted formulation was incorrect. -/
theorem picardScalarCech_externalCup_core
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCechCupComponent f g U V F G c)
    (eX : ∀ p : ℕ, ((picardCechFunctor f U).obj F).homology p →ₗ[k]
      scalarCohomology f F p)
    (heX : ∀ p, IsPicardScalarCechComparison f U F p (eX p))
    (eY : ∀ q : ℕ, ((picardCechFunctor g V).obj G).homology q →ₗ[k]
      scalarCohomology g G q)
    (heY : ∀ q, IsPicardScalarCechComparison g V G q (eY q))
    (eP : ∀ n : ℕ,
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology n →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
    (heP : ∀ n, IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) n (eP n)) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
    T.iCycles n z = HomologicalComplex.ιMapBifunctor A B
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ) i.val.1 i.val.2 n
        i.property ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
      eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v))) := by
  classical
  dsimp
  intro n i a v z hz
  obtain ⟨⟨p, q⟩, hi⟩ := i
  dsimp at hi a v hz ⊢
  subst n
  simp only [cast_eq]
  obtain ⟨cF, hcF, heF⟩ := heX p
  obtain ⟨cG, hcG, heG⟩ := heY q
  obtain ⟨cP, hcP, heP'⟩ := heP (p + q)
  obtain ⟨cup, hcup, _⟩ := exists_unique_moduleCupProduct
    ((tensorPullback (pullback.fst f g)).obj F)
    ((tensorPullback (pullback.snd f g)).obj G) p q
  let A := (picardCechFunctor f U).obj F
  let B := (picardCechFunctor g V).obj G
  let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
    (ComplexShape.up ℕ)
  let l := HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
    (ComplexShape.up ℕ) p q (p + q) rfl ≫ c.f (p + q)
  have hl : IsPicardExternalCechCupBidegree f g U V F G p q l := hc p q
  let t := HomologicalComplex.cyclesMap c (p + q) z
  have ht : ((picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).iCycles (p + q) t =
      l ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q v)) := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i c (p + q)) z
    change _ = c.f (p + q) (T.iCycles (p + q) z) at h
    rw [hz] at h
    exact h
  have hclass := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality c (p + q)) z
  change HomologicalComplex.homologyMap c (p + q) (T.homologyπ (p + q) z) =
    ((picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).homologyπ (p + q) t at hclass
  rw [hclass, ← heP']
  rw [picardModuleCech_externalCup f g F G U V hUc hVc p q
    cF hcF cG hcG cP hcP cup hcup l hl a v t ht, heF, heG]
  have hx := scalar_moduleCohomologyPullback_comparison f (pullback.fst f g ≫ f)
    (pullback.fst f g) rfl F p (eX p (A.homologyπ p a))
  have hy := scalar_moduleCohomologyPullback_comparison g (pullback.fst f g ≫ f)
    (pullback.snd f g) pullback.condition.symm G q (eY q (B.homologyπ q v))
  exact (congrArg₂ (fun x y ↦ cup x y) hx.symm hy.symm).trans
    (scalarCup_moduleCup_compatibility (pullback.fst f g ≫ f) _ _ p q cup hcup _ _).symm

/-- Canonical scalar Cech comparisons identify the natural-degree external cup.
No scalar resolution, extension by zero, or affine comparison existence occurs here.
Source: Stacks, Tags 01FD and 0FKV; Tag 0BED, equation-kunneth-on-cech
(blueprint: lem-sc-picard-scalar-cech-external-cup).

Proof: Pull back the factor covers along the two projections and refine them to
the product cover. The component coordinates are exactly the front/back Cech cup
of these two refinement maps, by the tensor-pullback adjunction unit formula.
Apply refinement/pullback compatibility (01FD) to the two factor cocycles, then
Cech/sheaf cup compatibility (0FKV) on the product cover. Forgetting scalars gives
the canonical module comparison squares. Their scalar restrictions give the same
squares over k: on each section r acts through the structure map. The scalar Ext
comparison defining externalCup is identified on injective-resolution cocycles:
moduleExtEquiv sends a class to the unit-module morphism evaluated at 1. Exact
scalar restriction preserves this morphism and its cocycle equation. The scalar
pullback coefficient has adjoint the tensor-pullback unit, and the scalar tensor
coefficient sends pure tensors to tmulSection. Hence their pullback and tensor
operations on these representatives are scalarCohomologyPullback and
scalarCohomologyCup, whose composition is externalCup of the factor classes. The cycle
inclusion hypothesis identifies the image cycle with this front/back cocycle;
monicity of the cycle inclusion removes the choice of representative. For p+q=n,
transport along the degree equality gives the displayed cast. Empty covers and
zero coefficients have zero cycles; for p=q=0 this is the section tensor pairing. -/
theorem picardScalarCech_externalCup
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCechCupComponent f g U V F G c)
    (eX : ∀ p : ℕ, ((picardCechFunctor f U).obj F).homology p →ₗ[k]
      scalarCohomology f F p)
    (heX : ∀ p, IsPicardScalarCechComparison f U F p (eX p))
    (eY : ∀ q : ℕ, ((picardCechFunctor g V).obj G).homology q →ₗ[k]
      scalarCohomology g G q)
    (heY : ∀ q, IsPicardScalarCechComparison g V G q (eY q))
    (eP : ∀ n : ℕ,
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology n →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
    (heP : ∀ n, IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) n (eP n)) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
      (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
      T.iCycles n z =
        HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) i.val.1 i.val.2 n i.property
            ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
      eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v))) := by
  classical
  dsimp
  intro n i a v z hz
  exact picardScalarCech_externalCup_core f g F G U V hUc hVc c hc eX heX eY heY eP heP n i a v z hz

end AlgebraicGeometry.Scheme.Modules
