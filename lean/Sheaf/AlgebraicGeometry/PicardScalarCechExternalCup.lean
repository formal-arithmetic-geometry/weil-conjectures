/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.AlgebraicGeometry.PicardScalarCechComparison
public import Sheaf.AlgebraicGeometry.PicardExternalCechCupComponent
import Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing
import Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison

/-! # Scalar Cech external cup and canonical comparison

Source: Stacks Project, Tags 01FD, 07MB, 0FKV, and 0BED.
-/

@[expose] public section
set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

-- STATEMENT-DISPUTED: picardScalarCech_externalCup_core omitted the cover hypotheses.
-- Outside a cover, IsModuleCechComparison need not determine a unique comparison.
-- The false core is withdrawn; the cover theorem uses its own hypotheses directly.

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
  dsimp only
  intro n ⟨⟨p, q⟩, hpq⟩ a b z hz
  dsimp only at hpq
  subst n
  obtain ⟨cX, hcX, hX⟩ := heX p
  obtain ⟨cY, hcY, hY⟩ := heY q
  obtain ⟨cP, hcP, hP⟩ := heP (p + q)
  obtain ⟨cup, hcup, _⟩ := exists_unique_moduleCupProduct
    ((tensorPullback (pullback.fst f g)).obj F)
    ((tensorPullback (pullback.snd f g)).obj G) p q
  let A := (picardCechFunctor f U).obj F
  let B := (picardCechFunctor g V).obj G
  let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
    (ComplexShape.up ℕ)
  let W := fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
    pullback.snd f g ⁻¹ᵁ V ij.2
  let P := (picardCechFunctor (pullback.fst f g ≫ f) W).obj
    (externalCupCoefficients f g F G)
  let t : P.cycles (p + q) := HomologicalComplex.cyclesMap c (p + q) z
  have ht : P.iCycles (p + q) t =
      (HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q (p + q) rfl ≫ c.f (p + q))
          ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b)) := by
    have hi := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i c (p + q)) z
    change P.iCycles (p + q) t = c.f (p + q) (T.iCycles (p + q) z) at hi
    rw [hi, hz]
    rfl
  have hpair := picardModuleCech_externalPairing f g F G U V hUc hVc p q
    (HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ) p q (p + q) rfl ≫ c.f (p + q))
    (by
      intro x y u
      simpa only [ConcreteCategory.comp_apply, cupFront, cupBack, n2CupFront, n2CupBack]
        using hc p q x y u)
    cX hcX cY hcY cP hcP cup hcup a b t ht
  have hclass : HomologicalComplex.homologyMap c (p + q) (T.homologyπ (p + q) z) =
      P.homologyπ (p + q) t :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality c (p + q)) z
  rw [hclass, ← hP, hpair, hX, hY]
  exact (scalarExternalCup_moduleComparison f g F G p q cup hcup _ _).symm

end AlgebraicGeometry.Scheme.Modules
