/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups S3 and V2
-/
module

public import Sheaf.AlgebraicGeometry.PicardScalarCechComparison
public import Sheaf.AlgebraicGeometry.PicardExternalCechCupComponent
import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
import Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing
import Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison

/-! # Scalar Cech external cup and canonical comparison

Source: Stacks Project, Tags 01FD, 07MB, 0FKV, and 0BED.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
-- Keep the derived cohomology and coefficient constructions folded during equality glue.
attribute [local irreducible] tensorPullback tensorPullbackObj
  RingedSpace.moduleCohomology moduleCohomologyFMap moduleCohomologyPullback

/-- Equality of either input preserves a bilinear pairing. -/
private theorem moduleCup_congr {R : Type w} [CommRing R]
    {M N L : ModuleCat.{w} R} (cup : M →ₗ[R] N →ₗ[R] L)
    {x x' : M} {y y' : N} (hx : x = x') (hy : y = y') :
    cup x y = cup x' y' := by
  simp [hx, hy]

/-- Canonical comparison of the external Cech cup on open covers.
The cover equalities are essential: without them IsModuleCechComparison does not
fix how classes extend outside the union of the opens.
Source: Stacks Project, Tags 01FD, 07MB, 0FKV and 0BED.
(blueprint: lem-sc-picard-scalar-cech-external-cup-core).

Proof: Form the bidegree component by the tensor summand inclusion followed by c.
Its front/back coordinates follow from hc. Apply cyclesMap c to z; cyclesMap_i
and the inclusion hypothesis give the bidegree pairing of the factor cycles.
Homology naturality identifies its class with H(c)([z]). Extract the three
ordinary module comparison witnesses from heX, heY and heP. The ordinary module
external-pairing comparison gives the cup of the module pullback classes.
Their witness equations replace the factor and product comparisons by eX, eY
and eP. The scalar Ext/module external-cup comparison identifies that ordinary
cup, multiplied by (-1)^(p*q), with externalCup of the two factor classes.
Compose the equalities and
eliminate the degree equality p+q=n. No comparison isomorphism is assumed. -/
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
      (-1 : ℤ) ^ (i.val.1 * i.val.2) •
          eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v))) := by
  classical
  dsimp only
  intro n i a v z hz
  rcases i with ⟨⟨p, q⟩, hpq⟩
  dsimp only at hpq a v hz ⊢
  subst n
  let A := (picardCechFunctor f U).obj F
  let B := (picardCechFunctor g V).obj G
  let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
    (ComplexShape.up ℕ)
  let W := fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
    pullback.snd f g ⁻¹ᵁ V ij.2
  let E := externalCupCoefficients f g F G
  let P := (picardCechFunctor (pullback.fst f g ≫ f) W).obj E
  let h := HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
    (ComplexShape.up ℕ) p q (p + q) rfl ≫ c.f (p + q)
  have hh : IsPicardExternalCechCupBidegree f g U V F G p q h := by
    intro x y t
    exact hc p q x y t
  let t := HomologicalComplex.cyclesMap c (p + q) z
  have ht : P.iCycles (p + q) t =
      h ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q v)) := by
    have hi := congrArg (fun m ↦ m z) (HomologicalComplex.cyclesMap_i c (p + q))
    change P.iCycles (p + q) t = c.f (p + q) (T.iCycles (p + q) z) at hi
    rw [hi, hz]
    rfl
  have hclass : HomologicalComplex.homologyMap c (p + q) (T.homologyπ (p + q) z) =
      P.homologyπ (p + q) t := by
    simpa only [ModuleCat.comp_apply] using
      ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality c (p + q)) z
  obtain ⟨cX, hcX, hx⟩ := heX p
  obtain ⟨cY, hcY, hy⟩ := heY q
  obtain ⟨cP, hcP, htP⟩ := heP (p + q)
  obtain ⟨cup, hcup, _⟩ := exists_unique_moduleCupProduct
    ((tensorPullback (pullback.fst f g)).obj F)
    ((tensorPullback (pullback.snd f g)).obj G) p q
  have hmodule := picardModuleCech_externalPairing f g F G U V hUc hVc p q
    h hh cX hcX cY hcY cP hcP cup hcup a v t ht
  have hx' := hx (A.homologyπ p a)
  have hy' := hy (B.homologyπ q v)
  have htP' := htP (P.homologyπ (p + q) t)
  have hxPull := congrArg
    (fun x ↦ moduleCohomologyPullback (pullback.fst f g) F p x) hx'
  have hyPull := congrArg
    (fun y ↦ moduleCohomologyPullback (pullback.snd f g) G q y) hy'
  have hpaired := moduleCup_congr (R := Γ(Limits.pullback f g, ⊤))
    (M := (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace p).obj
      ((tensorPullback (pullback.fst f g)).obj F))
    (N := (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace q).obj
      ((tensorPullback (pullback.snd f g)).obj G))
    (L := (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj E)
    cup hxPull hyPull
  have hm := hmodule.trans hpaired
  have hscalar := htP'.symm.trans hm
  have he := (scalarExternalCup_moduleComparison f g F G p q cup hcup
    (eX p (A.homologyπ p a)) (eY q (B.homologyπ q v))).symm
  have he' := (congrArg (fun x ↦ (-1 : ℤ) ^ (p * q) • x)
    ((congrArg (eP (p + q)) hclass).trans hscalar)).trans he
  exact he'


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
scalarCohomologyCup, whose composition is the signed ordinary external cup of
the factor classes. The cycle
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
      (-1 : ℤ) ^ (i.val.1 * i.val.2) •
          eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v))) := by
  exact picardScalarCech_externalCup_core f g F G U V hUc hVc c hc eX heX eY heY eP heP

end AlgebraicGeometry.Scheme.Modules
