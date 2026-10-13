/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.PicardKunnethResolutionModel
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

import Sheaf.Algebra.Homology.TensorKunnethNat
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Cochain realization of the external cup product

Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV; Varieties, Tag 0BED.
(blueprint: lem-sc-picard-external-cup-cochain).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The tensor total complex of the two actual scalar sections models.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-cochain). -/
noncomputable abbrev picardExternalTotal
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) : CochainComplex (ModuleCat.{w} k) ℤ :=
  HomologicalComplex.mapBifunctor (picardScalarModel f F) (picardScalarModel g G)
    (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)

/-- Normalization of a specified cochain map on tensor cycles. This imposes only the
external cup formula, not injectivity or surjectivity on homology.
Source: Stacks, Tags 01FD, 07MB and 0FKV; equation 33.29.1.1 of Tag 0BED
(blueprint: lem-sc-picard-external-cup-cochain). -/
def IsPicardExternalCupCochain
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)) : Prop :=
  ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : (picardScalarModel f F).cycles (i.val.1 : ℤ))
    (b : (picardScalarModel g G).cycles (i.val.2 : ℤ))
    (z : (picardExternalTotal f g F G).cycles (n : ℤ)),
    (picardExternalTotal f g F G).iCycles (n : ℤ) z =
      HomologicalComplex.ιMapBifunctor (picardScalarModel f F) (picardScalarModel g G)
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
        (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ) (by
          change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
          exact_mod_cast i.property)
        (((picardScalarModel f F).iCycles (i.val.1 : ℤ) a) ⊗ₜ[k]
          ((picardScalarModel g G).iCycles (i.val.2 : ℤ) b)) →
    picardScalarModelEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n
        (HomologicalComplex.homologyMap c (n : ℤ)
          ((picardExternalTotal f g F G).homologyπ (n : ℤ) z)) =
      cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) d)) i.property)
        (externalCup f g F G i.val.1 i.val.2
          (picardScalarModelEquiv f F i.val.1
            ((picardScalarModel f F).homologyπ (i.val.1 : ℤ) a))
          (picardScalarModelEquiv g G i.val.2
            ((picardScalarModel g G).homologyπ (i.val.2 : ℤ) b)))

private theorem lift_graded_homology
    (A C : CochainComplex (ModuleCat.{w} k) ℤ)
    (φ : ∀ n : ℤ, A.homology n ⟶ C.homology n) :
    ∃ c : A ⟶ C, ∀ n, HomologicalComplex.homologyMap c n = φ n := by
  classical
  have hr (n : ℤ) : ∃ r : A.X n ⟶ A.homology n,
      A.iCycles n ≫ r = A.homologyπ n := by
    let r := (A.homologyπ n).hom.comp (A.iCycles n).hom.leftInverse
    refine ⟨ModuleCat.ofHom r, ?_⟩
    ext x
    change (A.homologyπ n).hom ((A.iCycles n).hom.leftInverse
      ((A.iCycles n).hom x)) = (A.homologyπ n).hom x
    rw [LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp inferInstance))]
  have hs (n : ℤ) : ∃ s : C.homology n ⟶ C.cycles n,
      s ≫ C.homologyπ n = 𝟙 _ := by
    obtain ⟨s, hs⟩ := (C.homologyπ n).hom.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance))
    exact ⟨ModuleCat.ofHom s, ModuleCat.hom_ext hs⟩
  choose r hr using hr
  choose s hs using hs
  have hd (i j : ℤ) : A.d i j ≫ r j = 0 := by
    rw [← A.toCycles_i i j, Category.assoc, hr, A.toCycles_comp_homologyπ]
  let c : A ⟶ C :=
    { f := fun n ↦ r n ≫ φ n ≫ s n ≫ C.iCycles n
      comm' := by
        intro i j hij
        simp only [Category.assoc, C.iCycles_d, comp_zero]
        rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hd]
        simp }
  refine ⟨c, fun n ↦ ?_⟩
  rw [← cancel_epi (A.homologyπ n), HomologicalComplex.homologyπ_naturality]
  have hc : HomologicalComplex.cyclesMap c n = A.homologyπ n ≫ φ n ≫ s n := by
    rw [← cancel_mono (C.iCycles n), HomologicalComplex.cyclesMap_i]
    change A.iCycles n ≫ (r n ≫ φ n ≫ s n ≫ C.iCycles n) = _
    simp only [← Category.assoc, hr]
  rw [hc]
  simp only [Category.assoc, hs, Category.comp_id]

section
noncomputable section
set_option backward.isDefEq.respectTransparency.types true in
private local instance (Z : Scheme.{w}) : MonoidalCategory (KSheaf Z k) :=
  Sheaf.monoidalCategory _ _
set_option backward.isDefEq.respectTransparency.types true in
private local instance (Z : Scheme.{w}) : HasExt.{w + 1} (KSheaf Z k) :=
  HasExt.standard (KSheaf Z k)
set_option backward.isDefEq.respectTransparency.types true in
private local instance : MonoidalCategory (SheafOfModules.{w} X.ringCatSheaf) :=
  SheafOfModules.monoidalCategory X.sheaf
set_option backward.isDefEq.respectTransparency.types true in
private theorem equiv_smul (f : X ⟶ Spec (CommRingCat.of k))
    (F : SheafOfModules.{w} X.ringCatSheaf) (p : ℕ) (r : k)
    (x : scalarCohomology f F p) :
    scalarCohomologyExtEquiv f F p (r • x) = r • scalarCohomologyExtEquiv f F p x := by
  unfold scalarCohomologyExtEquiv
  exact scalarCohomologyExtMap_smul f F p r x
set_option backward.isDefEq.respectTransparency.types true in
private theorem linearEquiv_exists
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]
    (e : V ≃+ W) (h : ∀ (r : k) (x : V), e (r • x) = r • e x) :
    ∃ l : V ≃ₗ[k] W, (∀ x, l x = e x) ∧ (∀ y, l.symm y = e.symm y) := by
  exact ⟨e.toLinearEquiv h, fun _ ↦ rfl, fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency.types true in
private theorem cohomologyExtLinear_exists (f : X ⟶ Spec (CommRingCat.of k))
    (F : SheafOfModules.{w} X.ringCatSheaf) (n : ℕ) :
    ∃ e : scalarCohomology f F n ≃ₗ[k]
        Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n,
      (∀ x, e x = scalarCohomologyExtEquiv f F n x) ∧
        (∀ y, e.symm y = (scalarCohomologyExtEquiv f F n).symm y) := by
  exact linearEquiv_exists _ (equiv_smul f F n)

set_option backward.isDefEq.respectTransparency.types true in
private theorem pullbackLinear_exists (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
    (F : X.Modules) (n : ℕ) :
    ∃ l : scalarCohomology f F n →ₗ[k] scalarCohomology g ((tensorPullback a).obj F) n,
      ∀ x, l x = scalarCohomologyPullback f g a h F n x := by
  let : ((TopologicalSpace.Opens.map a.base).sheafPushforwardContinuous (ModuleCat.{w} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).Linear k :=
    ⟨by intros; rfl⟩
  let : (scalarInverseImage (k := k) a).Linear k :=
    ((TopologicalSpace.Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).left_adjoint_linear
  obtain ⟨e, he, _⟩ := cohomologyExtLinear_exists f F n
  obtain ⟨e', _, he'⟩ := cohomologyExtLinear_exists g ((tensorPullback a).obj F) n
  let I := scalarInverseImage (k := k) a
  let L := I.mapExtLinearMap k (𝟙_ (KSheaf X k)) (scalarSheaf f F) n
  let α := Abelian.Ext.mk₀ (scalarInverseUnitIso (k := k) a).inv
  let β := Abelian.Ext.mk₀ (scalarPullbackCoefficient f g a h F)
  refine ⟨e'.symm.toLinearMap.comp
    (((Abelian.Ext.bilinearCompOfLinear k _ _ _ _ _ _ (add_zero n)).flip β).comp
      ((Abelian.Ext.bilinearCompOfLinear k _ _ _ _ _ _ (zero_add n) α).comp
        (L.comp e.toLinearMap))), ?_⟩
  intro x
  change e'.symm ((α.comp ((e x).mapExactFunctor I) (zero_add n)).comp β (add_zero n)) = _
  rw [he', he]
  unfold scalarCohomologyPullback
  rfl

set_option backward.isDefEq.respectTransparency.types true in
private theorem cupLinear_exists (f : X ⟶ Spec (CommRingCat.of k))
    (F G : X.Modules) (p q : ℕ) :
    ∃ b : scalarCohomology f F p →ₗ[k] scalarCohomology f G q →ₗ[k]
        scalarCohomology f (F ⊗ G) (p + q),
      ∀ x y, b x y = scalarCohomologyCup f F G p q x y := by
  obtain ⟨eF, heF, _⟩ := cohomologyExtLinear_exists f F p
  obtain ⟨eG, heG, _⟩ := cohomologyExtLinear_exists f G q
  obtain ⟨eH, _, heH⟩ := cohomologyExtLinear_exists f (F ⊗ G) (p + q)
  let P := scalarSheaf f F
  let Q := scalarSheaf f G
  let L := (tensorRight (𝟙_ (KSheaf X k))).mapExtLinearMap k (𝟙_ (KSheaf X k)) P p
  let M := (tensorLeft P).mapExtLinearMap k (𝟙_ (KSheaf X k)) Q q
  let α := Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf X k))).inv
  let β := Abelian.Ext.mk₀ (scalarTensorCoefficient f F G)
  let B := (Abelian.Ext.bilinearCompOfLinear k _ _ _ _ _ _ (rfl : p + q = p + q)).compl₁₂
    ((Abelian.Ext.bilinearCompOfLinear k _ _ _ _ _ _ (zero_add p) α).comp L) M
  let N := eH.symm.toLinearMap.comp
    ((Abelian.Ext.bilinearCompOfLinear k _ _ _ _ _ _ (add_zero (p + q))).flip β)
  refine ⟨(B.compr₂ N).compl₁₂ eF.toLinearMap eG.toLinearMap, ?_⟩
  intro x y
  change eH.symm (((α.comp ((eF x).mapExactFunctor (tensorRight (𝟙_ (KSheaf X k))))
    (zero_add p)).comp ((eG y).mapExactFunctor (tensorLeft P)) rfl).comp β (add_zero _)) = _
  rw [heH, heF, heG]
  unfold scalarCohomologyCup scalarExtCup
  rfl

set_option backward.isDefEq.respectTransparency.types true in
private theorem externalCup_bilinear (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (G : Y.Modules) (p q : ℕ) :
    ∃ b : scalarCohomology f F p →ₗ[k] scalarCohomology g G q →ₗ[k]
      scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) (p + q),
      ∀ x y, b x y = externalCup f g F G p q x y := by
  let P := (tensorPullback (pullback.fst f g)).obj F
  let Q := (tensorPullback (pullback.snd f g)).obj G
  obtain ⟨L, hL⟩ := pullbackLinear_exists f (pullback.fst f g ≫ f)
    (pullback.fst f g) rfl F p
  obtain ⟨M, hM⟩ := pullbackLinear_exists g (pullback.fst f g ≫ f)
    (pullback.snd f g) pullback.condition.symm G q
  obtain ⟨cup, hcup⟩ := cupLinear_exists (pullback.fst f g ≫ f) P Q p q
  refine ⟨cup.compl₁₂ L M, ?_⟩
  intro x y
  change cup (L x) (M y) = _
  rw [hcup, hL, hM]
  rfl
end
end

/-- External cup admits a cochain realization between the explicitly constructed models.
This asserts no geometric Kunneth isomorphism and needs no compactness or affine diagonal.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV;
Varieties, Tag 0BED, construction before equation 33.29.1.1
(blueprint: lem-sc-picard-external-cup-cochain).

Proof: Resolve the coefficient sheaves, compute the projection pullbacks on resolution
representatives, and use the signed tensor pairing of Tag 0FKV followed by the
coefficient map from derived tensor to ordinary tensor. Tags 01FD and 07MB identify
this pairing on cocycle tensors with pullback followed by cup. The scalar Ext
comparison identifies it with the recorded externalCup operation, k-bilinearly.
To obtain a map on the fixed sections models rather than on a Godement model,
use the following explicit vector-space lifting argument. In each degree choose a
complement of boundaries in cycles and a complement of cycles in the term. The
latter complement maps isomorphically onto the next boundaries. Thus each complex
is the direct sum of its homology representatives with zero differential and pairs
mapped isomorphically by the differential. Projection to the homology representatives
and inclusion of them are cochain maps inducing the identity on homology. The field
linear tensor Kunneth map identifies homology of the tensor total with the sum of
factor homology tensors. Define a map on that homology by the bilinear external cup
on each summand, using picardScalarModelEquiv on all three models; include it into
the homology representatives of the product model. Composing with projection of
the tensor total gives the required cochain map c. Its homology map has exactly the
specified value on every tensor cycle by the tensor Kunneth cycle formula.
If two total cycles have the specified inclusion, monicity of iCycles identifies
them, so the formula holds for the arbitrary z in the statement. All negative
terms are zero, and the construction includes zero sheaves and empty schemes. -/
theorem picardExternalCupCochain_exists
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ∃ c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G),
      IsPicardExternalCupCochain f g F G c := by
  classical
  let A := picardScalarModel f F
  let B := picardScalarModel g G
  let C := picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
  let T := picardExternalTotal f g F G
  have hcup := fun p q ↦ externalCup_bilinear f g F G p q
  choose cup hcup using hcup
  have hK := fun n ↦ HomologicalComplex.tensor_kunneth_nat A B
    (picardScalarModel_negative f F) (picardScalarModel_negative g G) n
  choose e he using hK
  let σ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
      (A.homology (i.val.1 : ℤ)) ⊗[k] (B.homology (i.val.2 : ℤ)) →ₗ[k]
        C.homology (n : ℤ) :=
    (picardScalarModelEquiv (pullback.fst f g ≫ f)
      (externalCupCoefficients f g F G) n).symm.toLinearMap.comp
        ((LinearEquiv.cast (R := k)
          (M := fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) d)) i.property).toLinearMap.comp
          ((TensorProduct.lift (cup i.val.1 i.val.2)).comp
            (TensorProduct.map (picardScalarModelEquiv f F i.val.1).toLinearMap
              (picardScalarModelEquiv g G i.val.2).toLinearMap)))
  let τ (n : ℕ) := DirectSum.toModule k _ _ (σ n)
  let φnat (n : ℕ) : T.homology (n : ℤ) ⟶ C.homology (n : ℤ) :=
    ModuleCat.ofHom ((τ n).comp (e n).symm.toLinearMap)
  let φ : ∀ n : ℤ, T.homology n ⟶ C.homology n := fun n ↦
    match n with
    | .ofNat m => φnat m
    | .negSucc _ => 0
  obtain ⟨c, hc⟩ := lift_graded_homology T C φ
  refine ⟨c, ?_⟩
  intro n i a b z hz
  obtain ⟨z', hz', hez⟩ := he n i a b
  have hzz : z' = z :=
    ((ModuleCat.mono_iff_injective (T.iCycles (n : ℤ))).mp inferInstance)
      (hz'.trans hz.symm)
  subst z'
  change (picardScalarModelEquiv (pullback.fst f g ≫ f)
    (externalCupCoefficients f g F G) n)
      ((HomologicalComplex.homologyMap c (n : ℤ)) (T.homologyπ (n : ℤ) z)) = _
  rw [hc]
  change (picardScalarModelEquiv (pullback.fst f g ≫ f)
    (externalCupCoefficients f g F G) n)
      ((τ n) ((e n).symm (T.homologyπ (n : ℤ) z))) = _
  rw [← hez, LinearEquiv.symm_apply_apply]
  simp only [τ, DirectSum.toModule_lof]
  change (picardScalarModelEquiv (pullback.fst f g ≫ f)
    (externalCupCoefficients f g F G) n)
      ((picardScalarModelEquiv (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) n).symm
          ((LinearEquiv.cast (R := k)
            (M := fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G) d)) i.property)
                (TensorProduct.lift (cup i.val.1 i.val.2)
                  (TensorProduct.map (picardScalarModelEquiv f F i.val.1).toLinearMap
                    (picardScalarModelEquiv g G i.val.2).toLinearMap
                      ((A.homologyπ (i.val.1 : ℤ) a) ⊗ₜ[k]
                        (B.homologyπ (i.val.2 : ℤ) b)))))) = _
  rw [LinearEquiv.apply_symm_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul,
    hcup]
  rfl

end AlgebraicGeometry.Scheme.Modules
