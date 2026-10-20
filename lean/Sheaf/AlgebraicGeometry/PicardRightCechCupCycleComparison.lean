/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.PicardRightCechCupConstruction
public import WeilConjectures.AlgebraicGeometry.PicardKunnethResolutionModel
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Geometric comparison on external Cech tensor cocycles

Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; Tags 01FD, 07MB, 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-cycle-comparison).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

private theorem affineIntersections
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsAffineHom (pullback.diagonal f)]
    {ι : Type w} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (n : ℕ) (y : Fin (n + 1) → ι) : IsAffineOpen (⨅ l, U (y l)) := by
  apply InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen)
  · intro A hA B hB
    exact (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _)
      A (by simp) B (by simp) hA hB
  · intro l
    exact hU (y l)

private theorem tensorPullback_qcoh {X Y : Scheme.{w}} (a : X ⟶ Y)
    (F : Y.Modules) [F.IsQuasicoherent] : ((tensorPullback a).obj F).IsQuasicoherent := by
  let e := (nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (pullbackPushforwardAdjunction a)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (e.app F).symm (isQuasicoherent_pullback a F)

private theorem extendHomology_cancel
    {k : Type w} [Field k] {K L : CochainComplex (ModuleCat.{w} k) ℕ}
    (c : K ⟶ L) (n : ℕ) (x : K.homology n) :
    (L.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom
      (HomologicalComplex.homologyMap (HomologicalComplex.extendMap c
        ComplexShape.embeddingUpNat) (n : ℤ)
        ((K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv x)) =
      HomologicalComplex.homologyMap c n x := by
  have h := HomologicalComplex.extendHomologyIso_hom_naturality c
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  have h' := congrArg (fun m ↦
    (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv ≫ m) h
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h'
  exact ConcreteCategory.congr_hom h' x

/-- Factor and product affine comparisons identify the specified external Cech
cup on tensor cocycles. This asserts no tensor Kunneth equivalence.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech and the sentence
identifying its cohomology map; Cohomology Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-cycle-comparison).

Proof: Affine relative diagonals make every nonempty finite intersection of the
factor covers affine. The intersections of the product cover are fibre products
of these affine intersections over Spec k, hence affine. The product opens cover
the fibre product. The external coefficient is quasi-coherent by pullback and
tensor quasi-coherence. Apply the canonical affine Cech comparisons to both
factor coefficients and the product coefficient. Restriction of scalars is
exact and commutes with the products in each Cech term, so the comparisons are
k-linear. Compose the factor comparisons with the inverse fixed scalar-model
comparisons to get alpha and beta. For the product also use the zero-extension
homology isomorphism, giving b. The signed canonical Cech cup formula then
identifies (-1)^(p*q) times the product comparison with externalCup. The next
comparison on homology generators absorbs this factor in each tensor summand.
For factor cocycles a and v, the inclusion of z is the tensor of their inclusions
in the indicated total summand. The htheta coordinates compute its image on each
product-cover tuple as the front X section and back Y section pulled back by the
projection adjunction units and tensored. The projection refinements followed by
Cech cup have exactly these coordinates. Tag 01FD identifies the refinement maps
with pullback on cohomology, and Tag 0FKV identifies Cech cup with sheaf cup.
The fixed scalar-resolution comparison and its Ext identification give precisely
externalCup of the two displayed factor classes. Extension homology transports
this class to the integer complex without changing the natural-degree formula.
The degree cast implements p+q=n. Monicity of iCycles makes the assertion hold
for every z with the given inclusion. Empty covers force empty factors, and zero
coefficients give zero classes. In degree zero this is the section tensor pairing.
No invertibility of external cup, or tensor-total Kunneth, is used. -/
theorem picardRightCechCup_cycle_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F)
    (hθ : IsPicardRightCechCup f g U V F θ)
    (G : Y.Modules) [G.IsQuasicoherent] :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∃ (alpha : ∀ p : ℕ, A.homology p ≃ₗ[k] (picardScalarModel f F).homology (p : ℤ))
      (beta : ∀ q : ℕ, B.homology q ≃ₗ[k] (picardScalarModel g G).homology (q : ℤ))
      (b : ∀ n : ℕ,
        ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
          (picardScalarModel (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G)).homology (n : ℤ)),
      ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
        (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
        T.iCycles n z =
          HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ) i.val.1 i.val.2 n i.property
              ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
        (-1 : ℤ) ^ (i.val.1 * i.val.2) •
          picardScalarModelEquiv (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) n
          ((b n).hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
            ((T.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv
              (T.homologyπ n z)))) =
          cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) d)) i.property)
            (externalCup f g F G i.val.1 i.val.2
              (picardScalarModelEquiv f F i.val.1 (alpha i.val.1 (A.homologyπ _ a)))
              (picardScalarModelEquiv g G i.val.2 (beta i.val.2 (B.homologyπ _ v)))) :=
  by
  classical
  let A := (picardCechFunctor f U).obj F
  let B := (picardCechFunctor g V).obj G
  let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
    (ComplexShape.up ℕ)
  let W : ι × κ → (Limits.pullback f g).Opens := fun ij ↦
    pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2
  let E := externalCupCoefficients f g F G
  let P := (picardCechFunctor (pullback.fst f g ≫ f) W).obj E
  have hW : ∀ (n : ℕ) (y : Fin (n + 1) → ι × κ), IsAffineOpen (⨅ l, W (y l)) := by
    intro n y
    have heq : (⨅ l, W (y l)) =
        pullback.fst f g ⁻¹ᵁ (⨅ l, U (y l).1) ⊓
          pullback.snd f g ⁻¹ᵁ (⨅ l, V (y l).2) := by
      ext x
      simp only [W, TopologicalSpace.Opens.coe_iInf, TopologicalSpace.Opens.coe_inf,
        Scheme.Hom.coe_preimage, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
      exact forall_and
    rw [heq]
    exact isAffineOpen_preimage_inf_preimage_pullback f g
      (affineIntersections f U hU n (fun l ↦ (y l).1))
      (affineIntersections g V hV n (fun l ↦ (y l).2))
  have hWc : iSup W = ⊤ := by
    apply top_unique
    intro x hx
    have hxU : pullback.fst f g x ∈ iSup U := by rw [hUc]; trivial
    have hxV : pullback.snd f g x ∈ iSup V := by rw [hVc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩
  have : ((tensorPullback (pullback.fst f g)).obj F).IsQuasicoherent :=
    tensorPullback_qcoh _ F
  have : ((tensorPullback (pullback.snd f g)).obj G).IsQuasicoherent :=
    tensorPullback_qcoh _ G
  have : E.IsQuasicoherent := (quasiCoherent_tensor_product_affine_sections _ _).1
  choose eX heX using fun p ↦
    picardScalarCechComparison_exists f U (affineIntersections f U hU) hUc F p
  choose eY heY using fun q ↦
    picardScalarCechComparison_exists g V (affineIntersections g V hV) hVc G q
  choose eP heP using fun n ↦
    picardScalarCechComparison_exists (pullback.fst f g ≫ f) W hW hWc E n
  let alpha := fun p ↦ (eX p).trans (picardScalarModelEquiv f F p).symm
  let beta := fun q ↦ (eY q).trans (picardScalarModelEquiv g G q).symm
  let b := fun n : ℕ ↦ (P.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl) ≪≫
    (eP n).toModuleIso ≪≫ (picardScalarModelEquiv (pullback.fst f g ≫ f) E n).symm.toModuleIso
  refine ⟨alpha, beta, b, ?_⟩
  intro n i a v z hz
  obtain ⟨c, hθc, hc⟩ := hθ G
  have hcup := picardScalarCech_externalCup f g F G U V hUc hVc c hc
    (fun p ↦ (eX p).toLinearMap) heX (fun q ↦ (eY q).toLinearMap) heY
    (fun j ↦ (eP j).toLinearMap) heP n i a v z hz
  dsimp only [alpha, beta, LinearEquiv.trans_apply] at *
  simp only [LinearEquiv.apply_symm_apply]
  change (-1 : ℤ) ^ (i.val.1 * i.val.2) •
    (picardScalarModelEquiv (pullback.fst f g ≫ f) E n)
      ((b n).hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
        ((T.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv
          (T.homologyπ n z)))) = _
  rw [hθc]
  change (-1 : ℤ) ^ (i.val.1 * i.val.2) •
    (picardScalarModelEquiv (pullback.fst f g ≫ f) E n)
      ((picardScalarModelEquiv (pullback.fst f g ≫ f) E n).symm
        (eP n ((P.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom
          (HomologicalComplex.homologyMap (HomologicalComplex.extendMap c
            ComplexShape.embeddingUpNat) (n : ℤ)
            ((T.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv
              (T.homologyπ n z)))))) = _
  rw [LinearEquiv.apply_symm_apply, extendHomology_cancel]
  exact hcup

end AlgebraicGeometry.Scheme.Modules
