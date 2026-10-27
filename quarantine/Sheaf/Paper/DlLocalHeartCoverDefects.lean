/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.Paper.DlLocallyConstructibleAdicHeart
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.IntrinsicQbarCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.Basic
public import Sheaf.Paper.AdicHeartIntrinsicFibres
import Sheaf.Paper.DlLocalHeartAbelianEvaluation
import Sheaf.Paper.DlLocalHeartCoverBasisZero

/-! # Local adic heart defects and detection by open covers

Source: Bhatt--Scholze, Section 6.8, Proposition 6.8.14 and Remark 6.8.15;
Stacks Project, Tag 04TQ, sites-lemma-glue-maps; blueprint p-dl-a1-exact,
proof Steps 1 and 5 (blueprint: lem-dl-a1-local-heart-cover-defects).

The category and evaluation functors are the existing cartesian local heart data.
Abelian structures are supplied in the conclusion, together with exact evaluation
and detection of the three defects on arbitrary separated finite-type open covers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (T : Over (Spec (.of D.k₀)))

/-- The abelian structures and componentwise defect assertions on the literal local category.
The heart on each open is the existing common-stage standard heart over k0; there is
no coefficient stage on T. The middle defect is the cokernel of the canonical
factorization into the kernel: this is ker(g)/im(f), with its cycle and quotient maps.
Source: BS Proposition 6.8.14, Remark 6.8.15 and Stacks Tag 04TQ
(blueprint: lem-dl-a1-local-heart-cover-defects). -/
structure DlLocalHeartCoverDefects where
  /-- The cartesian local heart is abelian. -/
  [localAbelian : Abelian (DlLocallyConstructibleAdicHeart D c T)]
  /-- Each component is the abelian common-stage standard heart over k0. -/
  [componentAbelian (U : DlAdicFiniteOpen D T) :
    Abelian (sfCommonStageHeart c.l U.val.toScheme c.Qbar)]
  /-- Evaluation is additive. -/
  evaluationAdditive : ∀ U : DlAdicFiniteOpen D T, (dlAdicLocalEvaluation D c T U).Additive
  /-- Evaluation is exact: it preserves finite limits. -/
  evaluationLimits : ∀ U : DlAdicFiniteOpen D T,
    PreservesFiniteLimits (dlAdicLocalEvaluation D c T U)
  /-- Evaluation is exact: it preserves finite colimits. -/
  evaluationColimits : ∀ U : DlAdicFiniteOpen D T,
    PreservesFiniteColimits (dlAdicLocalEvaluation D c T U)
  /-- The kernel comparison is the one commuting with the kernel inclusion. -/
  kernelComponents : ∀ (A B : DlLocallyConstructibleAdicHeart D c T) (f : A ⟶ B)
    (U : DlAdicFiniteOpen D T), IsIso (kernelComparison f (dlAdicLocalEvaluation D c T U))
  /-- The cokernel comparison is the one commuting with the quotient projection. -/
  cokernelComponents : ∀ (A B : DlLocallyConstructibleAdicHeart D c T) (f : A ⟶ B)
    (U : DlAdicFiniteOpen D T), IsIso (cokernelComparison f (dlAdicLocalEvaluation D c T U))
  /-- Homology is preserved with its canonical cycle and quotient maps. -/
  evaluationHomology : ∀ U : DlAdicFiniteOpen D T,
    (dlAdicLocalEvaluation D c T U).PreservesHomology
  /-- The middle defect evaluates to the corresponding component quotient. -/
  homologyComponents : ∀ (U : DlAdicFiniteOpen D T)
    (S : ShortComplex (DlLocallyConstructibleAdicHeart D c T)),
    Nonempty ((dlAdicLocalEvaluation D c T U).obj
      (cokernel (kernel.lift S.g S.f S.zero)) ≅
        cokernel (kernel.lift (S.map (dlAdicLocalEvaluation D c T U)).g
          (S.map (dlAdicLocalEvaluation D c T U)).f
          (S.map (dlAdicLocalEvaluation D c T U)).zero))
  /-- Exact sequences remain exact under evaluation. -/
  evaluationExact : ∀ (U : DlAdicFiniteOpen D T)
    (S : ShortComplex (DlLocallyConstructibleAdicHeart D c T)),
    S.Exact → (S.map (dlAdicLocalEvaluation D c T U)).Exact
  /-- Vanishing of an arbitrary local heart object is detected on any such open cover. -/
  coverZero : ∀ (I : Type w) (U : I → DlAdicFiniteOpen D T),
    (⨆ i : I, (U i).val) = ⊤ →
    ∀ K : DlLocallyConstructibleAdicHeart D c T,
      IsZero K ↔ ∀ i : I, IsZero ((dlAdicLocalEvaluation D c T (U i)).obj K)
  /-- The left kernel, middle homology and right cokernel vanish exactly when all
  corresponding evaluated defects on the cover vanish. -/
  coverDefects : ∀ (I : Type w) (U : I → DlAdicFiniteOpen D T),
    (⨆ i : I, (U i).val) = ⊤ →
    ∀ S : ShortComplex (DlLocallyConstructibleAdicHeart D c T),
      (IsZero (kernel S.f) ↔
        ∀ i : I, IsZero (kernel ((dlAdicLocalEvaluation D c T (U i)).map S.f))) ∧
      (IsZero (cokernel (kernel.lift S.g S.f S.zero)) ↔
        ∀ i : I, IsZero (cokernel
          (kernel.lift (S.map (dlAdicLocalEvaluation D c T (U i))).g
            (S.map (dlAdicLocalEvaluation D c T (U i))).f
            (S.map (dlAdicLocalEvaluation D c T (U i))).zero))) ∧
      (IsZero (cokernel S.g) ↔
        ∀ i : I, IsZero (cokernel ((dlAdicLocalEvaluation D c T (U i)).map S.g)))

/-- Local cartesian adic heart data form an abelian category with componentwise defects;
zero objects and all three defects are detected by arbitrary separated finite-type
open covers, without a global coefficient field or quasi-compactness assumption.
Source: BS Proposition 6.8.14, Remark 6.8.15; Stacks Tag 04TQ
(blueprint: lem-dl-a1-local-heart-cover-defects).

Proof:
1. On each basis open use the bounded standard heart over k0 and its abelianity
(lem-per-adic-heart-pullback-fibres, prop-weil-heart-abelian). Completed restrictions
are additive and exact on these hearts (lem-per-adic-stratified-pullback-texact),
with the given normalized compositors (def-dl-a1-locally-constructible-adic-heart).
2. Add compatible arrows componentwise. The zero family and componentwise binary
biproducts satisfy their universal properties and gluing equations componentwise.
3. For f, form its component kernels. Exact restriction preserves the kernel universal
property (lem-sp-exact-functor-preserves-homology); conjugate by the cartesian
comparisons. Cancel the monic kernel inclusions to prove the cocycle, identity
normalization and compatibility of every kernel lift. This is a global kernel.
4. Dually form component cokernels. Cancel the restricted epic quotient maps to prove
the cocycle, normalization and compatibility of factorizations. This is a global cokernel.
5. A global monomorphism has zero kernel. Hence its component kernels are zero, so
its components are monic and are kernels of their cokernels. Their unique component
factorizations are compatible by cancellation of the component monomorphisms.
6. Dually a global epimorphism has zero cokernel, its components are epic, and their
cokernel factorizations glue by epic cancellation. This proves the abelian axioms.
7. Evaluation is additive and preserves the constructed kernels and cokernels.
Thus it is exact and preserves images and homology with their canonical maps
(lem-sp-exact-functor-preserves-homology, def-weil-pbc-exact-sequence). The three
defects are objects of the cartesian local category with these evaluations.
8. If K is zero on a cover, choose at each geometric point of a basis open V a cover
member containing it and a basis neighbourhood W in their intersection. The
cartesian comparisons make K_W zero. The pullback-fibre comparison identifies the
fibre of K_V there with the zero fibre of K_W. Joint conservativity of geometric
fibres (lem-per-adic-heart-pullback-fibres) makes K_V zero for every V, hence K zero.
The reverse implication follows by evaluation. Apply this to each defect from step 7.
This argument uses no finite subcover and makes no single coefficient-field choice. -/
theorem dlLocalHeartCoverDefects [LocallyOfFiniteType T.hom] :
    Nonempty (DlLocalHeartCoverDefects.{u, w} D c T) := by
  classical
  obtain ⟨H⟩ := dlLocalHeartAbelianEvaluation D c T
  let localAbelian := H.localAbelian
  let componentAbelian := H.componentAbelian
  let evaluationAdditive := H.evaluationAdditive
  let evaluationLimits := H.evaluationLimits
  let evaluationColimits := H.evaluationColimits
  have hm (U : DlAdicFiniteOpen D T)
      (S : ShortComplex (DlLocallyConstructibleAdicHeart D c T)) :
      Nonempty ((dlAdicLocalEvaluation D c T U).obj
        (cokernel (kernel.lift S.g S.f S.zero)) ≅
          cokernel (kernel.lift (S.map (dlAdicLocalEvaluation D c T U)).g
            (S.map (dlAdicLocalEvaluation D c T U)).f
            (S.map (dlAdicLocalEvaluation D c T U)).zero)) := by
    let F := dlAdicLocalEvaluation D c T U
    exact ⟨F.mapIso S.leftHomologyIsoCokernelLift.symm ≪≫
      (S.mapLeftHomologyIso F).symm ≪≫ (S.map F).leftHomologyIsoCokernelLift⟩
  have hz (I : Type w) (U : I → DlAdicFiniteOpen D T)
      (hU : (⨆ i : I, (U i).val) = ⊤) (K : DlLocallyConstructibleAdicHeart D c T) :
      IsZero K ↔ ∀ i : I, IsZero ((dlAdicLocalEvaluation D c T (U i)).obj K) := by
    constructor
    · intro h i
      exact (dlAdicLocalEvaluation D c T (U i)).map_isZero h
    · intro h
      have hV := dlLocalHeartCoverBasisZero D c T I U hU K h
      apply (IsZero.iff_id_eq_zero K).mpr
      ext V
      exact congrArg (fun f ↦ f.hom) ((hV V).eq_of_src (𝟙 _) 0)
  refine ⟨{
    localAbelian := H.localAbelian
    componentAbelian := H.componentAbelian
    evaluationAdditive := H.evaluationAdditive
    evaluationLimits := H.evaluationLimits
    evaluationColimits := H.evaluationColimits
    kernelComponents := fun _ _ _ _ ↦ inferInstance
    cokernelComponents := fun _ _ _ _ ↦ inferInstance
    evaluationHomology := fun _ ↦ inferInstance
    homologyComponents := hm
    evaluationExact := fun U S h ↦ h.map (dlAdicLocalEvaluation D c T U)
    coverZero := hz
    coverDefects := ?_ }⟩
  intro I U hU S
  refine ⟨?_, ?_, ?_⟩
  · exact (hz I U hU (kernel S.f)).trans (forall_congr' fun i ↦
      (PreservesKernel.iso (dlAdicLocalEvaluation D c T (U i)) S.f).isZero_iff)
  · exact (hz I U hU (cokernel (kernel.lift S.g S.f S.zero))).trans
      (forall_congr' fun i ↦ (Classical.choice (hm (U i) S)).isZero_iff)
  · exact (hz I U hU (cokernel S.g)).trans (forall_congr' fun i ↦
      (PreservesCokernel.iso (dlAdicLocalEvaluation D c T (U i)) S.g).isZero_iff)

end WeilConjectures
