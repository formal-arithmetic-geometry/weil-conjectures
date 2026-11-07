/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearGeometryOps
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsExistence
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarOperationsExistence
import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionEvaluationSections
import all WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Existence of operations on ordinary semilinear systems

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-operations-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r k h d w

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The geometric, coefficient-extension, and open-localization operations,
for a previously constructed ordinary system calculus.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-operations-existence).
Proof: apply the actual inverse-image, direct-image, tensor, and extension-by-zero
constructions on the ringed sequence site. Their normalized evaluation formulas
are obtained on K-flat and K-injective representatives and then localized. -/
structure SemilinearOperationsData (systems : Data.{c, v, r} J B τ) where
  geometric : ∀ {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv],
    {G : Geometry.{c, v, r} J B τ systems J' uInv uPush adjSet //
      G.PullTransitionFormula J B τ systems J' uInv uPush adjSet}
  coefficientExtension : ∀ (F : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n),
    ScalarSystems.{c, v, r} J B τ F σ α hα
  localization : ∀ U : C, OpenSystems.{c, v, r} J B τ U

set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option Elab.async false

-- The presentation uses free representables over two different site universes.
private noncomputable def operationRepCorepresentable
    {C₀ : Type c} {D₀ : Type d} [Category.{v} C₀] [Category.{w} D₀]
    {F : C₀ ⥤ D₀} {S : C₀ᵒᵖ ⥤ RingCat.{max c d v w r}}
    {R : D₀ᵒᵖ ⥤ RingCat.{max c d v w r}} (φ : S ⟶ F.op ⋙ R) (X : C₀) :
    (PresheafOfModules.pushforward φ ⋙ coyoneda.obj
      (Opposite.op (SheafOfModules.freeRep.{c,v,max c d v w r} S X))).CorepresentableBy
      (SheafOfModules.freeRep.{d,w,max c d v w r} R (F.obj X)) where
  homEquiv {N} := (SheafOfModules.repEquiv.{d,w,max c d v w r}
    (M := N) (X := F.obj X)).trans
      (SheafOfModules.repEquiv.{c,v,max c d v w r}
        (M := (PresheafOfModules.pushforward φ).obj N) (X := X)).symm
  homEquiv_comp g f := by
    apply SheafOfModules.repEquiv.{c,v,max c d v w r}.injective
    dsimp only [Equiv.trans_apply]
    erw [Equiv.apply_symm_apply, SheafOfModules.repEquiv_comp.{d,w,max c d v w r}]
    conv_rhs => erw [SheafOfModules.repEquiv_comp.{c,v,max c d v w r}]
    erw [Equiv.apply_symm_apply]
    rfl

-- The dependent sheaf and module functors require explicit comparison reductions.
private theorem operationPushRightAdjoint
    {C₀ : Type c} {D₀ : Type d} [Category.{v} C₀] [Category.{w} D₀]
    {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
    {F : C₀ ⥤ D₀} [F.IsContinuous J₀ K₀]
    {S : Sheaf J₀ RingCat.{max c d v w r}}
    {R : Sheaf K₀ RingCat.{max c d v w r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J₀ K₀).obj R) :
    (SheafOfModules.pushforward.{max c d v w r} φ).IsRightAdjoint := by
  have : (PresheafOfModules.pushforward.{max c d v w r} φ.hom).IsRightAdjoint := by
    apply Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    ext M
    simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
    apply Functor.leftAdjointObjIsDefined_of_isColimit
      (SheafOfModules.presentation_isColimit.{c, v, max c d v w r} M)
    rintro (_ | _)
    all_goals
      apply Functor.leftAdjointObjIsDefined_colimit
      intro X
      exact (operationRepCorepresentable.{c,v,r,d,w} φ.hom X.as.1.unop).isCorepresentable
  obtain ⟨hs, hw⟩ := SheafOfModules.coefficientSheafification.{d, w, max c d v w r} K₀
  let := hs
  let := hw
  infer_instance

attribute [local irreducible] systemRing ringPresheaf rings

universe a b av bv da db

private theorem operationExactTranspose
    {A : Type a} {B : Type b} [Category.{av} A] [Category.{bv} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{da} A] [HasDerivedCategory.{db} B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R)
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q) :
    (adj.mapExactDerivedCategory.homEquiv _ _)
      (L.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) ≫
        R.mapDerivedCategoryFactors.hom.app Q =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P Q f) := by
  have hu : adj.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        R.mapDerivedCategoryFactors.inv.app
          ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app P) := by
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    rfl
  rw [Adjunction.homEquiv_unit, hu, R.mapDerivedCategory.map_comp]
  simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  have hn := R.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  erw [Category.comp_id]

private theorem operationOpenSystems (systems : Data.{c, v, r} J B τ) (U : C) :
    Nonempty (OpenSystems.{c, v, r} J B τ U) := by
  let := abelianSheafify.{c,v,max c v r} J
  let := locallyBijective.{c,v,max c v r} J
  let φ := eqToHom (openRing.{c, v, r} J B τ U).symm
  have : (openRestriction.{c, v, r} J B τ U).IsRightAdjoint :=
    operationPushRightAdjoint.{max c v, v, r, c, v} (F := openSite U) φ
  let L := (openRestriction.{c, v, r} J B τ U).leftAdjoint
  let adj : L ⊣ openRestriction.{c, v, r} J B τ U :=
    Adjunction.ofIsRightAdjoint _
  let a (n : ℕ) := @SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
    (abelianSheafify.{c, v, max c v r} J)
    (locallyBijective.{c, v, max c v r} J) (B n) U
  let δ (n : ℕ) := (openRestrictionEvaluationSections.{c,v,r} J B τ U n).choose
  have : ((𝟭 ℕ).prod (Over.forget U)).IsContinuous
      (coefficientSequenceTopology (J.over U)) (coefficientSequenceTopology J) :=
    openSite_continuous J U
  have hi (n : ℕ) : IsIso ((mateEquiv adj (a n)).symm (δ n).hom).natTrans := by
    apply WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      (J.over U) J (Over.forget U)
      (ring.{max c v, v, max c v r} (coefficientSequenceTopology (J.over U))
        (systemRing.{max c v, v, max c v r} (J.over U)
          (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)))
      (ring.{c, v, max c v r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ)) n φ
      (ring.{max c v, v, max c v r} (J.over U) ((B n).over U))
      (ring.{c, v, max c v r} J (B n))
      (evaluation_ring.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n)
      (evaluation_ring.{c, v, max c v r} J B τ n) (𝟙 _)
      L _ adj (a n) (δ n)
  let ι (n : ℕ) := (asIso ((mateEquiv adj (a n)).symm (δ n).hom).natTrans).symm
  have : L.Additive := adj.left_adjoint_additive
  have he : ∀ S : ShortComplex _, S.Exact → (S.map L).Exact := by
    intro S hs
    apply (systems.componentwise _).mpr
    intro n
    have : (SheafOfModules.localizedSystemExtension.{c,v,r} (B n) U).Additive :=
      (a n).left_adjoint_additive
    change (S.map (L ⋙ evaluation.{c, v, max c v r} J B τ n)).Exact
    let E := evaluation.{max c v, v, max c v r} (J.over U)
      (openRings.{c,v,r} J B U) (openTransitions.{c,v,r} J B τ U) n
    let T := SheafOfModules.localizedSystemExtension.{c,v,r} (B n) U
    have : PreservesFiniteLimits T :=
      SheafOfModules.localizedSystemExtensionLimits.{c,v,r} (B n) U
    have : PreservesFiniteColimits T :=
      SheafOfModules.localizedSystemExtensionColimits.{c,v,r} (B n) U
    let S' := (S.map E).map T
    let e : S.map (L ⋙ evaluation.{c,v,max c v r} J B τ n) ≅ S' :=
      ShortComplex.isoMk ((ι n).app S.X₁) ((ι n).app S.X₂) ((ι n).app S.X₃)
        (by exact ((ι n).hom.naturality S.f).symm)
        (by exact ((ι n).hom.naturality S.g).symm)
    exact ShortComplex.exact_of_iso e.symm ((hs.map E).map T)
  obtain ⟨hl, hc⟩ := ((Functor.exact_tfae L).out 1 3).mp he
  let := hl
  let := hc
  refine ⟨{
    extension := L
    ordinaryAdjunction := adj
    extensionEvaluation := ι
    restrictionEvaluation := δ
    restrictionSections := fun n N V x ↦
      (openRestrictionEvaluationSections.{c, v, r} J B τ U n).choose_spec N V.unop x
    unit_evaluation := ?_
    counit_evaluation := ?_
    adjunction := adj.mapExactDerivedCategory
    transpose_model := ?_ }⟩
  · intro n M
    have h := unit_mateEquiv_symm adj (a n) (δ n).hom M
    change _ ≫ _ ≫ _ = _
    rw [reassoc_of% h, ← Functor.map_comp]
    change (a n).unit.app _ ≫
      (SheafOfModules.localizedSystemRestriction.{c,v,r} (B n) U).map
        ((asIso ((mateEquiv adj (a n)).symm (δ n).hom).natTrans).hom.app M ≫
          (asIso ((mateEquiv adj (a n)).symm (δ n).hom).natTrans).inv.app M) = _
    rw [Iso.hom_inv_id_app]
    erw [(SheafOfModules.localizedSystemRestriction.{c,v,r} (B n) U).map_id,
      Category.comp_id]
  · intro n N
    exact mateEquiv_counit_symm adj (a n) (δ n).hom N
  · intro P Q f
    exact operationExactTranspose adj P Q f

/-- Geometric and coefficient operations on a fixed semilinear system calculus.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-operations-existence).
Proof:
1. Apply $u^{-1}$ and $u_*$ termwise on the underlying sequence topoi. Their adjunction follows by
applying the original adjunction at every index: the naturality equations for a family of maps
correspond under transposition. The inverse image preserves finite limits and colimits, so is
exact on module systems, with coefficient ring $C_\bullet=u^{-1}B_\bullet$. This is a morphism of
the two ringed sequence topoi. Apply [lem-weil-pbc-ringed-projection-mate-exact] and
[prop-pur-kinjective-resolutions-exist] there. They give $V\dashv G=Ru_{*,\bullet}$, with $G$
computed by a K-injective system resolution and $V$ termwise exact. The unit and counit here are
maps in the ordinary derived categories of systems.

2. Write $L_n^B,L_n^C$ for the finite left extensions on the two sites. On a flat-term K-flat
representative $P$, inverse image and coefficient tensor give $VE_n^BP\cong E_n^Cu^{-1}P$, with
the same zero components above $n$. The isomorphism is $u^{-1}(P\otimes_{B_n}B_q)\cong
u^{-1}P\otimes_{C_n}C_q$. K-flat pullback and derived tensor/pullback identify it as $VL_n^B\cong
L_n^Cu^{-1}$ on the ordinary derived categories. For $P\in D(B_n)$ and $N\in D(\mathscr S(C))$,
the natural bijections
$$\operatorname{Hom}(P,e_nGN)\cong\operatorname{Hom}(L_n^BP,GN)\cong\operatorname{Hom}(VL_n^BP,N)\
cong\operatorname{Hom}(L_n^Cu^{-1}P,N)\cong\operatorname{Hom}(u^{-1}P,N_n)\cong\operatorname{Hom}(
P,Ru_{*,n}N_n)$$
therefore give $e_nG\cong Ru_{*,n}e_n$ by Yoneda. This proves the formula without any preservation
of K-injectives by evaluation.

3. Use the canonical adjunctions in the preceding Hom bijections. The derived adjunction formula
on a resolving representative is the ordinary tensor-adjoint formula: its unit sends $x$ to
$x\otimes1$, and its transpose sends $x\otimes a$ to $a h(x)$. This follows from the canonical
pre-derived adjunction formula of [lem-pc-pre-derived-adjoint-functors-general], with the identity
resolving leg, and then naturality in a K-flat resolution. Consequently the Hom bijections
defining $e_nG$ carry the evaluated unit and counit to the level unit and counit: applying the
bijection to an identity gives its unit, and applying its inverse to an identity gives its counit.
The comparison $VL_n^B\cong L_n^Cu^{-1}$ commutes with $\sigma_{mn}$, since its two composites are
the same inverse-image tensor reassociation on $q\leq n$ and zero above. Transpose this square.
The reduction transition of $GN$ becomes $G_n(t^N_{m,n})b_{m,n}$, where $b$ is the transpose of
$$u^{-1}T_{m,n}G_m\xrightarrow{q^{-1}}S_{m,n}u^{-1}G_m\xrightarrow{S_{m,n}\varepsilon_m}S_{m,n}.$$
Ordinary mate pasting gives the composition law. This proves compatibility of evaluations with the
adjunction maps and coefficient transitions, not merely the evaluated objects.

4. For an open localization apply $j_!,j^*$ at each level. Their exactness and adjunction follow
from [lem-pur-site-restriction-module-adjunction-exact], by transposing the transition equations.
Both exact functors are their own total derived functors
[lem-weil-pbc-exact-functor-derived-functor], so they descend termwise and retain their adjunction
by [lem-pc-derived-adjoint-functors]. To compute coefficient change, use the slice projection
identity [lem-weil-pbc-ringed-slice-extension-tensor]. It also proves $j_!$ preserves flatness:
tensoring an exact sequence with $j_!F$ is exact $j_!$ applied to its exact restriction tensored
with flat $F$. For K-flat $P$ and acyclic $A$, $(j_!P)\otimes A\cong j_!(P\otimes j^*A)$ is
acyclic, proving K-flatness. Thus the same identity on K-flat resolutions gives the derived
coefficient comparison. On an extension summand it sends $x\otimes b$ to $x\otimes j^*b$; iterated
coefficient changes agree as balanced tensors. All these are transformations on systems before
localization and so have the stated ordinary derived system models.

5. A compatible ring-system map $B_\bullet\to D_\bullet$ is a map of ring sheaves on the sequence
site. Apply derived ringed-topos pullback for the identity topos
[lem-weil-pbc-ringed-topoi-derived-pullback], resolving by flat-term K-flat complexes on that
site. Their evaluations are flat-term K-flat by step 3, so evaluation of extension is exactly
$M_n\otimes^L_{B_n}D_n$. Tensor and coefficient composition are obtained from total tensor
rebracketing. The monoidal and composition comparisons of
[lem-sfb-ringed-derived-monoidal-comparisons] apply both to the sequence topos and to each
evaluation morphism. They prove compatibility with tensor associativity, units, symmetry and
iterated pullback. Thus these comparisons are actual natural transformations on ordinary derived
systems, with the indicated evaluation formulas, for arbitrary coefficient maps.

6. Form each specified exchange by its unit/composition/counit word [def-weil-pbc-adjunction-mate]
for the derived functors on the ringed sequence topoi; for an open map use $j_!\dashv j^*$
instead. Pullback composition and direct-image composition use the normalized ordinary comparisons
[lem-sfb-ringed-derived-monoidal-comparisons,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. Every letter is already a system
functor or transformation. Evaluation of those letters is the level letter, including the unit and
counit by step 9 and the exact open adjunction by step 10. Hence evaluation of the word is the
corresponding level word. The same applies to any specified composite with open extension or
proper direct image. Ordinary mate pasting proves compatibility with composition on the system
category itself. No properness was needed to construct a direct-image composition, and no
invertibility of a mate is inferred.

For geometric tensor pullback use the inverse-image pure-tensor comparison on each total-complex
summand, with the inverse ordinary comparison as its recorded inverse. The differential signs make
these chain maps. Resolving on the system site by K-flat complexes with flat terms gives the
normalized derived comparison; hence its specification is checked before evaluation, without
assuming derived evaluation is faithful. -/
theorem semilinearOperationsData (systems : Data.{c, v, r} J B τ) :
    Nonempty (SemilinearOperationsData.{c, v, r} J B τ systems) := by
  classical
  refine ⟨{
    geometric := fun J' uInv uPush adjSet ↦
      (semilinearGeometricOperations J B τ systems J' uInv uPush adjSet).some
    coefficientExtension := fun F σ α hα ↦
      (semilinearScalarOperations J B τ F σ α hα).some
    localization := fun U ↦ (operationOpenSystems J B τ systems U).some }⟩

end WeilConjectures.SemilinearSections
