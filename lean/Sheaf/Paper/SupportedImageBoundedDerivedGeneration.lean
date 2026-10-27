/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.QcqsOpenClosedTree
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.Paper.SupportedImageGenerationHull
import Sheaf.Paper.SupportedModelKernelGeneration
import Sheaf.Paper.SupportedHullPathExtension
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-! # Derived generation of supported finite-model images

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph; agent-formulated
structural image-generation input, exact reference WANTED
(blueprint: lem-sfb-supported-image-bounded-derived-generation).

The support chains use the existing open-closed tree paths. Any finite chain in the
source can be completed by complementary leaf siblings to such a tree. Conversely,
every path has the required quasi-compact open or closed steps. The common lower bound
below is termwise, and the colimit is in complexes, before localization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem tree_qcqs {X : Scheme.{u}} (tree : QcqsOpenClosedTree X) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  cases tree <;> exact ⟨inferInstance, inferInstance⟩

private theorem path_source_qcqs {X S : Scheme.{u}} {tree : QcqsOpenClosedTree X}
    (p : tree.Path S) : CompactSpace S ∧ QuasiSeparatedSpace S := by
  induction p with
  | root t => exact tree_qcqs t
  | openBranch _ _ _ _ _ _ ih => exact ih
  | closedBranch _ _ _ _ _ _ ih => exact ih

private theorem path_extension_exact {X S : Scheme.{u}} {tree : QcqsOpenClosedTree X}
    (p : tree.Path S) :
    (p.extension Λ).Additive ∧ PreservesFiniteLimits (p.extension Λ) ∧
      PreservesFiniteColimits (p.extension Λ) := by
  induction p with
  | root t =>
    dsimp only [QcqsOpenClosedTree.Path.extension]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  | openBranch j i h a b p ih =>
    obtain ⟨hadd, hlim, hcolim⟩ := ih
    let := hadd
    let := hlim
    let := hcolim
    change (p.extension Λ ⋙ openImmersionLowerShriek Λ j).Additive ∧
      PreservesFiniteLimits (p.extension Λ ⋙ openImmersionLowerShriek Λ j) ∧
      PreservesFiniteColimits (p.extension Λ ⋙ openImmersionLowerShriek Λ j)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  | closedBranch j i h a b p ih =>
    obtain ⟨hadd, hlim, hcolim⟩ := ih
    let := hadd
    let := hlim
    let := hcolim
    let := closedSupport_lowerStarExact Λ i j (by rw [h, compl_compl])
    change (p.extension Λ ⋙ lowerStar Λ i).Additive ∧
      PreservesFiniteLimits (p.extension Λ ⋙ lowerStar Λ i) ∧
      PreservesFiniteColimits (p.extension Λ ⋙ lowerStar Λ i)
    exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The actual abelian image of any map between finite scalar local models, extended
along any support chain, belongs to the explicitly specified derived hull. Coefficients
use all continuous maps, including the full norm-topological algebraic closure.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph;
agent-formulated structural input, exact reference WANTED
(blueprint: lem-sfb-supported-image-bounded-derived-generation).

Proof plan (the DAG proof, including the two independent hull inputs):

1. All schemes in the support chain are qcqs. For a quasi-compact open subscheme, quasi-
compactness is the assumed quasi-compactness of the open, and intersections of its affine opens
remain the same quasi-compact intersections in the ambient scheme. For a closed subscheme, a
finite ambient affine cover pulls back to a finite affine cover; its pairwise intersections are
closed in the ambient quasi-compact intersections and hence quasi-compact. Induct on the length of
the chain, starting at $X$. Write $K=\ker(u:L\to M)$ on its source $S$. Refine the two model
covers to a common cover and then by weakly contractible affines. The basis theorem supplies such
a small cover $\{b_i:W_i\to S\}$. On each $W_i$ the two restrictions are scalar models for fixed
finitely presented modules $B_i,C_i$.
Uses: lem-weil-pbc-closed-in-quasi-compact, lem-weil-pbc-quasi-separated-affine-cover-criterion,
sk-thm-pe-weakly-contractible-basis.

2. Fix one such $W$ and put $P=\pi_0(W)$. Use the component morphism $\pi_W$ and its exact fully
faithful derived inverse image $F_W$. The two scalar models on $W$ are $F_W(B_R),F_W(C_R)$:
present $B,C$ by finite scalar matrices; exact inverse image takes their cokernels to the
cokernels of the same matrices over $\Lambda_W$. Full faithfulness gives a unique map $v:B_R\to
C_R$ pulling back to $u|_W$. Degree-zero maps in a module-derived category are the module maps, so
$v$ is an actual module morphism. Exactness gives $b^*K\cong F_W\ker v$. In particular we have not
replaced the continuous entries of $u$ by constant entries.
Uses: lem-zl-component-relative-profinite-site, lem-sfb-wcontractible-component-derived-hom, sk-
def-sfb-constructible, lem-weil-pbc-derived-single-fully-faithful, det-prop-sfb-module-pullback-
exact-main.

3. The functor $F_W$ preserves sheaf products: at a weakly contractible affine $U\to W$, its
evaluation formula is $F_WM(U)=M(\pi_0U)$, and all sheaf limits are sectionwise, so the product
comparison is a bijection there. The conservative basis test makes it an isomorphism. For
complexes $T_j$ on $\operatorname{Prof}/P$, therefore, $F_WQ(\prod_jT_j)=Q(\prod_jF_WT_j)$. The
termwise-product theorem on $W$ identifies the latter with $\prod_jF_WQT_j$ in the target derived
category. Full faithfulness of $F_W$ now gives, for every source object $A$,
$\operatorname{Hom}(A,Q\prod_jT_j)=\prod_j\operatorname{Hom}(A,QT_j)$. Thus $Q\prod_jT_j$ is the
source derived product and $F_W$ carries it to the target derived product. Also $F_W$ preserves
termwise filtered colimits, as an inverse-image left adjoint; it is exact and hence sends a strict
diagram with common termwise lower bound to one with that same bound. Exactness preserves shifts
and triangles, and any functor preserves retract diagrams.
Uses: lem-sfb-component-pullback-unbounded-evaluation, lem-sfb-wcontractible-component-derived-
hom, det-pe-sections-conservative, det-pe-products-derived, lem-weil-pbc-left-adjoint-preserves-
colimits, lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-ringed-topoi-module-adjunction.

4. Every generator of $\mathcal H_P$ pulls back to a finite scalar local model on $W$: the
component site functor carries its covering to a pro-étale covering, and the scalar cokernel
calculation of step 2 applies on its members. Consequently $\{T:F_WT\in\mathcal G_W\}$ is one of
the full replete classes intersected to define $\mathcal H_P$, by step 3 and by the identity-chain
generators of $\mathcal G_W$. It contains $\mathcal H_P$. The profinite relation-kernel lemma
applies to $v$ and yields $(\ker v)[0]\in\mathcal H_P$. Thus $(b^*K)[0]\in\mathcal G_W$ for every
chart $W$.
Uses: lem-zl-component-relative-profinite-site, lem-sfb-profinite-constant-model-relation-hull.

5. Apply supported-hull pro-étale descent to the module $K$ on the qcqs scheme $S$ and the cover
chosen in step 1. The hypothesis of that lemma was proved in step 4, so $K[0]\in\mathcal G_S$.
This is descent of membership in the specified hull; it is not inferred merely from conservativity
of restriction or descent of lisse sheaves.
Uses: lem-sfb-supported-hull-proetale-descent.

6. For each single arrow $a$ of the support chain, its indicated functor $a_!$ is exact and
triangulated on ordinary derived categories. For an open arrow it preserves derived products by
the extension-by-zero limits theorem and sheaf colimits by $a_!\dashv a^*$. For a closed arrow,
ordinary $a_*$ is exact, preserves derived products as the right adjoint of exact $a^*$, and
preserves filtered sheaf colimits because the target is qcqs and the open complement is quasi-
compact. Applied termwise these functors keep a common lower bound. They take supported finite-
model generators on their sources to generators on their targets by concatenating support chains.
The inverse image of $\mathcal G_{\mathrm{target}}$ under this functor is therefore an admissible
class defining $\mathcal G_{\mathrm{source}}$. Induction over the chain gives $J(\mathcal
G_S)\subseteq\mathcal G_X$, hence $JK[0]\in\mathcal G_X$.
Uses: lem-weil-pbc-proetale-ringed-open-closed, det-sf-open-closed-extension-zero-limits, lem-
weil-pbc-left-adjoint-preserves-colimits, lem-weil-pbc-right-adjoint-preserves-limits, lem-sfb-
internal-module-operations-transport, lem-sf-exact-functor-derived-triangulated, sk-def-sfb-
module-derived-pushpull, sk-def-sfb-derived-categories.

7. In the abelian module category, the image factorization gives $0\to K\to
L\to\operatorname{im}u\to0$. Exactness of $J$ gives the corresponding short exact sequence on $X$,
and the short-exact-complex triangle theorem gives the distinguished triangle $JK[0]\to JL[0]\to
J(\operatorname{im}u)[0]\to JK[1]$. The first term lies in $\mathcal G_X$ by step 6 and the second
is an explicit generator. Rotation, shifts and triangle extension closure give the third term, as
required. For a zero map the image is zero; for an identity its image is the given model. The
preceding argument includes zero scalar modules, the zero ring, empty charts and schemes, and the
empty support chain. No Noetherianity, finite coefficient field for $\Omega$-valued functions or
completeness assertion about the image has been inserted.
Uses: lem-weil-pbc-complex-ses-triangle.
-/
theorem supported_image_mem_bounded_derived_generation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hL : HasFiniteConstantLocalModel Λ S L)
    (hM : HasFiniteConstantLocalModel Λ S M) (u : L ⟶ M) :
    supportedImageGenerationHull Λ X
      ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj (image u))) := by
  obtain ⟨hcompact, hseparated⟩ := path_source_qcqs p
  let := hcompact
  let := hseparated
  have hK := finite_model_kernel_mem_supported_generation Λ ℓ hΛ S L M hL hM u
  have hJK := supported_hull_path_extension Λ tree p (kernel u) hK
  obtain ⟨hadd, hlim, hcolim⟩ := path_extension_exact Λ p
  let := hadd
  let := hlim
  let := hcolim
  let C := Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)
  let q := factorThruImage u
  let T : ShortComplex C := ShortComplex.mk (kernel.ι u) q
    (by simp only [q, ← cancel_mono (image.ι u), Category.assoc, image.fac,
      kernel.condition, HasZeroMorphisms.zero_comp])
  have hT : T.ShortExact := by
    refine { exact := ?_ }
    exact ShortComplex.exact_of_g_is_cokernel T (ShortComplex.exact_kernel u).isColimitImage
  have hJ := hT.map_of_exact (p.extension Λ)
  intro P hP
  let := hP.1
  let := hP.2.1
  exact P.ext_of_isTriangulatedClosed₃ hJ.singleTriangle hJ.singleTriangle_distinguished
    (hJK P hP) (hP.2.2.2.2.1 tree S p L hL)

end AlgebraicGeometry.ProEtale.CondensedRing
