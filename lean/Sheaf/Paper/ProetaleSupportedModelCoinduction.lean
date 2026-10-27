/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.SupportedModelHull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.Paper.SectionwiseFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.CategoryTheory.CechPushforwardAugmentedModel
import Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import Sheaf.CategoryTheory.FiniteProductInjectiveResolutions
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived

/-! # Pro-etale coinduction of supported finite scalar models

Source: agent-formulated generator-level coinduction obligation below blueprint latest,
sec-six-functors-basics/sk-prop-sf-comp-coherence/det-sf-comp-coherence-cocycle.proof.md,
refinement paragraph, via refinement (2). Hemo--Richarz--Scholbach Sections 3--4 specify
the ordinary module-object setting; Lemma 5.3(1) supplies bounded continuity only.
An exact reference for this coinduction statement is WANTED.
(blueprint: lem-sfb-proetale-supported-model-coinduction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Actual ordinary module-derived direct image along a qcqs weakly etale map sends
supported finite scalar local models in degree zero into the target supported model hull.
The five coefficient cases exclude both algebraic-closure coefficient conventions.

Source: agent-formulated generator-level coinduction obligation below blueprint latest,
det-sf-comp-coherence-cocycle, refinement paragraph, via refinement (2).
Hemo--Richarz--Scholbach Sections 3--4 give the ambient setting, and Lemma 5.3(1)
only bounded continuity; neither Corollary 4.7 nor Lemma 5.3 asserts this statement.
Exact coinduction reference WANTED.
(blueprint: lem-sfb-proetale-supported-model-coinduction).

Proof plan (the six steps of the DAG):

1. Use the etale coinduction theorem for the fixed coefficient to obtain its quantified etale
property on all qcqs schemes. Substituting it into conditional ind-etale continuity shows that
every qcqs map locally admitting the specified finite affine ind-etale charts sends supported
finite scalar generators into the target hull. This substitution does not assume descent of a
local model to one etale stage.
Uses: lem-sfb-etale-supported-model-coinduction, lem-sfb-indetale-supported-hull-continuity.

2. Choose the finite cover $q_a:D_a\to U$ supplied by the ind-etale Cech refinement theorem.
Every iterated fibre product $D_{a_0\ldots a_n}$ is qcqs and its map to $V$ has exactly the
finite affine ind-etale charts required in step 1. These are source covers, so no assertion of
descent of hull-membership on $V$ is being used. Empty $U$ gives zero throughout and can be
discarded.
Uses: lem-sfb-weakly-etale-indetale-cech-refinement.

3. Put $N=JL$. Along any Cech projection $r:D_{a_0\ldots a_n}\to U$, base-change the entire
support chain. The open and closed module base-change isomorphisms, iterated one edge at a time
and transported through the exact internal/section-module equivalences, give $r^*JL\cong J'
r_W^*L$. Quasi-compactness and quasi-separatedness survive base change; the complementary open
is the base change of the original complementary open. Restrict the cover trivializing $L$: on
that cover the same constant presentation for the scalar module $P$ gives
$\Lambda\otimes_{\underline\Lambda}\underline P$ after inverse image. Thus $r_W^*L$ is a finite
scalar local model and $r^*N$ is a supported generator on the intersection. Step 1 now puts $R(b
r)_*(r^*N[0])$ in $\mathcal G_V$.
Uses: lem-sf-ring-sheaf-base-change-mates, lem-sfb-internal-module-operations-transport, lem-
weil-pbc-qcqs-morphism-permanence, sk-def-sfb-constructible.

4. The finite covering family defines an epimorphism $D=\coprod_a h_{D_a}\to1$ in
$U_{\mathrm{proét}}$. Apply the coherent Cech pushforward-model theorem with $f=b$ and the
module $N$. It gives a nonnegative double complex $B^{n,q}$ on $V$, an isomorphism
$Rb_*N[0]\cong Q\operatorname{Tot}B$, and column isomorphisms $QB^{n,\bullet}\cong
R(bv_n)_*(N_n[0])$. Finite-family site geometry identifies $D^{n+1}$ with the finite disjoint
union of the fibre products in step 2. Sections on a finite disjoint union are the product of
the component sections, so its module direct image is the product of the component direct
images; compatible finite products of injective resolutions compute their derived product. Slice
localization identifies each component with its own pro-etale site, and exact module transport
retains the pulled-back coefficient. Hence the column is a finite product of the objects in step
3 and belongs to $\mathcal G_V$. The augmentation is the actual derived restriction
augmentation.
Uses: lem-sfb-cech-pushforward-augmented-model, lem-weil-pbc-proetale-qcqs-finite-family-
geometry, lem-weil-pbc-finite-product-injective-resolutions, lem-weil-proetale-weakly-etale-
localization, lem-sfb-internal-module-operations-transport.

5. Let $T_m$ be the total of columns $0,\ldots,m$, with the outgoing horizontal differential
discarded. Projection $T_m\to T_{m-1}$ is a chain map whose kernel is $B^{m,\bullet}[-m]$ with
the signed vertical differential. The degreewise short exact sequence gives a distinguished
triangle. Starting at $T_0=B^{0,\bullet}$ and using step 4, shift and triangle-extension closure
gives $QT_m\in\mathcal G_V$ for all $m\ge0$. These truncations are quotient complexes; no
spurious inclusion as subcomplexes is used.
Uses: lem-weil-pbc-complex-ses-triangle.

6. The projections $T_{m+1}\to T_m$ split on graded modules by insertion of a zero column. For
$T=\operatorname{Tot}B$ there is a degreewise short exact sequence $0\to
T\to\prod_{m\ge0}T_m\xrightarrow{1-s}\prod_{m\ge0}T_m\to0$, where $(sx)_m$ is the projection of
$x_{m+1}$. Indeed the kernel is the compatible sequences, and in degree $r$ the tower stabilizes
once $m\ge r$, identifying its limit with $T^r$. For surjectivity, given $(y_m)$ set $x_0=0$ and
recursively lift $x_m-y_m$ to $x_{m+1}$ using the graded splitting. This is a morphism of
degree-$r$ sheaves, so it proves epimorphy without choosing objectwise preimages. Termwise
products represent derived products. By step 5 both products lie in $\mathcal G_V$, and the
short-exact-sequence triangle, rotation and shift closure put $QT$ there. The augmented-total
isomorphism from step 4 proves the asserted membership of $Rb_*JL[0]$. All constructions retain
zero models, zero rings and identity support chains.
Uses: det-pe-products-derived, lem-weil-pbc-complex-ses-triangle.
-/
theorem proetale_supported_model_coinduction
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
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
    (U V : Scheme.{u})
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace V] [QuasiSeparatedSpace V]
    (b : U ⟶ V) [WeaklyEtale b] [QuasiCompact b] [QuasiSeparated b]
    (W : Scheme.{u}) (p : ScalarModelSupportChain U W)
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))
    (hL : HasFiniteConstantLocalModel Λ W L) :
    supportedModelHull Λ V
      ((CondensedRing.moduleObjectDerivedPushforward Λ b).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L))) := by
  sorry

end AlgebraicGeometry.ProEtale
