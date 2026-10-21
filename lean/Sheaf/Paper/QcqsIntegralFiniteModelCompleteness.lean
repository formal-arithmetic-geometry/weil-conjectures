/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence

import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.CategoryTheory.ModuleObjects.LiftExact
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.Paper.PrincipalReductionConeCalculus
import Sheaf.Algebra.Homology.RoosConeCalculus
import Sheaf.Paper.CompletionTriangleComparison
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import Sheaf.Paper.FiniteConstantModelResolution
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Sheaf.Paper.ProEtaleFixedModuleConstructible
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison

/-!
# Completeness and classical reductions of qcqs integral finite-model inputs

Source: Bhatt--Scholze, The pro-etale topology for schemes, Sections 6.5--6.6;
blueprint main-20261015, localizing-closure-ctf-equals-bc, finite scalar models
(blueprint: lem-sfb-qcqs-integral-finite-model-completeness).

The scheme is arbitrary qcqs. The integral ring carries its spectral norm topology.
The completion predicate uses the specified strict-tower augmentation. Finite reductions
are formed by the recorded derived extension along the actual quotient homomorphism.
The ordinary coordinate condition retains the comparison equivalence and etale-origin pair.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The actual positive reduction has bounded constructible ordinary coordinates and
an etale-origin pair. The existential encoding is the normalized section-action encoding,
not an arbitrary derived equivalence. The quotient carries the topology induced by the
spectral norm. Index n denotes the positive exponent n+1, as in derivedReduction.
Source: Bhatt--Scholze, Sections 6.5--6.6; blueprint finite-model criterion, finite reduction
clause (blueprint: lem-sfb-qcqs-integral-finite-model-completeness). -/
def HasClassicalFiniteReduction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (V : Scheme.{u})
    (J : DerivedCategory (AdicCompletion.Modules l E V)) (n : ℕ) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) V
      ((AdicCompletion.derivedReduction l E V n).obj J) ∧
    ∃ e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) V,
    FiniteDiscreteOrdinary.ordinaryBoundedConstructible
        (Padic.coefficientExtensionRing l E (n + 1)) V
        (e.fixedDerived.functor.obj ((AdicCompletion.derivedReduction l E V n).obj J)) ∧
      ∃ h : DerivedCategory.TStructure.t.plus
          (e.fixedDerived.functor.obj ((AdicCompletion.derivedReduction l E V n).obj J)),
        Nonempty (Scheme.FixedEtaleOriginWitness V
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
          ⟨e.fixedDerived.functor.obj ((AdicCompletion.derivedReduction l E V n).obj J), h⟩)

/-- Integral finite-model constructible finite-Tor inputs on any qcqs scheme are
complete for the canonical strict quotient tower and have classical finite reductions.
No Noetherianity, dimension, characteristic or invertibility assumption is imposed.

Source: Bhatt--Scholze, Sections 6.5--6.6; the agent finite-constant-scalar-model qcqs
criterion, using the main-20261015 blueprint's finite-model argument
(blueprint: lem-sfb-qcqs-integral-finite-model-completeness).

Proof, following the DAG's eleven steps:

1. Write $B_T=A_T$ and $k_n=A/\pi^n$. Use the exact section-action equivalence and its termwise
   derived equivalence of [lem-sfb-module-object-ringed-site-derived-comparison], with the
   tensor comparison [lem-pe-internal-section-tensor-comparison], to work with ordinary sheaves
   of $B_T$-modules. These equivalences leave underlying abelian sheaves and maps unchanged;
   hence they identify cohomology, scalar matrices and their finite constant local models. They
   preserve products by the product universal property and identify the strict quotient towers
   and their augmentations: tensor is identified by the cited comparison, and every quotient map
   is the same underlying map. Thus the completion assertion may be proved in these coordinates
   and transported back, including its specified unit. All sites and products are small in the
   universe of [def-weil-size-convention].

2. We first record how to test the canonical completion map $c_K$. For an immersion $h:T\to W$,
   [lem-weil-pbc-proetale-immersion-limit-preservation] says that inverse image with an
   identified coefficient ring is exact and preserves products; its coefficient identification
   is an isomorphism by [lem-sfb-alpha-iso]. For a covering object $U\to W$, [lem-weil-proetale-
   weakly-etale-localization] and [lem-sfb-proetale-object-inverse-image-restriction] identify
   inverse image with slice restriction. Exactness follows from [det-pe-topos-functoriality-
   inverse-image] on abelian sheaves and [det-prop-sfb-module-pullback-exact-lifted] on modules
   with the identified coefficient ring. Slice restriction preserves products because module
   limits are sectionwise [lem-weil-pbc-module-sheaves-limits-sectionwise]. In either case apply
   inverse image to the strict model $D_n(M)=\operatorname{Cone}(\pi^n:M\to M)$, with transition
   $(x,y)\mapsto(x,\pi y)$ and augmentation $m\mapsto(m,0)$, of [lem-pe-principal-reduction-
   cone-calculus]. Exactness identifies these cones and scalar maps with those on the restricted
   complex. Product preservation then identifies $1-T$ and its cone in [lem-pe-roos-cone-
   calculus]. It also takes the augmentation $m\mapsto(((m,0))_n,0)$ to the restricted
   augmentation. By [lem-pe-completion-triangle-comparison] this proves compatibility with $c_K$
   itself, rather than just an abstract isomorphism of completion objects. Inverse image also
   commutes with finite reduction, by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]; here
   $h^*B_W=B_T$ and $h^*(k_n)_W=(k_n)_T$.

3. For any scheme $T$, [det-pe-derived-nakayama-resolution] identifies the derived reduction of
   $B_T[0]$ with $(k_n)_T[0]$: the exact sequence $0\to B_T\xrightarrow{\pi^n}B_T\to(k_n)_T\to0$
   gives the levelwise quasi-isomorphism from the strict cone to this quotient. The cone
   projections commute with $(x,y)\mapsto(x,\pi y)$ and take the augmentation to the quotient
   projection. The transitions $(k_{n+1})_T\to(k_n)_T$ are epimorphic: the scalar quotient is
   surjective and every local constant value has a scalar lift. Their ordinary inverse limit,
   with its actual quotient projections, is $B_T$ by [det-prop-sfb-qlbar-colimit-x-integral-
   limit]. Apply [det-pe-milnor-epimorphic] to this tower, reindexed by $n\ge1$, to identify
   that cone with its derived inverse limit. The levelwise cone-to-quotient quasi-isomorphisms
   give a quasi-isomorphism of Roos complexes by [lem-pe-roos-cone-calculus], respecting the
   augmentations just described. Consequently $c_{B_T[0]}$ is an isomorphism. The same proof
   works for each finite power $B_T^r$, since finite products commute with the displayed limits,
   scalar quotients and $1-T$; it includes $r=0$.

4. Let $M=B_T\otimes_A P$ for a finitely presented scalar $A$-module $P$. By [lem-sfb-finite-
   constant-model-two-term-free-resolution] there is an exact sequence $0\to B_T^a\to B_T^b\to
   M\to0$, induced by an exact scalar sequence $0\to A^a\xrightarrow{u}A^b\to P\to0$. Thus
   $M[0]$ is the cone of $B_T^a[0]\to B_T^b[0]$. By [lem-pe-completion-triangle-comparison], the
   three canonical completion maps form a morphism of distinguished triangles. The first two
   maps are isomorphisms by step 3; the long exact cohomology sequences [lem-sf-derived-
   homology-long-exact] show that the third is an isomorphism too (in each degree, use the five
   consecutive terms around $H^q(M)$). This proves completeness for each finite constant scalar
   model, including torsion models and the zero module. For a sheaf merely having such models on
   a pro-étale cover, step 2 identifies its restricted completion maps with these maps, and
   [lem-zl-condensed-cover-restriction-conservative] shows its completion map is an isomorphism.

5. Let $M$ be any constructible $B_V$-module in the finite constant scalar-model sense [sk-def-
   sfb-constructible]. Apply [lem-fix-constructible-open-closed-refinement] to its finite
   constructible locally closed stratification. It gives a finite binary tree of qcqs
   subschemes, each internal vertex split into a quasi-compact open and its closed complement,
   and an actual morphism from every nonempty leaf to one original stratum. Write $t:T\to
   S_\alpha$ for this morphism. The leaf restriction $M|_T$, an iterated inverse image along the
   branch immersions, is isomorphic to $t^*(M|_{S_\alpha})$ by the composition isomorphisms
   $(g\circ f)^{-1}\cong f^{-1}g^{-1}$ of [det-pe-topos-functoriality-inverse-image] (5), since
   the branch composite equals $s_\alpha\circ t$; and for a trivializing pro-étale cover
   $\{U_i\to S_\alpha\}$ the base change $\{U_i\times_{S_\alpha}T\to T\}$ is a pro-étale cover
   by clause (1) of that node. A finite constant model pulls back to a finite constant model:
   base-change the trivializing cover and its finite scalar presentation, using the coefficient
   isomorphism [lem-sfb-alpha-iso] and the tensor pullback comparison [lem-weil-pbc-ringed-
   topoi-derived-tensor-pullback]. The pulled-back presentation is a cokernel presentation with
   the same constant scalar matrix. Thus the leaf restrictions of $M$ have the local models to
   which step 4 applies. Empty leaves have the zero module category and zero completion map. No
   ordering of the original strata by an open-stratum argument is assumed.

6. For each vertex $T$ of the tree of step 5 consider the cone $C_T$ of $c_{M|_T[0]}$. Step 2
   identifies its restrictions to the two children with their corresponding cones; inverse image
   is exact, so it also identifies their cohomology. At a leaf the cone is zero by steps 4--5.
   Suppose the cones at both children of a vertex vanish. Each sheaf $H^q(C_T)$ then has zero
   restrictions to the complementary open and closed children. Their open immersion is quasi-
   compact by the refinement theorem, so [lem-exc-open-closed-detection] gives $H^q(C_T)=0$ for
   every $q$. Hence $C_T=0$ in the ordinary derived category. Finite upward induction reaches
   $V$, proving that every such constructible sheaf $M[0]$ is complete. This uses no Noetherian
   hypothesis on the space or on its structure sheaf.

7. Choose $r\le s$ with $H^q(J)=0$ outside $[r,s]$. Each nonzero cohomology sheaf is
   constructible by [sk-def-sfb-constructible], hence complete by step 6. Use the successive-
   truncation triangles [lem-weil-pbc-truncation-triangle]. The initial truncation $\tau_{\le
   r-1}J$ is zero. Inductively the triangle with vertices $\tau_{\le q-1}J$, $\tau_{\le q}J$,
   and $H^q(J)[-q]$ has complete first and third vertices: shifts preserve completeness and the
   completion maps form a morphism of triangles by [lem-pe-completion-triangle-comparison]. The
   same long-exact-sequence argument as step 4 gives completeness of the middle vertex. At
   $q=s$, $\tau_{\le s}J\simeq J$. Thus precisely the strict-tower completion unit of the
   statement is an isomorphism; no auxiliary choice of an isomorphism to a limit has replaced
   it.

8. Fix $n\ge1$. The ring $k_n$ is finite by [lem-weil-l-adic-extension-integers-dvr] and [lem-
   weil-valued-dvr-finite-quotients]. For a local model $M=B_T\otimes_A P$, use the scalar
   resolution $0\to A^a\xrightarrow{u}A^b\to P\to0$ from step 4. By the K-flat calculation in
   [lem-pur-derived-change-of-rings], its derived reduction is $[(k_n)_T^a\xrightarrow{\bar
   u}(k_n)_T^b]$ in degrees $[-1,0]$. The finite-discrete equivalence [lem-sf-module-object-
   ordinary-coefficient-equivalence] identifies these terms and their maps with ordinary
   constant-$k_n$ module sheaves. The constant module functor is exact by [def-sfb-site-derived-
   constant-module-functor], so the two cohomology sheaves are the constant sheaves of
   $\ker(\bar u:k_n^a\to k_n^b)$ and $\operatorname{coker}\bar u$. These scalar modules are
   finite, being a subset and a quotient of finite sets. They are finitely presented over $k_n$:
   choose finitely many generators from all their elements, and finitely many relations from the
   finite kernel of the resulting map from a finite free $k_n$-module. Thus this computation
   supplies both the ordinary finite-stalk local models and the finite constant scalar local
   models for the reductions, with cohomology only in $[-1,0]$.

9. For any constructible integral sheaf $M$, restrict $M\otimes^L_{B_V}(k_n)_V$ to its original
   finite stratification and then to the trivializing pro-étale covers. The
   reduction/restriction compatibility from step 2 gives exactly the two-term complexes of step
   8. Exact inverse image commutes with cohomology. Therefore every restricted cohomology sheaf
   is locally constant with finite $k_n$-values, so is constructible by [def-weil-proetale-
   constructible-sheaf]; it also has the finite scalar-model meaning of [sk-def-sfb-
   constructible], since the scalar modules in step 8 are finitely presented. The cover
   conservativity of [lem-zl-condensed-cover-restriction-conservative] and the same finite-tree
   detection as step 6 give vanishing outside $[-1,0]$ globally. Consequently
   $M\otimes^L(k_n)_V$ is bounded constructible in ordinary finite-coefficient coordinates, and
   the finite-discrete equivalence of [lem-sf-module-object-ordinary-coefficient-equivalence]
   gives the same assertion for the internal reduction.

10. Apply the exact triangulated functor $-\otimes^L_{B_V}(k_n)_V$ of [lem-pur-derived-change-
   of-rings] to the finite sequence of truncation triangles used in step 7. Its graded vertices
   are $(H^q(J)\otimes^L(k_n)_V)[-q]$, bounded constructible by step 9. The finite-discrete
   equivalence [lem-sf-module-object-ordinary-coefficient-equivalence] preserves shifts and
   distinguished triangles. In ordinary finite-coefficient coordinates, [lem-weil-proetale-dbc-
   triangulated] therefore proves by induction that $J_n$ is bounded constructible. The bound
   can be taken to be $[r-1,s]$: each graded vertex has cohomology only in $[q-1,q]$, and
   exactness of the cohomology sequences [lem-sf-derived-homology-long-exact] preserves their
   common containing interval under extensions. In particular the bound is independent of $n$.

11. The finite discrete ring $k_n$ is Noetherian: any ascending chain of its ideals stabilizes
   because it is a chain of subsets of a finite set. Apply [sk-thm-pe-constructible-comparison]
   on the qcqs scheme $V$ to the ordinary bounded constructible reduction from step 10. Its
   derived equivalence gives $L_n\in D^b_c(V_{\mathrm{ét}},k_n)$ and an isomorphism
   $\alpha_n:\nu_V^*L_n\xrightarrow{\sim}J_n$ in ordinary finite-coefficient coordinates. Retain
   this pair, which is exactly the étale-origin witness of [def-weil-pbc-etale-origin-witness];
   boundedness implies membership in $D^+$. The coefficient equivalence used here is precisely
   [lem-sf-module-object-ordinary-coefficient-equivalence]. Steps 7 and 10--11 give every
   asserted clause for arbitrary $n\ge1$. The hypotheses throughout were finite scalar models, a
   finite constructible stratification and qcqs for its refinement; no geometric condition
   involving $\ell$ was used.
-/
theorem qcqs_integral_finite_model_completeness
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (J : ConstantModelConstructibleFiniteTor (DerivedNakayama.integerRing l E) V) :
    IsDerivedComplete l E V J.obj ∧
      ∀ n : ℕ, HasClassicalFiniteReduction l E V J.obj n := by
  sorry

end AlgebraicGeometry.ProEtale
