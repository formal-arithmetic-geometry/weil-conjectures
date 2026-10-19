/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.RefinementCoefficientRealization
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.Topology.Stratification
import Sheaf.Paper.NilpotentReductionLissity
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
import Sheaf.Paper.CompatibleFiniteDerivedTrivializations
import Mathlib.CategoryTheory.Sites.Point.Basic
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.Paper.FiniteMittagLeffler
import Sheaf.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
import Sheaf.Paper.CompletedConstantFiniteComplexRealization
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Local effectivity of normalized bounded constructible towers

Source: blueprint amplification (c); Stacks Tags 09AL, 09BU--09BX and 09AV
(blueprint: lem-weil-pbc-normalized-constructible-local-effectivity).

The existing AdicTower packages the strict derived tower, quotient-linear levels,
evaluation identifications, normalization isomorphisms, transitions and quotient cocycle.
The positive level n+1 is indexed by n : ℕ. Intrinsic constructibility uses the canonical
constant-to-functions coefficient comparison. The etale-origin conclusion uses the
existing bounded-constructible essential image, transported on actual cochain
representatives along the canonical coefficient-ring isomorphism. Thus no new derived
scalar functor or chosen comparison equivalence is needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Bounded constructible etale origin of a level of the recorded adic tower. The witness
C represents an object in the existing finite-coefficient bounded-constructible essential
image. Its coefficient transport is restriction along the canonical ring-sheaf comparison,
termwise before localization. This is just a presentation of the same derived object,
not an additional condition on the representative.
Source: blueprint def-weil-pbc-proetale-modules; Stacks Tag 09AL
(blueprint: lem-weil-pbc-normalized-constructible-local-effectivity). -/
def IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : AdicTower X d) (n : ℕ) : Prop :=
  letI : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
  letI : TopologicalSpace (A ⧸ d.ideal ^ (n + 1)) := ⊥
  letI : DiscreteTopology (A ⧸ d.ideal ^ (n + 1)) := discreteTopology_bot _
  ∃ C : CochainComplex
      (ProEtale.FiniteCoefficientModules X (A ⧸ d.ideal ^ (n + 1))) ℤ,
    ProEtale.isBoundedConstructibleFiniteCoefficient X (A ⧸ d.ideal ^ (n + 1))
      (DerivedCategory.Q.obj C) ∧
    Nonempty (DerivedCategory.Q.obj
      (((SheafOfModules.restrictScalars
        (AdicCoefficients.finiteRingComparison X (A ⧸ d.ideal ^ (n + 1))).hom).mapHomologicalComplex
          (.up ℤ)).obj C) ≅ M.level n)

/-- A normalized adic tower with intrinsically constructible cohomology in one common
interval has bounded constructible etale origin at every level and admits all the common
local-model data of uniformly bounded constructibility. Local terms need not be projective.
Source: blueprint amplification (c), agent assembly of Stacks 09AL, 09BU--09BX, 09AV;
see the source and proof records of the node
(blueprint: lem-weil-pbc-normalized-constructible-local-effectivity).

Proof plan (the node's eight steps):
1. Since $P_n$ is finite, it is Noetherian. Apply
[lem-weil-pbc-finite-ring-constructible-derived-origin] to $M_n$ with its interval $[a,b]$. This
proves the first conclusion and gives bounded constructible etale witnesses $K_n$ with
$\nu_T^*K_n\simeq M_n$. Derived tensor commutes with inverse image by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Thus the etale source
$K_{n+1}\otimes^L_{P_{n+1}}P_n$ pulls back to the supplied normalized $M_n$, which is bounded.
Exactness and the sheaf unit isomorphism in [prop-weil-pbc-site-comparison-finite-level] imply
that inverse image commutes with cohomology and detects zero sheaves; hence this etale source is
bounded as well. Full faithfulness on $D^+$ in [thm-weil-pbc-site-comparison] now lifts each
normalization and its inverse uniquely, as well as the transitions after restricting to the higher
coefficient ring. Faithfulness carries the given quotient cocycle to the etale witnesses. We do
not apply bounded-below full faithfulness to a potentially unbounded derived tensor without first
checking its bound.
Dependencies: lem-weil-pbc-finite-ring-constructible-derived-origin,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, prop-weil-pbc-site-comparison-finite-level,
thm-weil-pbc-site-comparison.

2. Choose the finite stratifications witnessing constructibility of the finitely many sheaves
$\mathcal H^q(K_1)$, $a\leq q\leq b$, and intersect their strata. Finite intersections of locally
closed subsets are locally closed, and these intersections form a finite partition; give them the
iterated fibre-product subscheme structures. Refine to connected strata. A Noetherian space has
finitely many irreducible components, each connected, so its connected components are finite
unions of those components; their complements are closed, hence they are open and closed. Thus
this refinement remains finite and locally closed. On every resulting connected stratum $S$, the
cohomology of $K_1|_S$ is finite lisse. The empty scheme has the empty partition and the zero
complex as its local model.
Dependencies: def-constructible-stratification, def-weil-pbc-proetale-modules.

3. Fix a stratum $S$ and a level $n$. Put $B=P_n$ and $J=I/I^n$. The complex $K_n|_S$ is bounded
above, and its derived reduction to $B/J=P_1$ is $K_1|_S$ by repeated normalization and its
cocycle. Apply [lem-weil-pbc-nilpotent-reduction-lissity]. Since $J^n=0$, it follows that every
cohomology sheaf of $K_n|_S$ is locally constant of finite type. Over the finite ring $P_n$ these
stalks are finite sets. The original interval $[a,b]$ is preserved by the exact inverse image
along the immersion. This uses no finite Tor bound over $P_n$.
Dependencies: lem-weil-pbc-nilpotent-reduction-lissity,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

4. Choose a geometric point $\bar s$ of the nonempty connected $S$ and let $E_n=(K_n|_S)_{\bar
s}$. Stalks are exact by [prop-weil-pbc-geometric-stalks-exact] and are inverse images at the
geometric point by [lem-kun-stalk-as-pullback]; the tensor-pullback theorem therefore makes them
commute with derived scalar extension; hence $E_n$ has finite cohomology in $[a,b]$, and the
stalks of the normalizations give $E_{n+1}\otimes^L_{P_{n+1}}P_n\simeq E_n$ with the same cocycle.
By [lem-weil-pbc-finite-ring-derived-local-constancy], each $K_n|_S$ is locally isomorphic to
$\underline E_n$ and its sheaf $\mathcal I_n$ of such isomorphisms is finite locally constant with
nonempty stalks. Apply [lem-weil-pbc-compatible-finite-derived-trivializations] to these sheaves
and the two normalized systems. It gives a pro-etale covering $U\to S$ and simultaneously
compatible isomorphisms $h_n:\underline E_n|_U\simeq M_n|_U$. Restrictions of the witnesses agree
with the witnesses on the stratum by [lem-weil-pbc-comparison-pullback].
Dependencies: lem-weil-pbc-finite-ring-derived-local-constancy,
lem-weil-pbc-compatible-finite-derived-trivializations, def-weil-pbc-geometric-stalks,
lem-weil-pbc-comparison-pullback, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
prop-weil-pbc-geometric-stalks-exact, lem-kun-stalk-as-pullback.

5. Put $C=\widehat A=\varprojlim P_n$ and $J=IC$. The ring is Noetherian and $J$-adically complete
by [lem-weil-pbc-completion-noetherian-quotient-noetherian], since $A/I$ is Noetherian and $I$ is
finitely generated. Its quotients $C/J^n=P_n$ are the completion quotient identities of
[lem-weil-pbc-constant-completion-equivalence], applied on the one-point site. Apply
[lem-weil-pbc-pseudocoherent-normalized-algebra-tower] to the algebraic system $E_n$. It supplies
a pseudo-coherent $E=R\varprojlim E_n$ and compatible reduction isomorphisms $E\otimes_C^L
P_n\simeq E_n$. The Noetherian finite-cohomology hypothesis for $E_1$ holds because $P_1$ is
finite and $E_1$ is bounded.
Dependencies: lem-weil-pbc-completion-noetherian-quotient-noetherian,
lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-pseudocoherent-normalized-algebra-tower.

6. Each group $H^q(E_n)$ is finite. By [lem-weil-pbc-mittag-leffler], its inverse system has
$\varprojlim{}^1=0$. The Milnor exact sequence [lem-pc-derived-limit-milnor-sequence] therefore
identifies $H^q(E)$ with $\varprojlim H^q(E_n)$, so $E$ has cohomology only in $[a,b]$. Choose a
bounded-above finite free representative $P^\bullet\to E$ with $P^q=0$ for $q>b$ by
[lem-pc-pseudo-coherent-bounded-finite-free-model]. Set $Q^q=P^q$ for $a<q\leq b$,
$Q^a=\operatorname{coker}(P^{a-1}\to P^a)$, and $Q^q=0$ otherwise. The differential out of $Q^a$
is well-defined because $d^a d^{a-1}=0$. The quotient map $P\to Q$ induces the same cohomology in
degrees $q\geq a$ and kills an acyclic lower tail because $H^q(P)=0$ for $q<a$; it is a
quasi-isomorphism. Thus $Q$ is a single bounded complex of finite $C$-modules in $[a,b]$. Its
first term need not be projective. The construction does not tensor the truncation underived.
Dependencies: lem-weil-pbc-mittag-leffler, lem-pc-derived-limit-milnor-sequence,
lem-pc-pseudo-coherent-bounded-finite-free-model.

7. On each covering member $U$ realize $Q$ termwise by $L=c_U(Q)$ using
[lem-weil-pbc-completed-constant-finite-complex-realization]. It is supported in $[a,b]$ and its
terms are adic lisse of finite type. Regard it as an $A_T|_U$-complex by the projection-induced
coefficient map. The relative clause of that lemma gives natural compatible isomorphisms
$t_n:L\otimes^L_{A_T|_U}R_n|_U\simeq\underline{E_n}|_U$. This explicitly uses the restricted
completed coefficient ring, not an equality between its inverse image and a completed ring formed
anew on $U$. All the reduction cohomology sheaves are constant finite $P_n$-module sheaves because
$E_n$ has finite cohomology. The interval for terms is the same $[a,b]$ on all strata and covering
members.
Dependencies: lem-weil-pbc-completed-constant-finite-complex-realization.

8. Define $e_n=t_n^{-1}h_n^{-1}:M_n|_U\simeq L\otimes^L_{A_T|_U}R_n|_U$. The equation for the
compatible trivializations is $h_n\eta_n=\rho_n(h_{n+1}\otimes^L R_n)$. Naturality of the
realization isomorphisms gives $t_n\sigma_n=\eta_n(t_{n+1}\otimes^L R_n)$. Substituting the
definition of $e_n$ into these two equations gives $e_n\rho_n=\sigma_n(e_{n+1}\otimes^L R_n)$,
exactly the normalization-compatibility equation of [def-weil-pbc-bounded-constructible-tower].
The common stratification, covering and complexes constructed above satisfy every clause of that
definition, with $d_0=a,d_1=b$.
Dependencies: def-weil-pbc-bounded-constructible-tower,
lem-weil-pbc-compatible-finite-derived-trivializations,
lem-weil-pbc-completed-constant-finite-complex-realization.
-/
theorem normalizedConstructibleTower_local_effectivity
    (X : Scheme.{u}) [IsNoetherian X] {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (hconstructible : ∀ (n : ℕ) (q : ℤ),
      @IsConstructibleProEtaleCoefficientModuleSheaf X (A ⧸ d.ideal ^ (n + 1)) _
        (d.quotientFinite n)
        ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj (M.level n))))
    (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n))) :
    (∀ n : ℕ, IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin X d M n) ∧
      IsUniformlyBoundedConstructibleAdicTower d M := by
  sorry

end AlgebraicGeometry.Scheme
