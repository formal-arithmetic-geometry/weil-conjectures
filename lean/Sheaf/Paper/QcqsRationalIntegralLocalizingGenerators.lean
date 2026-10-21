/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.Defs.Filter
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.Paper.FiniteConstantModelResolution
import Sheaf.AlgebraicGeometry.CoefficientTorFlatModel
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Paper.CoefficientFiniteDescentLisse
import Sheaf.Paper.StratifiedLatticeRank
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Sheaf.Paper.ContinuousLatticeSum
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Constructible

/-! # Integral generators for qcqs rational constructible complexes

Source: blueprint main-20261015, det-sf-comp-coherence-refinement.proof.md, (2),
coefficient devissage for the closed-complement calculation
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators).

The algebraic-closure coefficient is the finite-subextension-valued condensed ring.
Both conclusions take place in the ordinary unbounded module-object derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The integral scalar-extension generators for the single coefficient field E.
The existential is closed under ambient isomorphisms, with no restriction on morphisms.
Source: blueprint refinement (2), definition of G_V
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators). -/
def rationalIntegralGenerators (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (V : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) V))) :=
  fun K ↦ ∃ J : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ℓ E) V,
    Nonempty (((Mod.extendScalars (padicIntegersToPadicSubfield V ℓ E)).leftDerivedFunctor).obj
      J.obj ≅ K)

set_option synthInstance.maxHeartbeats 80000 in
-- The composite coefficient map makes the generic K-flat instance search larger.
/-- The integral scalar-extension generators for the finite-subextension-valued closure.
Every finite subextension is allowed, and the coefficient map is its actual inclusion.
Source: blueprint refinement (2), definition of G_V
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators). -/
def algClIntegralGenerators (ℓ : ℕ) [Fact ℓ.Prime] (V : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V))) :=
  fun K ↦ ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ)
    (J : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ℓ F) V),
    Nonempty (((Mod.extendScalars (padicIntegersToPadicSubfield V ℓ F ≫
      padicSubfieldRingObjToPadicAlgCl V ℓ F)).leftDerivedFunctor).obj J.obj ≅ K)

/-- Integral scalar extensions are constructible of finite Tor amplitude, and every
bounded constructible finite-Tor complex is in their ambient localizing hull. In fact it
is a finite iterated extension of shifts of those generators. All triangle maps are
arbitrary ambient linear maps; no finite-field descent of maps or complexes is claimed.

Source: blueprint refinement (2), coefficient devissage
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators).

Proof plan (the complete DAG proof, with the finite-field case omitting closure descent):
1. Work with the section-ring sheaves of the pulled-back ring objects. The equivalence
[lem-sfb-module-object-ringed-site-derived-comparison] leaves underlying sheaves and maps
unchanged, and [lem-pe-internal-section-tensor-comparison] identifies relative tensor, flatness
and K-flatness. Thus finite scalar presentations, cohomology, Tor bounds and the specified derived
scalar extensions have exactly their ringed-site meanings. At the end this equivalence transports
the argument back to module objects. It preserves ambient coproducts by their universal property;
all categories and coproducts use [def-weil-size-convention].
2. For every scheme $T$, $A_T\to F_T$ is a flat localization by
[det-prop-sfb-qlbar-colimit-x-invert-ell]. For the finite-subextension-valued algebraic closure,
$F_T\to\Lambda_T$ is flat by [lem-sfb-qlbar-flat]. Their composite is flat: its tensor functor is
the composite of the two exact scalar-extension functors, by $(b\otimes f)\otimes m\mapsto
b\otimes fm$ and its inverse $b\otimes m\mapsto(b\otimes1)\otimes m$. These maps follow directly
from the balancing relations. Consequently $T_{F,T}$ is exact termwise scalar extension,
triangulated by [lem-sf-exact-functor-derived-triangulated], and its cohomology is the scalar
extension of the original cohomology by [lem-weil-pbc-exact-functor-complex-cohomology]. Only the
finite-valued algebraic-closure coefficient is used here.
3. Let $J\in D_{\mathrm{ctf}}(V,A)$. Each local scalar model of each $H^q(J)$ has the two-term
finite-free scalar resolution of [lem-sfb-finite-constant-model-two-term-free-resolution]. After
step 2 its scalar matrix is over the field $\Lambda(*)$; its cokernel is a finite-dimensional
vector space, so its realized cokernel is finite free. Hence $H^q(T_{F,V}J)$ has finite constant
models on the same finite constructible stratification. Boundedness follows from the cohomology
identification in step 2. For a Tor interval $[a,b]$ of $J$, [lem-pe-coefficient-tor-flat-model]
supplies a flat complex supported in $[a,b]$. Base change carries flat modules to flat modules:
tensoring the base-changed module with an arbitrary target-module sheaf equals tensoring the
original module with that sheaf after scalar restriction, by the same balancing relations. The
base-changed flat complex therefore has the same support and represents $T_{F,V}J$ by
[lem-pur-derived-change-of-rings]. Apply the Tor/flat-model criterion again. This proves $\mathcal
G_V\subset D_{\mathrm{ctf}}(V,\Lambda)$.
4. Fix a constructible $\Lambda_V$-module $M$. Apply
[lem-fix-constructible-open-closed-refinement] to a finite constructible locally closed
stratification witnessing its constructibility. This gives a finite binary tree with qcqs
vertices, each cut by a quasi-compact open and its closed complement, and genuine scheme morphisms
from leaves to original strata. Along each branch use the exact inverse-image composition of
[det-pe-topos-functoriality-inverse-image] and the coefficient isomorphism [lem-sfb-alpha-iso].
Pull back the trivializing covers and scalar presentations. On a leaf the pulled scalar module is
finite-dimensional over $\Lambda(*)$, hence its realization is finite free. Thus each leaf
restriction of $M$ is lisse. The use of actual factoring morphisms avoids inferring factorization
merely from containment of underlying sets.
5. On a qcqs leaf $T$, the lisse module is already over $E_T$ when $\Lambda=E$. When
$\Lambda=\Omega^{\mathrm{fin}}$, apply clause (1) of [det-lem-coefficient-finite-descent-lisse] on
this qcqs $T$, obtaining a finite subextension $F$ and lisse $F_T$-module $L$ whose extension is
$M|_T$. This result applies to lisse objects, not to the full complex or its arrows. Split $T$
into its finitely many clopen constant-rank pieces using [det-lem-stratified-lattice-rank] for
$L$. All pieces remain qcqs, and rank zero is permitted.
6. For a constant-rank lisse $F_T$-module $L$ on qcqs $T$, [det-lem-stratified-lattice-scheme]
gives a separated etale surjection $q:\mathrm{Lat}(L)\to T$ and a universal lisse integral lattice
in $q^*L$. Images of affine opens of $\mathrm{Lat}(L)$ are open by
[lem-weil-pbc-etale-morphism-open-map]. Quasi-compactness [def-weil-pbc-quasi-compact-scheme]
selects finitely many whose images cover $T$. Their disjoint union $P$ is qcqs, and $p:P\to T$ is
separated, etale and surjective. Restrict the universal lattice to $P$. Apply
[lem-weil-pbc-etale-stratified-finite] (Stacks Tag 03S0) to $p$. It supplies a finite
constructible locally closed partition of $T$ such that every $p_S:P\times_T S\to S$ is finite
etale and surjective. This use of 03S0 requires only qcqs, not Noetherianity.
7. Fix one such $S$, with lattice $N\subset p_S^*L$. Split $p_S$ on an etale covering using
[lem-weil-pbc-finite-etale-etale-local-split]. On a splitting with sheets indexed by a finite set
$I$, define $p_{S*}p_S^*L\to L$ by $(s_i)\mapsto\sum_i s_i$. Two splittings differ locally by a
permutation of the sheets, which leaves this sum unchanged; hence these local maps glue by the
sheaf condition. Define $L_0$ as the image of $p_{S*}N\to L$. Over a splitting it is the sum of
the sheet lattices. The set $I$ is nonempty since $p_S$ is surjective. This constructs the trace
and its image without dividing by the degree.
8. Trivialize $L$ further pro-etale locally. Clause (1) of [det-lem-stratified-lattice-scheme]
identifies a lattice in this trivialization with a section of the constant sheaf on
$\mathrm{GL}_r(F)/\mathrm{GL}_r(\mathcal O_F)$. Thus on a further common covering the finitely
many sheet lattices are fixed scalar lattices $B_i\subset F^r$. Apply
[lem-sfb-continuous-lattice-sum]: their sheaf sum is the sheaf of continuous functions into
$\sum_iB_i$, is finite free over the integral coefficients, and its actual inclusion spans the
rational coefficient module. The comparison [lem-weil-pbc-continuous-coefficient-realizations]
identifies this calculation with the pulled-back condensed coefficients, including the inclusion.
Therefore $L_0$ is lisse over $\mathcal O_{F,S}$ and $F_S\otimes L_0\cong L|_S$. This is a direct
local sum calculation, with no Noetherian hypothesis on $S$.
9. Apply [lem-fix-constructible-open-closed-refinement] on each qcqs $T$ from step 5 to the finite
partition just obtained. Its leaves have actual maps to the lattice-bearing strata. Pull back
$L_0$ and its spanning isomorphism, using [lem-sfb-alpha-iso] and
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. A locally free integral module remains
locally free under this pullback, because the pulled trivializing cover and basis remain a cover
and a basis. Coefficient extension also pulls back by the cited tensor comparison. Attach these
finite trees to the original tree of step 4. We obtain one finite qcqs open/closed tree over $V$;
on every nonempty terminal leaf $W$ there are a finite coefficient field $F$ (equal to $E$ in the
finite-field case), an integral lisse module $B_W$, and an isomorphism $\Lambda_W\otimes_{\mathcal
O_{F,W}} B_W\cong M|_W$.
10. For an edge of this tree, extension from an open child means $j_!$, and extension from a
closed child means $i_*$. These are exact, restrict to the identity on the child, and vanish on
the other child by [lem-weil-pbc-proetale-ringed-open-closed]. If a child module has finite
constant models on a finite constructible partition, its extension has the same models on those
strata and the zero model on the complementary child. All these subsets are constructible in the
parent: a quasi-compact open is constructible, its complement is constructible, and relative
constructible subsets compose in such a constructible locally closed subset
[def-weil-constructible-subset]. Thus the extensions preserve the finite scalar-model
constructibility used here. A locally free module has Tor amplitude $[0,0]$ by its local free
tensor calculation; [lem-sfb-tor-interval-local-detection] tests this on the trivializing cover
and then on complementary children. Consequently either edge extension of a flat module is flat,
and iteration preserves Tor amplitude $[0,0]$.
11. These edge extensions commute with the exact coefficient extension of step 2. For $j_!$ take
the map $j_!(\Lambda_U\otimes B)\to\Lambda_T\otimes j_!B$ adjoint to its identity restriction on
$U$. For $i_*$ take $\Lambda_T\otimes i_*B\to i_*(\Lambda_Z\otimes B)$ adjoint to its identity
restriction on $Z$. The restriction comparisons are
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback], with coefficient identifications
[lem-sfb-alpha-iso]. Each map restricts to an isomorphism on its own child and to $0\to0$ on the
other by [lem-weil-pbc-proetale-ringed-open-closed]. The kernel and cokernel have both
restrictions zero; [lem-exc-open-closed-detection] makes them zero. This proves both comparison
isomorphisms, and iteration proves the comparison along any branch.
12. For a terminal leaf $W$, extend its $B_W$ to $V$ along its branch, using the edge operations
of step 10, and denote the resulting integral sheaf by $J_W$. Step 10 gives bounded
constructibility and Tor amplitude $[0,0]$, so $J_W[0]\in D_{\mathrm{ctf}}(V,\mathcal O_F)$. Step
11 and the leaf isomorphism of step 9 identify $T_{F,V}(J_W[0])$ with the branch extension of
$(M|_W)[0]$. It therefore lies in $\mathcal G_V$. The empty leaf contributes zero, for which the
zero integral module is a model.
13. At each internal vertex $T$, the localization sequence of
[lem-weil-pbc-proetale-ringed-open-closed] applied to $M|_T$ is $0\to j_!(M|_U)\to M|_T\to
i_*(M|_Z)\to0$. Extend it to $V$ by the exact edge functors along the branch. By
[lem-sf-derived-ses-triangle] this is a distinguished triangle. Induct upward through the finite
tree: its terminal branch extensions are in $\mathcal G_V$ by step 12, and its middle vertex is an
extension of the two child vertices. Thus $M[0]$ is obtained from finitely many objects of
$\mathcal G_V$ by finitely many triangle extensions. This is a finite-tree induction, with the
terminal case already proved; it does not assume that an original stratum is open in the union of
the remaining strata.
14. For $K\in D_{\mathrm{ctf}}(V,\Lambda)$ choose $a\le b$ containing its cohomology. Every
$H^q(K)[0]$ is constructible, so step 13 gives its finite construction from $\mathcal G_V$. Apply
the truncation triangles of [lem-weil-pbc-truncation-triangle]: $\tau_{\le a-1}K=0$, and for
$q=a,\ldots,b$ the triangle has vertices $\tau_{\le q-1}K$, $\tau_{\le q}K$, and $H^q(K)[-q]$.
Induction gives $\tau_{\le b}K\simeq K$ in the finite shift-and-extension closure of $\mathcal
G_V$, hence in its ambient localizing hull. No connecting map is descended to $F$; all triangles
and their arbitrary $\Lambda_V$-linear maps stay in the ambient category. Together with step 3
this proves both clauses. The zero complex, empty $V$ and rank-zero leaves are included.
-/
theorem qcqs_rational_integral_localizing_generators
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V] :
    (∀ K, rationalIntegralGenerators ℓ E V K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) V K ∧
        DerivedCategory.finiteTorAmplitude _ K) ∧
    (∀ K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) V,
      CategoryTheory.localizingClosure (rationalIntegralGenerators ℓ E V) K.obj ∧
        ∃ n : ℕ,
          ((rationalIntegralGenerators ℓ E V).shiftClosure ℤ).extensionProductIter n K.obj) := by
  sorry

/-- Integral scalar extensions are constructible of finite Tor amplitude, and every
bounded constructible finite-Tor complex is in their ambient localizing hull. In fact it
is a finite iterated extension of shifts of those generators. All triangle maps are
arbitrary ambient linear maps; no finite-field descent of maps or complexes is claimed.

Source: blueprint refinement (2), coefficient devissage
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators).

Proof plan (the complete DAG proof, with the finite-field case omitting closure descent):
1. Work with the section-ring sheaves of the pulled-back ring objects. The equivalence
[lem-sfb-module-object-ringed-site-derived-comparison] leaves underlying sheaves and maps
unchanged, and [lem-pe-internal-section-tensor-comparison] identifies relative tensor, flatness
and K-flatness. Thus finite scalar presentations, cohomology, Tor bounds and the specified derived
scalar extensions have exactly their ringed-site meanings. At the end this equivalence transports
the argument back to module objects. It preserves ambient coproducts by their universal property;
all categories and coproducts use [def-weil-size-convention].
2. For every scheme $T$, $A_T\to F_T$ is a flat localization by
[det-prop-sfb-qlbar-colimit-x-invert-ell]. For the finite-subextension-valued algebraic closure,
$F_T\to\Lambda_T$ is flat by [lem-sfb-qlbar-flat]. Their composite is flat: its tensor functor is
the composite of the two exact scalar-extension functors, by $(b\otimes f)\otimes m\mapsto
b\otimes fm$ and its inverse $b\otimes m\mapsto(b\otimes1)\otimes m$. These maps follow directly
from the balancing relations. Consequently $T_{F,T}$ is exact termwise scalar extension,
triangulated by [lem-sf-exact-functor-derived-triangulated], and its cohomology is the scalar
extension of the original cohomology by [lem-weil-pbc-exact-functor-complex-cohomology]. Only the
finite-valued algebraic-closure coefficient is used here.
3. Let $J\in D_{\mathrm{ctf}}(V,A)$. Each local scalar model of each $H^q(J)$ has the two-term
finite-free scalar resolution of [lem-sfb-finite-constant-model-two-term-free-resolution]. After
step 2 its scalar matrix is over the field $\Lambda(*)$; its cokernel is a finite-dimensional
vector space, so its realized cokernel is finite free. Hence $H^q(T_{F,V}J)$ has finite constant
models on the same finite constructible stratification. Boundedness follows from the cohomology
identification in step 2. For a Tor interval $[a,b]$ of $J$, [lem-pe-coefficient-tor-flat-model]
supplies a flat complex supported in $[a,b]$. Base change carries flat modules to flat modules:
tensoring the base-changed module with an arbitrary target-module sheaf equals tensoring the
original module with that sheaf after scalar restriction, by the same balancing relations. The
base-changed flat complex therefore has the same support and represents $T_{F,V}J$ by
[lem-pur-derived-change-of-rings]. Apply the Tor/flat-model criterion again. This proves $\mathcal
G_V\subset D_{\mathrm{ctf}}(V,\Lambda)$.
4. Fix a constructible $\Lambda_V$-module $M$. Apply
[lem-fix-constructible-open-closed-refinement] to a finite constructible locally closed
stratification witnessing its constructibility. This gives a finite binary tree with qcqs
vertices, each cut by a quasi-compact open and its closed complement, and genuine scheme morphisms
from leaves to original strata. Along each branch use the exact inverse-image composition of
[det-pe-topos-functoriality-inverse-image] and the coefficient isomorphism [lem-sfb-alpha-iso].
Pull back the trivializing covers and scalar presentations. On a leaf the pulled scalar module is
finite-dimensional over $\Lambda(*)$, hence its realization is finite free. Thus each leaf
restriction of $M$ is lisse. The use of actual factoring morphisms avoids inferring factorization
merely from containment of underlying sets.
5. On a qcqs leaf $T$, the lisse module is already over $E_T$ when $\Lambda=E$. When
$\Lambda=\Omega^{\mathrm{fin}}$, apply clause (1) of [det-lem-coefficient-finite-descent-lisse] on
this qcqs $T$, obtaining a finite subextension $F$ and lisse $F_T$-module $L$ whose extension is
$M|_T$. This result applies to lisse objects, not to the full complex or its arrows. Split $T$
into its finitely many clopen constant-rank pieces using [det-lem-stratified-lattice-rank] for
$L$. All pieces remain qcqs, and rank zero is permitted.
6. For a constant-rank lisse $F_T$-module $L$ on qcqs $T$, [det-lem-stratified-lattice-scheme]
gives a separated etale surjection $q:\mathrm{Lat}(L)\to T$ and a universal lisse integral lattice
in $q^*L$. Images of affine opens of $\mathrm{Lat}(L)$ are open by
[lem-weil-pbc-etale-morphism-open-map]. Quasi-compactness [def-weil-pbc-quasi-compact-scheme]
selects finitely many whose images cover $T$. Their disjoint union $P$ is qcqs, and $p:P\to T$ is
separated, etale and surjective. Restrict the universal lattice to $P$. Apply
[lem-weil-pbc-etale-stratified-finite] (Stacks Tag 03S0) to $p$. It supplies a finite
constructible locally closed partition of $T$ such that every $p_S:P\times_T S\to S$ is finite
etale and surjective. This use of 03S0 requires only qcqs, not Noetherianity.
7. Fix one such $S$, with lattice $N\subset p_S^*L$. Split $p_S$ on an etale covering using
[lem-weil-pbc-finite-etale-etale-local-split]. On a splitting with sheets indexed by a finite set
$I$, define $p_{S*}p_S^*L\to L$ by $(s_i)\mapsto\sum_i s_i$. Two splittings differ locally by a
permutation of the sheets, which leaves this sum unchanged; hence these local maps glue by the
sheaf condition. Define $L_0$ as the image of $p_{S*}N\to L$. Over a splitting it is the sum of
the sheet lattices. The set $I$ is nonempty since $p_S$ is surjective. This constructs the trace
and its image without dividing by the degree.
8. Trivialize $L$ further pro-etale locally. Clause (1) of [det-lem-stratified-lattice-scheme]
identifies a lattice in this trivialization with a section of the constant sheaf on
$\mathrm{GL}_r(F)/\mathrm{GL}_r(\mathcal O_F)$. Thus on a further common covering the finitely
many sheet lattices are fixed scalar lattices $B_i\subset F^r$. Apply
[lem-sfb-continuous-lattice-sum]: their sheaf sum is the sheaf of continuous functions into
$\sum_iB_i$, is finite free over the integral coefficients, and its actual inclusion spans the
rational coefficient module. The comparison [lem-weil-pbc-continuous-coefficient-realizations]
identifies this calculation with the pulled-back condensed coefficients, including the inclusion.
Therefore $L_0$ is lisse over $\mathcal O_{F,S}$ and $F_S\otimes L_0\cong L|_S$. This is a direct
local sum calculation, with no Noetherian hypothesis on $S$.
9. Apply [lem-fix-constructible-open-closed-refinement] on each qcqs $T$ from step 5 to the finite
partition just obtained. Its leaves have actual maps to the lattice-bearing strata. Pull back
$L_0$ and its spanning isomorphism, using [lem-sfb-alpha-iso] and
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. A locally free integral module remains
locally free under this pullback, because the pulled trivializing cover and basis remain a cover
and a basis. Coefficient extension also pulls back by the cited tensor comparison. Attach these
finite trees to the original tree of step 4. We obtain one finite qcqs open/closed tree over $V$;
on every nonempty terminal leaf $W$ there are a finite coefficient field $F$ (equal to $E$ in the
finite-field case), an integral lisse module $B_W$, and an isomorphism $\Lambda_W\otimes_{\mathcal
O_{F,W}} B_W\cong M|_W$.
10. For an edge of this tree, extension from an open child means $j_!$, and extension from a
closed child means $i_*$. These are exact, restrict to the identity on the child, and vanish on
the other child by [lem-weil-pbc-proetale-ringed-open-closed]. If a child module has finite
constant models on a finite constructible partition, its extension has the same models on those
strata and the zero model on the complementary child. All these subsets are constructible in the
parent: a quasi-compact open is constructible, its complement is constructible, and relative
constructible subsets compose in such a constructible locally closed subset
[def-weil-constructible-subset]. Thus the extensions preserve the finite scalar-model
constructibility used here. A locally free module has Tor amplitude $[0,0]$ by its local free
tensor calculation; [lem-sfb-tor-interval-local-detection] tests this on the trivializing cover
and then on complementary children. Consequently either edge extension of a flat module is flat,
and iteration preserves Tor amplitude $[0,0]$.
11. These edge extensions commute with the exact coefficient extension of step 2. For $j_!$ take
the map $j_!(\Lambda_U\otimes B)\to\Lambda_T\otimes j_!B$ adjoint to its identity restriction on
$U$. For $i_*$ take $\Lambda_T\otimes i_*B\to i_*(\Lambda_Z\otimes B)$ adjoint to its identity
restriction on $Z$. The restriction comparisons are
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback], with coefficient identifications
[lem-sfb-alpha-iso]. Each map restricts to an isomorphism on its own child and to $0\to0$ on the
other by [lem-weil-pbc-proetale-ringed-open-closed]. The kernel and cokernel have both
restrictions zero; [lem-exc-open-closed-detection] makes them zero. This proves both comparison
isomorphisms, and iteration proves the comparison along any branch.
12. For a terminal leaf $W$, extend its $B_W$ to $V$ along its branch, using the edge operations
of step 10, and denote the resulting integral sheaf by $J_W$. Step 10 gives bounded
constructibility and Tor amplitude $[0,0]$, so $J_W[0]\in D_{\mathrm{ctf}}(V,\mathcal O_F)$. Step
11 and the leaf isomorphism of step 9 identify $T_{F,V}(J_W[0])$ with the branch extension of
$(M|_W)[0]$. It therefore lies in $\mathcal G_V$. The empty leaf contributes zero, for which the
zero integral module is a model.
13. At each internal vertex $T$, the localization sequence of
[lem-weil-pbc-proetale-ringed-open-closed] applied to $M|_T$ is $0\to j_!(M|_U)\to M|_T\to
i_*(M|_Z)\to0$. Extend it to $V$ by the exact edge functors along the branch. By
[lem-sf-derived-ses-triangle] this is a distinguished triangle. Induct upward through the finite
tree: its terminal branch extensions are in $\mathcal G_V$ by step 12, and its middle vertex is an
extension of the two child vertices. Thus $M[0]$ is obtained from finitely many objects of
$\mathcal G_V$ by finitely many triangle extensions. This is a finite-tree induction, with the
terminal case already proved; it does not assume that an original stratum is open in the union of
the remaining strata.
14. For $K\in D_{\mathrm{ctf}}(V,\Lambda)$ choose $a\le b$ containing its cohomology. Every
$H^q(K)[0]$ is constructible, so step 13 gives its finite construction from $\mathcal G_V$. Apply
the truncation triangles of [lem-weil-pbc-truncation-triangle]: $\tau_{\le a-1}K=0$, and for
$q=a,\ldots,b$ the triangle has vertices $\tau_{\le q-1}K$, $\tau_{\le q}K$, and $H^q(K)[-q]$.
Induction gives $\tau_{\le b}K\simeq K$ in the finite shift-and-extension closure of $\mathcal
G_V$, hence in its ambient localizing hull. No connecting map is descended to $F$; all triangles
and their arbitrary $\Lambda_V$-linear maps stay in the ambient category. Together with step 3
this proves both clauses. The zero complex, empty $V$ and rank-zero leaves are included.
-/
theorem qcqs_algCl_integral_localizing_generators
    (ℓ : ℕ) [Fact ℓ.Prime]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V] :
    (∀ K, algClIntegralGenerators ℓ V K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) V K ∧
        DerivedCategory.finiteTorAmplitude _ K) ∧
    (∀ K : ConstantModelConstructibleFiniteTor (Profinite.padicAlgClRingObj ℓ) V,
      CategoryTheory.localizingClosure (algClIntegralGenerators ℓ V) K.obj ∧
        ∃ n : ℕ, ((algClIntegralGenerators ℓ V).shiftClosure ℤ).extensionProductIter n K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale
