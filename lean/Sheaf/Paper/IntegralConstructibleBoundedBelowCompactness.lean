/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.AdicGlobalDerivedHom
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
import Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Algebra.Homology.RhomGlobalSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.Topology.Stratification
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.AlgebraicGeometry.ProEtaleClosedLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Integral constructible complexes and uniformly bounded below sums

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.12 and
Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-constructible-bounded-below-compactness).

Coproducts are supplied as colimit cofans, so the statement is independent of
chosen coproduct objects. Their universal property constructs exactly the comparison
induced by the individual coprojections. The empty family is included.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Global derived Hom out of an integral constructible complex commutes with sums
of complexes having one common integer cohomological lower bound. The map is the
unique map whose component at i is RHom(K,-) of the ith coprojection. Both sums are
coproducts in the ambient derived categories, with no completion of their sum.
Source: Bhatt--Scholze, Lemma 6.8.12, using Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-constructible-bounded-below-compactness).
Proof:
1. First establish the bounded-below cohomology calculation for an arbitrary commutative ring
sheaf R on the pro-etale site of a qcqs scheme S. The module category is Grothendieck by
[lem-weil-pbc-small-module-diagrams-grothendieck], with the diagram category chosen to be the
one-object identity category. Given M_i with a common lower bound N, choose representatives E_i
with E_i^q=0 for q<N using [def-sbc-standard-tstructure-derived-category]. Their termwise sum
represents the derived coproduct by [lem-kun-grothendieck-derived-coproducts]. Choose the affine
weakly contractible hypercover U_bullet of S supplied by
[lem-weil-pbc-proetale-affine-acyclic-hypercover]. By
[lem-weil-pbc-proetale-hypercover-computes-bounded-complex], RΓ(S,M_i) is the total complex of
E_i^q(U_p), and the same formula computes the coproduct. Evaluation on U_p preserves sums by
[lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits]. In total degree r only N≤q≤r
and p=r-q occur, so interchanging the sum over i with this finite sum identifies the total
complexes, including their differentials and coprojections. Therefore the canonical map ⊕_i
RΓ(S,M_i)→RΓ(S,⊕_i M_i) is an isomorphism. This proves the integral ring-sheaf version directly,
rather than applying the existing rational-coefficient pushforward lemma.
2. We use a local form of the desired property. For a qcqs S, a commutative ring sheaf R, and B
bounded above, let C_S(B) mean: for every qcqs pro-etale object W→S, global RHom on W out of
B|_W commutes with every small family with a common lower bound. All coefficient sheaves in this
argument are inverse images of R; when tensoring with A-complexes, fix the A-algebra structure
on R and write R_Z=i^{-1}R for a closed immersion i. Write H(B,M)=Rℋom_R(B,M). If B∈D^{≤b} and
M∈D^{≥N}, then H(B,M)∈D^{≥N-b}. Here are details that do not assume an injective resolution
starts in exactly degree N. Choose bounded-below K-injective representatives using
[lem-sc-bounded-below-injective-resolution]. The global-sections theorem
[lem-pur-rhom-global-sections], applied on the slice site and to M|_W[r], together with shift
compatibility in [lem-weil-pbc-ringed-internal-hom-exact-restriction], gives H^r
RHom_W(B|_W,M|_W)=Hom_D(B|_W,M|_W[r]). For r<N-b this group is zero by orthogonality of the
standard t-structure [def-sbc-standard-tstructure-derived-category], since M[r] lies in D^{≥N-r}
with N-r>b. Restriction is exact. Also [lem-pur-kinjective-restrict-localized] preserves
K-injective resolutions and [lem-weil-pbc-ringed-internal-hom-exact-restriction] identifies the
restricted H with H on the slice. For affine weakly contractible W, step 1's exact-evaluation
statement identifies these zero groups with the sections of the cohomology sheaf H^r(H(B,M)) on
W. Such W cover every affine object, by the degree-zero part of
[lem-weil-pbc-proetale-affine-acyclic-hypercover]. Therefore that sheaf is zero. This proves the
asserted uniform bound on internal Hom. These identifications apply to arbitrary B, not just
locally free complexes. For each site object W→S, clause (1) of
[lem-weil-proetale-weakly-etale-localization] gives a canonical equivalence of sites
W_proet≃S_proet/W, preserving covering families; strict equality of independently chosen small
skeleta is not needed. Transport the restricted ring sheaf R|_W and its modules along this
equivalence. Their actions and restrictions are sectionwise as in
[def-pur-localized-ringed-site], so the slice K-injective and internal-Hom theorems above apply
with these coefficients. This uses only the site-equivalence clause, not the constant-ring
identification in clauses (2) and (3); the completed coefficient ring need not be constant.
3. Here is the locality argument for C_S, including the distinction between internal and global
Hom. For any uniformly bounded-below family M_i, form α:⊕_i H(B,M_i)→H(B,⊕_i M_i). Its source
and target have the common lower bound N-b from step 2. By step 1, RΓ(W,α) is exactly the global
Hom comparison for the restricted family on every qcqs W. Conversely, if these comparisons are
isomorphisms on every qcqs W, the cone of α is zero: test on affine weakly contractible W, where
exact evaluation identifies derived evaluation with evaluation on complexes; its cohomology
sections all vanish. Such W cover every object, by
[lem-weil-pbc-proetale-affine-acyclic-hypercover] applied to affine objects, so every cohomology
sheaf of the cone is zero. Slice restriction of α is its corresponding comparison by
[lem-weil-pbc-ringed-internal-hom-exact-restriction]; restriction also commutes with sums (the
sheafified sectionwise description in [lem-weil-pbc-module-sheaves-colimits-forgetful]). Thus
C_S(B) can be checked on a pro-etale covering by qcqs objects V_a: for any qcqs W, the objects
W×_S V_a cover W, all their further qcqs slices are allowed in C_{V_a}, and the preceding cone
test shows α|_{V_a}=0 on cones, hence α is an isomorphism on W. The qcqs fibre products and
covering operations are those of [lem-weil-pbc-proetale-qcqs-finite-family-geometry]. The bound
b is fixed before this test, so no unbounded totalization is used.
4. The class C_S is closed under shifts, finite sums, direct summands and two-out-of-three in
distinguished triangles of bounded-above objects. Indeed H sends source triangles to triangles
and respects shifts by [lem-weil-pbc-ringed-internal-hom-exact-restriction]; the comparisons α
form a morphism of triangles. Direct sums of these triangles are triangles, as seen on their
mapping-cone complexes using [lem-kun-grothendieck-derived-coproducts]. In the long exact
cohomology sequences, if the comparisons for two vertices are isomorphisms, exactness gives it
for the third; a comparison on a direct summand is the corresponding direct summand of the
comparison. The unit R belongs to C_S because RHom_R(R,M)=RΓ(S,M), and the same identity holds
on every slice, so step 1 applies. Consequently R⊗_A^L P belongs to C_S for every bounded
complex P of finite projective A-modules: each projective term is a summand of a finite free
module, and the finite sequence of stupid-truncation triangles builds P from these terms. All
operations are finite; no compact-generation assertion is being used.
5. If j:U→S is a quasi-compact open immersion, then j_! carries C_U to C_S. The exact adjunction
j_!⊣j^{-1} is [lem-weil-pbc-proetale-ringed-open-closed]. It induces a derived adjunction:
restriction sends K-injectives to K-injectives, since maps into a restricted K-injective from an
acyclic complex are adjoint to maps from its acyclic exact j_!-image. Apply the chain adjunction
and [lem-weil-pbc-kinjective-hom-derived] to obtain Hom_D(j_!B,M[r])=Hom_D(B,j^{-1}M[r]) for
every r. By [lem-pur-rhom-global-sections] and shift compatibility from step 2, these are the
cohomology groups of the global derived Homs. The bijections are natural in M and hence
intertwine the canonical coproduct comparisons. Since coproducts of A-modules are exact, the
property C_U(B) implies that the comparison on S is an isomorphism on every cohomology group,
and thus an isomorphism in D(A). Restriction is exact and preserves coproducts by its
sectionwise restriction and sheafification description, so the common lower bound on M_i remains
the same on U. The argument applies on every qcqs slice W, with U_W=U×_S W; this is qcqs by
[lem-weil-pbc-proetale-qcqs-finite-family-geometry], and restriction of j_! is the extension by
zero for U_W, directly from its presheaf definition in
[lem-weil-pbc-proetale-ringed-open-closed]. This proves the required comparison on every W.
6. Let i:Z→S be closed with quasi-compact open complement h:V→S, and suppose L on Z is locally
R_Z⊗_A^L P with P a bounded finite-projective A-complex. Assume L is bounded above. We prove
C_S(i_*L). By step 3 we can first replace S by an affine open. Refine a trivializing cover of Z
by a finite cover of affine ind-etale objects Z_a→Z, using [lem-weil-pbc-ind-etale-basis]. The
lift v of [lem-weil-pbc-affine-closed-site-functor-properties] gives affine pro-etale
S_a=v(Z_a)→S with S_a×_S Z=Z_a. Together with V these S_a cover S: they cover every point of Z
and V covers its complement. They are a finite family of qcqs objects. On V, i_*L is zero. On
S_a it is i_{a,*}(R_{Z_a}⊗_A^L P_a), with i_a:Z_a→S_a. This base-change identity follows on
sheaves from (i_*F)(W)=F(W×_S Z) in [def-weil-pbc-proetale-operations]; both closed pushforwards
are exact because the complements are quasi-compact, by
[lem-weil-pbc-proetale-ringed-open-closed], so it holds termwise on representing complexes. Put
P_{S_a}=R_{S_a}⊗_A P_a and h_a:S_a\Z_a→S_a. The localization short exact sequences of the same
open-closed node, applied termwise, give the triangle
h_{a,!}(P_{S_a}|_{S_a\Z_a})→P_{S_a}→i_{a,*}(P_{S_a}|_{Z_a}). Steps 4 and 5 put its first two
vertices in C_{S_a}, so its third is in C_{S_a}. Step 3 now proves C_S(i_*L). Notice that the
trivializing cover was lifted from Z to ambient site objects; no assertion that internal Hom
commutes with arbitrary closed inverse image is made.
7. Apply [lem-weil-pbc-integral-stratified-perfect-characterization] to K. Its hypotheses are
exactly the finite extension E, noetherian finite-dimensional T, invertibility of ℓ, and the
completed A_T-module category in the statement. It gives boundedness of K and a finite
stratification on which K is pro-etale locally A_T⊗_A^L P for perfect A-complexes P.
Restrictions here use the same completed ring sheaf, not constant A coefficients or rational E
coefficients. Refine this finite stratification to a finite filtration by closed subsets with
locally perfect layers. Explicitly, express each stratum as an open intersected with a closed
subset and list the finitely many opens involved (including complements of those closed
subsets). The subset F_k of points belonging to at most k of these opens is closed: its
complement is the union of the intersections of k+1 opens. On F_k\F_{k-1} the membership
patterns form a finite clopen partition, each piece lying in one original stratum. Thus the
restriction of K to every layer is locally perfect. If m is the number of listed opens, set
F_{-1}=∅ and |F_m|=|T|; give every F_k for 0≤k≤m its reduced closed subscheme structure by
[lem-weil-pbc-reduced-induced-closed-subscheme]. Thus F_m is T_red, while its open complement is
empty. Each membership-pattern piece of a layer maps to its original stratum: affine locally the
defining ideal of the original stratum vanishes on that piece and is therefore contained in the
radical ideal defining the reduced piece. These quotient maps glue. Exact inverse image in
[def-weil-pbc-proetale-operations] carries a local finite-projective tensor description to its
pullback: each finite-projective term is a retract of a finite free module, so pulling back its
splitting gives the same tensor description with the pulled-back ring. Thus the locally perfect
assertion survives this scheme-theoretic refinement, using inverse-image coefficients
throughout. Every complement used is quasi-compact by
[lem-weil-pbc-noetherian-open-subscheme-noetherian], since T is noetherian; the same applies to
its intersections with affine opens, so the complementary open immersions are quasi-compact
morphisms. In any qcqs pro-etale base change these complements remain quasi-compact, so all
preceding steps remain applicable there.
8. Put U_k=T\F_k for -1≤k≤m, so U_{-1}=T and U_m=∅. Let j_k:U_k→T be the open immersion and
L_k=j_{k,!}(K|_{U_k}). For each 0≤k≤m, the layer Y_k=F_k\F_{k-1} is closed in U_{k-1}; write
i_k:Y_k→U_{k-1} and h_k:U_k→U_{k-1}. Its open complement is quasi-compact. Apply the
localization short exact sequence of [lem-weil-pbc-proetale-ringed-open-closed] termwise to
K|_{U_{k-1}}, then apply the exact functor j_{k-1,!}. This gives a triangle
L_k→L_{k-1}→j_{k-1,!}i_{k,*}(K|_{Y_k}). The identification of its first vertex uses the
adjunctions of the same open-closed node: for module sheaves F on U_k and G on T,
Hom(j_{k-1,!}h_{k,!}F,G)=Hom(h_{k,!}F,j_{k-1}^{-1}G)=Hom(F,h_k^{-1}j_{k-1}^{-1}G)=Hom(F,j_k^{-1}G).
Thus j_{k-1,!}h_{k,!} and j_{k,!} are canonically isomorphic as left adjoints to j_k^{-1}. This
natural identification respects the counits, and exactness permits applying it termwise to
complexes. The inverse-image restrictions compose, with coefficients always the inverse image of
A_T. By step 7, K|_{Y_k} is locally perfect and bounded above. Step 6 puts i_{k,*}(K|_{Y_k}) in
C_{U_{k-1}}, and step 5 puts the third vertex in C_T. Start with L_m=0, which lies in C_T by the
definition, and descend in k using step 4 and these triangles to obtain L_{-1}=K in C_T. This
uses localization only on the complementary opens, and requires no closed inverse-image
base-change identity.
9. Take the qcqs site object W=T in C_T(K) from step 8. This gives precisely the canonical
global derived Hom comparison in the statement, with the given common lower bound N. All
previous calculations allowed every integer N, so the shift from D^{≥0} in the source has
already been included. They identify maps induced by coprojections throughout; consequently the
isomorphism is the specified canonical map. The complexes and maps are A-linear, so the
isomorphism holds in D(A), not merely on underlying groups. The empty family gives 0→0. No
completeness or constructibility was imposed on the target family M_i or on its coproduct. -/
theorem integralConstructible_boundedBelow_compactness
    (T : Scheme.{u}) [IsNoetherian T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hdim : ∃ N : ℕ, topologicalKrullDim T ≤ (N : WithBot ℕ∞))
    (hℓ : ∀ x : T, IsUnit (ℓ : T.presheaf.stalk x))
    (K : PbcIntegralCategory ℓ E T hdim hℓ)
    (I : Type (u + 1))
    (M : I → DerivedCategory (pbcModules T
      (pbcAdicCompletion T (pbcIntegralDatum ℓ E))))
    (_hM : ∃ n : ℤ, ∀ i : I, DerivedCategory.IsGE (M i) n)
    (s : Cofan M) (_hs : IsColimit s)
    (t : Cofan (fun i : I ↦
      (adicGlobalRHom T (pbcIntegralDatum ℓ E) K.obj).obj (M i)))
    (ht : IsColimit t) :
    IsIso (ht.desc (Cofan.mk
      ((adicGlobalRHom T (pbcIntegralDatum ℓ E) K.obj).obj s.pt)
      (fun i : I ↦ (adicGlobalRHom T (pbcIntegralDatum ℓ E) K.obj).map
        (s.inj i)))) := by
  sorry

end AlgebraicGeometry.Scheme
