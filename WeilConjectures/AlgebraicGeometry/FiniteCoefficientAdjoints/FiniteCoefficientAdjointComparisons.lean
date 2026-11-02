/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteStageNormalizedAdjunction
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteStageNormalizedChange
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteStageNormalizedCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin

/-! # Assembly of the finite-coefficient exceptional adjunction system

Source: current blueprint reduction-exceptional, Locality and Charts, and
field-extension towers (blueprint: lem-pur-finite-coefficient-adjoint-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints
attribute [local irreducible] etaleUpper etaleAdjunction
  projectionAtWitness refinementAtWitness ProEtale.pbcFixedScalarExtension
  ProEtale.pbcFixedScalarExtensionComp ProEtale.normalizedOriginScalarUnit
  ProEtale.compactSupportSiteComparison
  ProEtale.derivedComparisonAdjunction

end AlgebraicGeometry.FiniteCoefficientAdjoints

namespace AlgebraicGeometry.FiniteCoefficientAdjoints

private def retainedOrigin (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : (ctf A T).FullSubcategory) :
    Scheme.FixedEtaleOriginWitness T A ⟨K.obj, K.property.plus⟩ where
  complex := ⟨(rnu A T).obj K.obj,
    ProEtale.plus_rightDerivedFunctor_comparisonLowerStar_obj K.property.plus⟩
  iso :=
    have := (ProEtale.DerivedCategory.plusEtaleOrigin_iff K.obj).mp
      K.property.plusEtaleOrigin |>.2
    asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K.obj)

/-- General finite-coefficient exceptional adjunction and normalized coefficient system.
Source: current blueprint sk-lem-sp-reduction-exceptional.proof.md and
sk-lem-sp-field-extension-towers.proof.md; the general finite-type supplement is the
15-step ordinary-derived proof of this node
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).

Proof (the node's complete ordinary-derived proof, in its original order):
1. Work first on ordinary etale sites. All schemes in a compactification are finite type over k
and hence Noetherian: apply finite-type-over-Noetherian to Spec(k), whose only ideals are 0 and
k. The coefficient rings A_n are finite local rings by the DVR and finite-quotient statements.
For E contained in F, uniqueness of the extending absolute value identifies the restriction from
F with the absolute value on E, so R is a subring of S and |t|_F<1. The DVR expansion in S
writes t=u v^e with u a unit and e>=1; hence t^nS=v^{en}S, and S/tS is finite by the finite-
quotient statement. Here is the missing finite-generation argument, rather than an invocation of
a geometric coefficient lemma. Choose representatives b_1,...,b_h in S for all elements of S/tS.
Starting with x_0=x in S, recursively choose i_r with x_r=b_{i_r}+t x_{r+1}. Then x=sum_{r<N}t^r
b_{i_r}+t^N x_N, and |t^N x_N|_F<=|t|_F^N tends to zero. For each i, the partial coefficient
sums sum_{r<N,i_r=i}t^r are Cauchy in E; completeness gives a limit a_i in the closed unit ball
R. Taking limits in the finite sum gives x=sum_i a_i b_i. Thus S is finitely generated over R,
and it is torsion-free since R and S lie in fields. The DVR finite-free lemma makes S finite
free over R; reducing a finite basis gives B=S/t^nS finite free over A=R/t^n. The ideal identity
above is independent of the units relating uniformizers. Thus every ring in the question is a
positive DVR quotient, is finite Noetherian, and is annihilated by an ell-power invertible on
every scheme here: apply the same positive-valuation expansion to ell in each valuation ring.
Choose intervals with a<=b, enlarging an interval if necessary for a zero object.
Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-l-adic-extension-absolute-value, lem-
weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, lem-weil-l-adic-
extension-complete, lem-sc-dvr-fg-torsionfree-free.

2. For any k-map h between finite-type k-schemes, lem-kun-0f10(1), interpreted by def-kun-cd,
supplies a finite c with R^q h_* M=0 for q>c for all torsion abelian sheaves. The restriction-
of-scalars comparison, applied to Z \to A, transfers this bound to A-module sheaves; the
forgetful functor is exact and detects zero objects. In particular this applies to the proper
map g and to every complementary open j used below. No assumption on the absolute cohomological
dimension of k is made. For bounded inputs, the bound implies Rh_* sends cohomological [a,b]
into [a,b+c]: filter by the finitely many cohomology truncations, use Rh_*(M[-r])=Rh_*M[-r], and
the long exact cohomology sequences of those triangles.
Uses: lem-kun-0f10, def-kun-cd, lem-sbc-canonical-restrict-scalars-functor-comparisons, lem-sf-
derived-homology-long-exact.

3. Rh_* preserves ordinary bounded constructible finite-Tor complexes for these h and DVR stages
A. Indeed thm-dg-finite-type-constructibility gives bounded constructibility. If K has Tor
amplitude [a,b], use lem-sf-etale-flat-constructible to represent K by flat constructible terms
in [a,b]. Tensoring those terms with any finite A-algebra B gives flat constructible B-module
sheaves in the same degrees: on a common finite constructible stratification their fibres are
finite modules, and B-flatness follows from (P tensor_A B) tensor_B N=P tensor_A N. In
particular K tensor_A^L kappa is bounded constructible in [a,b]. Since kappa is a finitely
presented A-module and K belongs to D^-, lem-sf-projection-finite-constant and Step 2 identify
(Rh_*K) tensor_A^L kappa with Rh_*(K tensor_A^L kappa). Its cohomology vanishes outside [a,b+c].
Apply lem-exc-residue-tor-test on the target to obtain Tor amplitude [a,b+c]. The same argument
with M=B in the projection lemma gives the canonical coefficient comparison T Rh_* K \to Rh_* T
K as an isomorphism after restriction of B-scalars. The restriction-of-scalars comparison
identifies the target with the B-linear direct image; restriction detects isomorphisms, so this
is the B-linear projection isomorphism itself, for both coefficient maps in the question.
Uses: thm-dg-finite-type-constructibility, lem-sf-etale-flat-constructible, lem-sf-projection-
finite-constant, lem-exc-residue-tor-test, lem-sbc-canonical-restrict-scalars-functor-
comparisons.

4. For an open immersion j, exact extension by zero preserves bounded constructibility: extend a
constructibility stratification on its open domain by the closed complement, on which the sheaf
is zero. Its stalks are the original stalks or zero. Consequently extension by zero takes a flat
constructible model to a flat constructible model of the same length, and the natural map T j_!
\to j_! T is an isomorphism: use a flat model and check its termwise tensor map on stalks.
Conservativity of geometric stalks proves isomorphism of this specified map. Composing with Step
3 for g proves that F_A^et=Rg_*j_! preserves D^b_ctf and that its canonical projection
comparison q is invertible. This is the projection comparison built by the geometric open/proper
operations, not a newly chosen isomorphism.
Uses: lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-extension-by-zero-stalks, lemma-weil-
pbc-geometric-stalk-conservative, lem-sf-etale-flat-constructible.

5. The ambient etale adjoint f_A^times exists by thm-amb-etale-exceptional-adjoint. Use the
unbounded compactification and composition comparisons of lem-amb-unbounded-compact-support-
comparisons; every map here is separated of finite type between Noetherian schemes. For the
local factors and their composites, thm-nagata-compactification gives compactifiability: the
targets are quasi-compact and quasi-separated (they are separated finite-type k-schemes).
Transposing its left-functor composition isomorphism by the two ambient adjunctions identifies
(gf)^times with f^times g^times on the whole ordinary derived categories, with the composite
unit and counit. Thus this use of composition does not presuppose that an exceptional image is
bounded below. Source-open locality is precisely the canonical isomorphism of lem-amb-etale-
adjoint-locality. For an open target restriction v, v_! dashv v^* and the same composition
comparison give the corresponding v^* factor in the right adjoint. All these identifications use
conjugate adjunctions and the mate-pasting identities, so their units and counits have fixed
normalizations.
Uses: thm-amb-etale-exceptional-adjoint, thm-nagata-compactification, lem-amb-unbounded-compact-
support-comparisons, lem-amb-etale-adjoint-locality, lem-weil-pbc-mate-pasting.

6. For a closed immersion i:Z\toP between finite-type k-schemes, its complementary open j is
quasi-compact since P is Noetherian. Step 2 gives the uniform vanishing required by prop-exc-
closed-tor. Theorem thm-dg-finite-type-constructibility, applied to j and a constructible sheaf
in degree zero, gives constructibility of each R^qj_* of that sheaf. Thus every hypothesis of
prop-exc-closed-tor holds, and i^times=Ri^! preserves D^b_ctf. For a projection pi:A^r_V\toV,
thm-amb-vector-bundle-purity identifies pi^times L with pi^*L(r)[2r] by the adjoint of the
stated trace. Exact inverse image preserves constructibility and flatness; the twist is locally
constant and etale locally free of rank one by lem-asd-etale-finite-twist-pullback, applied to
m=ell^s annihilating A (m is invertible on these k-schemes). Hence this expression preserves
D^b_ctf. Cover Y by finitely many affine V and each inverse image by finitely many affine U.
Finite algebra generators give a closed immersion U\toA^r_V factoring f|U. By Step 5 and open
adjunctions, u^* f^times L identifies with i^times pi^times v^*L, where u:U\toX and v:V\toY. The
right side is bounded constructible finite-Tor. These properties glue across the finite open
cover: take the minimum of the finitely many lower bounds and maximum of upper bounds, and glue
the finite constructibility stratifications. Consequently f^times preserves D^b_ctf over the
original arbitrary k.
Uses: prop-exc-closed-tor, thm-dg-finite-type-constructibility, thm-amb-vector-bundle-purity,
prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-amb-etale-adjoint-locality, lem-amb-unbounded-compact-support-comparisons, lem-asd-etale-
finite-twist-pullback.

7. For any finite coefficient ring here, etale/pro-etale comparison identifies bounded etale
constructible complexes with intrinsically constructible bounded pro-etale complexes. It also
identifies their finite-Tor subcategories. In the forward direction, pull back a bounded flat
constructible etale model: exactness of nu^* and the flat-term pullback assertion for ringed
topoi give a bounded flat model on the pro-etale site. In the reverse direction, write K=nu^*K0
by constructible derived origin; if K has Tor amplitude [a,b], its tensor with the constant
residue field has cohomology in [a,b]. Tensor-pullback compatibility identifies this with
nu^*(K0 tensor_A^L kappa). Exactness and full faithfulness of nu^* on D^+ reflect this interval,
so the residue-field Tor test shows that K0 has the same Tor amplitude. The etale origin is
bounded, so all these uses of D^+ full faithfulness are legitimate. Apply compact-support site
comparison to identify F_A nu_X^* with nu_Y^* F_A^et. It follows from Steps 4 and 6 that F_A and
G_A=nu_X^* f_A^times Rnu_{Y,*} preserve the stated pro-etale category. For K=nu_X^*K0 and
L=nu_Y^*L0 the Hom chain Hom(F_A K,L)=Hom(F_A^et K0,L0)=Hom(K0,f_A^times L0)=Hom(K,G_A L) gives
the required adjunction. Each equality uses the specified comparison and unit, so its unit and
counit are precisely the transported geometric ones. Tensor-pullback compatibility transports
the specified q of Step 4 as well.
Uses: lem-weil-pbc-finite-ring-constructible-derived-origin, lem-sf-etale-flat-constructible,
lem-sf-comparison-pullback-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, thm-weil-
pbc-site-comparison, lem-exc-residue-tor-test, lem-sf-class-compact-support-comparison.

8. For the smooth affine-space projection $\pi:\mathbf A^r_V\to V$, apply det-sp-reduction-
exceptional to $A\to B$. Step 1 verifies its finite commutative $\ell$-primary hypotheses for
both coefficient maps. It gives an invertible pro-etale coefficient mate characterized by the
displayed counit-transpose equation, with chart value the tensor reassociation of
$\pi^*(-)(r)[2r]$. Use the same standard compactification for both functors. The
site/coefficient square and the counit-transport clause of lem-sp-et-proet-coefficient-
compatibility identify the ordinary-etale projection map of Step 4, after site transport, with
the named pro-etale coefficient map in that equation. Its hypotheses hold by Steps 1, 4 and 7:
the schemes are separated finite type over $k$, and the inputs and exceptional outputs are
bounded constructible finite-Tor. By det-sp-et-proet-adjunction-transfer the transported counit
is $\nu_V^*(\epsilon_A^{\mathrm{et}})\circ c_{\pi,A}^{-1}$, exactly the counit used in Step 7.
Apply det-sp-unique-right-adjoint to identify its right adjoint with the one used in det-sp-
reduction-exceptional, preserving this counit. Under these identifications the invertible mate
satisfies $\epsilon_B F_B(b_\pi)=T\epsilon_A q_\pi^{-1}$; uniqueness of the adjunction transpose
makes it our specified $b_\pi$. The cited site/coefficient square carries this equation back to
the ordinary-etale equation. Full faithfulness of the site equivalences of Step 7 reflects
invertibility, giving the ordinary-etale projection case needed in Step 12. For $r=0$ these are
the identity adjunction and tensor reassociation.
Uses: det-sp-reduction-exceptional, lem-sp-et-proet-coefficient-compatibility, det-sp-et-proet-
adjunction-transfer, det-sp-unique-right-adjoint, thm-weil-pbc-site-comparison.

9. For a closed immersion $i:Z\hookrightarrow P$ with open complement $j$, construct support
triangles on ordinary complexes. For a module sheaf $M$ put $H(M)=i^*\ker(M\to j_*j^*M)$. The
kernel is supported on $Z$; the fully faithful supported-sheaf equivalence of lem-kun-04ca,
transported to modules by naturality for scalar multiplications, identifies it with $i_*H(M)$.
Every map $i_*N\to M$ factors uniquely through this kernel: its composite to $j_*j^*M$ is zero
under $j^*\dashv j_*$ because $j^*i_*N=0$. Hence $i_*\dashv H$, with counit the kernel
inclusion. Choose functorial degreewise-injective K-injective representatives $I$ using the
Grothendieck and replacement lemmas. On every etale $V\to P$, $V\times_P U\to V$ is monic;
injective restriction along monomorphisms gives surjectivity of $I^r(V)\to I^r(V\times_PU)$.
Thus $0\to i_*H(I)\to I\to j_*j^*I\to0$ is a natural short exact sequence of complexes. Open
restriction preserves K-injectives by the localization lemma, so the last term represents
$Rj_*j^*L$. The closed stalk formula, zero stalks off $Z$, and exact conservative stalks show
$i_*$ is exact, also on modules since exactness is detected after forgetting scalars. Exactness
of $i_*$ and the termwise adjunction show $H(I)$ represents $Ri^!L$: $H$ preserves K-injectives,
and the Hom-into-K-injective bijections derive $i_*\dashv H$ with this counit. Apply the short-
exact-sequence triangle lemma. This realizes precisely the counit/unit support triangle of lem-
exc-closed-support-triangle, with a natural connecting map.
Uses: lem-kun-04ca, lem-weil-pbc-ring-sheaves-grothendieck, lem-pur-kinjective-degreewise-
existence, lem-pur-ringed-site-injective-mono-restriction, lem-pur-kinjective-restrict-
localized, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-termwise-adjunction-
homotopy, lem-weil-pbc-kinjective-hom-derived, lem-weil-pbc-kinjective-total-derived, lem-weil-
pbc-complex-ses-triangle, lem-exc-closed-support-triangle, lemma-openclosed-stalk-lowerstar,
prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative, lem-weil-pbc-
open-immersion-etale, lem-weil-pbc-etale-site-localization-open, prop-weil-pbc-inverse-image-
modules-exact.

10. To compare support triangles for $A\to B$, it is enough to check the specified $B$-linear
mate after exact restriction of scalars. Choose a K-flat resolution $Q\to B_P$ with flat terms
over $A_P$ and use the representative $I$ of Step 9. Tensor its short exact support sequence
with $Q$. This remains degreewise exact: each tensor by $Q^r$ is exact and the sums in total
tensor are exact (direct sums are filtered colimits of finite sums in the Grothendieck module
category). Put $N=\operatorname{Tot}(Q\otimes_A I)$ and choose its functorial degreewise-
injective K-injective replacement $a:N\to J$ over $A_P$. The chain maps $a$ and $Q\otimes
j_*j^*I\to j_*(j^*Q\otimes j^*I)\xrightarrow{j_*j^*a}j_*j^*J$ commute strictly with the
restriction units, by the sectionwise tensor map and naturality. They induce a unique map of
kernels $Q\otimes i_*H(I)\to i_*H(J)$, hence a map of short exact sequences. The triangle lemma
makes it a morphism of distinguished triangles, including the connecting arrow. In the ordinary
$A$-derived category its middle map represents the identity of $\operatorname{Res}(TL)$. Its
right map is the canonical projection comparison of Step 3, identified with
$\operatorname{Res}(Rj_{*,B}j^*TL)$ by the restriction-of-scalars comparison. It is invertible.
The left map is therefore invertible by triangle two-out-of-three. This construction uses an
$A$-flat model of $B$ only after restriction; it asserts no strict $B$-action on its flat terms.
Uses: lem-pc-kflat-resolution, lem-kun-derived-tensor-well-defined, lem-weil-pbc-ring-sheaves-
grothendieck, lem-pur-kinjective-degreewise-existence, lem-weil-pbc-complex-ses-triangle, lem-
sf-triangle-morphism-iso, lem-sbc-canonical-restrict-scalars-functor-comparisons, lem-pur-sheaf-
ring-derived-coefficient-adjunction, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

11. Identify the left map with the specified mate, rather than an arbitrary triangle completion.
The $B$-coefficient support triangle, after restriction to $A$, has middle term
$\operatorname{Res}(TL)$ and right term $Rj_{*,A}j^*\operatorname{Res}(TL)$ with its unit, by
the restriction comparison. Its left term and $i_*H(J)$ are supported on $Z$. For any supported
derived object $W=i_*M$, the open adjunction gives
$\operatorname{Hom}(W,Rj_*D[r])=\operatorname{Hom}(j^*W,D[r])=0$ for every $r$. Here $j^*i_*M=0$
follows termwise from the support equivalence and exactness of inverse image. The exact Hom
sequence of a triangle therefore makes maps from $W$ to either left term bijective with maps
from $W$ to the middle term. Applying this bijection twice gives the unique counit-compatible
identification of the two left terms. The source left term of Step 10 is supported too and
identifies with $i_*\operatorname{Res}(T Ri_A^!L)$ via the closed-immersion projection
isomorphism of Step 3. Under these identifications its map to the middle term is
$T\epsilon_{i,A}$. The definition of $b_i$ says that $i_*\operatorname{Res}(b_i)$ has precisely
this same composite. Uniqueness in the Hom bijection identifies the maps, so
$i_*\operatorname{Res}(b_i)$ is invertible. Since $i^*i_*\simeq\mathrm{id}$, $i_*$ detects
isomorphisms; exact restriction of scalars detects them as well. Thus the specified $B$-linear
$b_i$ is invertible. In particular neither injectivity of a restricted $B$-injective nor
flatness of $B/A$ was assumed.
Uses: lem-exc-closed-support-triangle, lem-kun-04ca, prop-weil-pbc-inverse-image-modules-exact,
lem-weil-pbc-hom-into-triangle-exact, lem-sbc-canonical-restrict-scalars-functor-comparisons,
lem-pur-sheaf-ring-derived-coefficient-adjunction.

12. The compactification-refinement and composition equations for the specified projection maps
are exactly the last clauses of lem-sp-et-proet-coefficient-compatibility; Steps 1, 4 and 7
verify its finite-ring and bounded constructible finite-Tor hypotheses. Applying mate-pasting
now identifies the coefficient mate for a composite with the pasted mates of its factors and
identifies its restriction on each affine U of Step 6 with the composite of b_i, b_pi, and the
coefficient identity for v^*. The last identity follows directly from exact pullback commuting
with coefficient tensor. Source locality identifies this restriction with u^*b_f, with the
adjunctions transported as in Step 5. Steps 8 and 11 make it invertible on each U. Its cone has
zero cohomology on an open cover, hence zero geometric stalks; geometric-stalk conservativity
applied to the cohomology sheaves proves b_f invertible. Via Step 7 this proves invertibility of
the exact b_{A,B} in the question for quotient maps. The same argument proves it for the finite-
free map because Step 3, the smooth coefficient-mate comparison of Step 8 and the support
triangle also apply to that map. Alternatively for the finite-free map choose an A-basis of B:
both T and q identify with the same finite direct sum, and the right-adjoint mate is that
finite-sum identification by counit naturality. This alternative is only a check; the defined b
is basis-independent.
Uses: lem-weil-pbc-mate-pasting, lem-amb-unbounded-compact-support-comparisons, lem-amb-etale-
adjoint-locality, lemma-weil-pbc-geometric-stalk-conservative, lem-weil-pbc-ringed-topoi-
derived-tensor-pullback, lem-sp-et-proet-coefficient-compatibility.

13. The counit identity is the defining equation for the transpose b, so holds as an equality of
the specified maps. For the unit equation, let alpha=G_B(q_K) b_{F_A K} T_X(eta_{A,K}). Its F_B
dashv G_B transpose is epsilon_{B,F_BT_XK} F_B(alpha). Counit naturality moves q_K to the
outside, and the defining counit equation for b changes this expression to q_K (T_Y
epsilon_{A,F_AK}) q^{-1}_{G_AF_AK} F_BT_X(eta_{A,K}). Naturality of q changes the last two
factors to T_YF_A(eta_{A,K}) q_K^{-1}. The A-triangle identity now reduces the whole composite
to q_K id q_K^{-1}=id. The transpose of id is eta_{B,T_XK}, proving exactly the displayed unit
equation. This is elementary adjunction algebra, using no invertibility principle for mates.
Uses: lem-weil-pbc-mate-pasting.

14. It remains to check ordinary coefficient-system equalities. The canonical derived-tensor
associators and unitors, with their naturality and associativity diagrams, are clause (4) of
det-sp-scalar-extension-functor on the ordinary pro-etale categories; its finite commutative
primary-ring hypotheses hold by Step 1. They are computed by K-flat representatives as in clause
(1). For $A\to B\to C$, transpose the two projection composites under the derived
inverse/direct-image adjunction. Both become the same iterated evaluation $h^*Rh_*K\to K$,
extended to $C$, since the composite counit is the product of the two counits. The same argument
for open extension is termwise extension by zero and summandwise tensor. Thus the projection
composites agree, including identity coefficient maps. Step 12 gives compatibility with
compactification refinements and geometric compositions. The mate-pasting lemma now gives the
stated equalities for $b$: transpose the two candidate composites under $F_C\dashv G_C$; both
give $T_{A,C}\epsilon_A\circ q_{A,C}^{-1}$, so they coincide. The unit identity of Step 13 and
the defining counit identity are preserved under these equalities. Any mixed diagram of the
permitted quotient and finite-free maps is checked by the same transposition and tensor
reassociation, independently of bases. This concerns finite systems of ordinary functors and
natural transformations only. The right adjoints are already constructed in Steps 5–7; no right
adjoint on a category of towers or lifting of a family of derived maps is required.
Uses: det-sp-scalar-extension-functor, lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-
weil-pbc-mate-pasting.

15. Finally Step 1 writes t=u v^e with u in S^times and e>=1, so t^nS=v^{en}S and
S/t^nS=S/v^{en}S as quotient rings; the cited DVR and finite-quotient statements make these
precisely the finite local coefficient stages. The finite-free lemma applies using the finite-
generation and torsion-free hypotheses proved explicitly in Step 1, and reducing its basis gives
the finite-free extensions at each level. Given any positive integer r, choose n>=r; then en>=r.
Thus the indices en form a cofinal subsystem, and all coefficient, unit and counit comparisons
just proved restrict to it. This is only an assertion about finite coefficient systems; no
passage to inverse limits or extension to rational or condensed coefficient categories has
occurred.
Uses: lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, lem-sc-dvr-
fg-torsionfree-free.
-/
theorem finite_coefficient_adjoint_comparisons
    (k : Type u) [Field k] (p l : ℕ) [CharP k p]
    (hk : Finite k ∨ IsAlgClosed k) (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    letI := (finiteTypeMorphismProperties k f).1
    letI := (finiteTypeMorphismProperties k f).2.1
    letI := (finiteTypeMorphismProperties k f).2.2
    ∃ (S : FiniteTypeSystem l E k f),
      (∀ (s : Stage l E) (c : Compactification f) (K : (ctf s.ring X).FullSubcategory),
        ctf s.ring X K.obj → ctf s.ring Y ((lower s.ring c).obj K.obj)) ∧
      (∀ (s : Stage l E) (c : Compactification f) (K : (ctf s.ring Y).FullSubcategory),
        ctf s.ring Y K.obj → ctf s.ring X ((upper s.ring c).obj K.obj)) ∧
      (∀ (s : Stage l E) (c : Compactification f),
        Nonempty {d : (restrict (lower s.ring c) (S.datum s c).lower_preserves ⊣
            restrict (upper s.ring c) (S.datum s c).upper_preserves) //
          d = (S.datum s c).adjunction}) ∧
      (∀ (s : Stage l E) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        DerivedCategory.TStructure.t.plus
          ((etaleUpper s.ring c).obj ((rnu s.ring Y).obj K.obj))) ∧
      (∀ (s : Stage l E) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        ((S.datum s c).adjunction.counit.app K).hom =
          (ProEtale.compactSupportSiteComparison s.ring c).hom.app
              ⟨(etaleUpper s.ring c).obj ((rnu s.ring Y).obj K.obj),
                (S.datum s c).etaleBound K.obj K.property⟩ ≫
            (nu s.ring Y).map ((etaleAdjunction s.ring c).counit.app
              ((rnu s.ring Y).obj K.obj)) ≫
            (ProEtale.derivedComparisonAdjunction
              (ModuleCat.{u + 1} s.ring) Y).counit.app K.obj) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory),
        ctf s.ring X K.obj → ctf t.ring X ((tensor a.ringMap X).obj K.obj)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        ctf s.ring Y K.obj → ctf t.ring Y ((tensor a.ringMap Y).obj K.obj)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f),
        Nonempty {q : ((ctf s.ring X).ι ⋙ lower s.ring c ⋙ tensor a.ringMap Y ≅
            (ctf s.ring X).ι ⋙ tensor a.ringMap X ⋙ lower t.ring c) //
          q = (S.change a c).projection}) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f),
        Nonempty {b : ((ctf s.ring Y).ι ⋙ upper s.ring c ⋙ tensor a.ringMap X ≅
            (ctf s.ring Y).ι ⋙ tensor a.ringMap Y ⋙ upper t.ring c) //
          b = (S.change a c).mate}) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory)
          (w : Scheme.FixedEtaleOriginWitness X s.ring ⟨K.obj, K.property.plus⟩),
        DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension a.ringMap X).obj w.complex.obj)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory)
          (w : Scheme.FixedEtaleOriginWitness X s.ring ⟨K.obj, K.property.plus⟩),
        (S.change a c).projection.hom.app K =
          projectionAtWitness a.ringMap c K w
            ((S.change a c).etale_tensor_bound K w)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        (lower t.ring c).map ((S.change a c).mate.hom.app K) ≫
            (S.datum t c).counit
              ⟨(tensor a.ringMap Y).obj K.obj,
                (S.change a c).tensor_preserves_Y K.obj K.property⟩ =
          (S.change a c).projection.inv.app
              ⟨(upper s.ring c).obj K.obj,
                (S.datum s c).upper_preserves K.obj K.property⟩ ≫
            (tensor a.ringMap Y).map ((S.datum s c).counit K)) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory),
        (tensor a.ringMap X).map ((S.datum s c).unit K) ≫
            (S.change a c).mate.hom.app
              ⟨(lower s.ring c).obj K.obj,
                (S.datum s c).lower_preserves K.obj K.property⟩ ≫
            (upper t.ring c).map ((S.change a c).projection.hom.app K) =
          (S.datum t c).unit
            ⟨(tensor a.ringMap X).obj K.obj,
              (S.change a c).tensor_preserves_X K.obj K.property⟩) ∧
      (∀ (s : Stage l E) (K : (ctf s.ring X).FullSubcategory),
        ∃ w : Scheme.FixedEtaleOriginWitness X s.ring ⟨K.obj, K.property.plus⟩,
          w = S.origin_X s K) ∧
      (∀ (s : Stage l E) (K : (ctf s.ring Y).FullSubcategory),
        ∃ w : Scheme.FixedEtaleOriginWitness Y s.ring ⟨K.obj, K.property.plus⟩,
          w = S.origin_Y s K) ∧
      (∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
          (h : ab.embedding = b.embedding.comp a.embedding) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory),
        (tensor b.ringMap Y).map ((S.change a c).projection.hom.app K) ≫
            (S.change b c).projection.hom.app
              ⟨(tensor a.ringMap X).obj K.obj,
                (S.change a c).tensor_preserves_X K.obj K.property⟩ ≫
            (lower v.ring c).map
              ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
                a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
          (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
              a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
                ((lower s.ring c).obj K.obj) ≫
            (S.change ab c).projection.hom.app K) ∧
      (∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
          (h : ab.embedding = b.embedding.comp a.embedding) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        (tensor b.ringMap X).map ((S.change a c).mate.hom.app K) ≫
            (S.change b c).mate.hom.app
              ⟨(tensor a.ringMap Y).obj K.obj,
                (S.change a c).tensor_preserves_Y K.obj K.property⟩ ≫
            (upper v.ring c).map
              ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
                a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
          (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
              a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
                ((upper s.ring c).obj K.obj) ≫
            (S.change ab c).mate.hom.app K) ∧
      (∀ (s : Stage l E) (a : Arrow s s)
          (h : a.embedding = AlgHom.id (Padic l) s.field) (c : Compactification f)
          (K : (ctf s.ring X).FullSubcategory),
        (S.change a c).projection.hom.app K ≫
            (lower s.ring c).map ((ProEtale.normalizedOriginScalarUnit
              (Scheme.ProEt.topology X) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
          (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y)
            a.ringMap (Arrow.ringMap_id a h)).hom.app ((lower s.ring c).obj K.obj)) ∧
      (∀ (s : Stage l E) (a : Arrow s s)
          (h : a.embedding = AlgHom.id (Padic l) s.field) (c : Compactification f)
          (K : (ctf s.ring Y).FullSubcategory),
        (S.change a c).mate.hom.app K ≫
            (upper s.ring c).map ((ProEtale.normalizedOriginScalarUnit
              (Scheme.ProEt.topology Y) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
          (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
            a.ringMap (Arrow.ringMap_id a h)).hom.app ((upper s.ring c).obj K.obj)) ∧
      (∀ (s : Stage l E) {c d : Compactification f} (r : c.Refinement d),
        Nonempty {z : RefinementDatum r (S.datum s c) (S.datum s d) //
          z = S.refinement s r}) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) {c d : Compactification f}
          (r : c.Refinement d) (K : (ctf s.ring X).FullSubcategory),
        (tensor a.ringMap Y).map ((S.refinement s r).lowerIso.hom.app K) ≫
            (S.change a d).projection.hom.app K =
          (S.change a c).projection.hom.app K ≫
            (S.refinement t r).lowerIso.hom.app
              ⟨(tensor a.ringMap X).obj K.obj,
                (S.change a c).tensor_preserves_X K.obj K.property⟩) ∧
      (∀ {s t : Stage l E} (a : Arrow s t) {c d : Compactification f}
          (r : c.Refinement d) (K : (ctf s.ring Y).FullSubcategory),
        (tensor a.ringMap X).map ((S.refinement s r).upperIso.hom.app K) ≫
            (S.change a c).mate.hom.app K =
          (S.change a d).mate.hom.app K ≫
            (S.refinement t r).upperIso.hom.app
              ⟨(tensor a.ringMap Y).obj K.obj,
                (S.change a c).tensor_preserves_Y K.obj K.property⟩) ∧
      (∀ (s t : Stage l E) (a : Arrow s t),
        s.exponent = t.exponent → a.IsFiniteFree) ∧
      (∀ s : Stage l E, ∃ (e : ℕ+) (z : s.integersˣ),
        s.parameter = (z : s.integers) *
          Padic.coefficientExtensionUniformizer l s.field ^ (e : ℕ) ∧
        (∀ n : ℕ, Ideal.span ({s.parameter} : Set s.integers) ^ n =
          Padic.coefficientExtensionIdeal l s.field ((e : ℕ) * n)) ∧
        ∀ r : ℕ, ∃ n : ℕ+, r ≤ (e : ℕ) * (n : ℕ))  := by
  classical
  let := finiteTypeNoetherian k X
  let := finiteTypeNoetherian k Y
  let := (finiteTypeMorphismProperties k f).1
  let := (finiteTypeMorphismProperties k f).2.1
  let := (finiteTypeMorphismProperties k f).2.2
  let datum : ∀ (s : Stage l E) (c : Compactification f), AdjointDatum s.ring c :=
    fun s c ↦ (finite_stage_normalized_adjunction k p l hp hlp E f s c).choose
  let change : ∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f),
      Change a.ringMap c (datum s c) (datum t c) :=
    fun a c ↦ (finite_stage_normalized_change k p l hk hp hlp E f a c
      (datum _ c) (datum _ c)).choose
  have coherent := finite_stage_normalized_coherence k p l hp hlp E f datum change
  let refinement := coherent.choose
  have hcoh := coherent.choose_spec.1
  let S : FiniteTypeSystem l E k f :=
    { datum := datum
      change := change
      origin_X := fun s K ↦ retainedOrigin s.ring X K
      origin_Y := fun s K ↦ retainedOrigin s.ring Y K
      projection_comp := hcoh.1
      mate_comp := hcoh.2.1
      projection_id := hcoh.2.2.1
      mate_id := hcoh.2.2.2.1
      refinement := refinement
      projection_refinement := hcoh.2.2.2.2.1
      mate_refinement := hcoh.2.2.2.2.2 }
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun s c K hK ↦ (S.datum s c).lower_preserves K.obj hK
  · exact fun s c K hK ↦ (S.datum s c).upper_preserves K.obj hK
  · exact fun s c ↦ ⟨⟨(S.datum s c).adjunction, rfl⟩⟩
  · exact fun s c K ↦ (S.datum s c).etaleBound K.obj K.property
  · exact fun s c K ↦ (S.datum s c).counit_normalization K
  · exact fun a c K hK ↦ (S.change a c).tensor_preserves_X K.obj hK
  · exact fun a c K hK ↦ (S.change a c).tensor_preserves_Y K.obj hK
  · exact fun a c ↦ ⟨⟨(S.change a c).projection, rfl⟩⟩
  · exact fun a c ↦ ⟨⟨(S.change a c).mate, rfl⟩⟩
  · exact fun a c K w ↦ (S.change a c).etale_tensor_bound K w
  · exact fun a c K w ↦ (S.change a c).projection_normalization K w
  · exact fun a c K ↦ (S.change a c).counit_equation K
  · exact fun a c K ↦ (S.change a c).unit_equation K
  · exact fun s K ↦ ⟨S.origin_X s K, rfl⟩
  · exact fun s K ↦ ⟨S.origin_Y s K, rfl⟩
  · exact S.projection_comp
  · exact S.mate_comp
  · exact S.projection_id
  · exact S.mate_id
  · exact fun s c d r ↦ ⟨⟨S.refinement s r, rfl⟩⟩
  · exact S.projection_refinement
  · exact S.mate_refinement
  · exact fun s t a h ↦ stage_finiteFree a h
  · exact stage_ramification

end AlgebraicGeometry.FiniteCoefficientAdjoints
