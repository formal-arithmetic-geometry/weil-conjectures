module

public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.ConstructibleAffineFreePresentationGeneral
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.SheafTensorStructure
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CoefficientHeartClosure
import Sheaf.Paper.CoefficientHeartSmall
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.FiniteDiscreteCoefficientEncoding
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteConstructibleEncoding
import Sheaf.Paper.FiniteDiscreteRestrictionEncoding
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Sheaf.Paper.IntegralConstantModelHeartClosure
import Sheaf.Paper.InternalModuleAbEquivalence
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Thick and essentially small constructible finite-Tor complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-brown-hypotheses,
node det-brown-hypotheses-small (blueprint: det-brown-hypotheses-small).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a Noetherian scheme and one of the six admissible condensed coefficient rings,
the bounded constructible finite-Tor complexes form a thick essentially small subcategory.
The alternatives in `_hΛ` are finite discrete `A` killed by an `l`-power, `ℤ_[l]`,
`𝒪_E`, `ℚ_[l]`, `E`, and the finite-subextension-valued condensed `ℚ̄_l`.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-brown-hypotheses,
node det-brown-hypotheses-small (blueprint: det-brown-hypotheses-small).

Proof plan (the thirteen steps of the node):
1. Work in the fixed universe and small-site skeleton convention. Put $\mathcal
M=\Mod_{\Lambda_X}$ and $\mathcal T=D(\mathcal M)$. The sheaf-tensor structure theorem supplies
abelian sheafification and its strong symmetric monoidal structure on this small site, so the
hypotheses of the internal/sectionwise equivalence hold. That equivalence identifies $\mathcal M$
with sheaves of modules over the corresponding ring sheaf, preserving underlying abelian sheaves
and restrictions. The small ringed-site theorem makes this category Grothendieck abelian. For two
module sheaves, their morphisms are a subset of the product, over the small site, of the sets of
sectionwise module homomorphisms, hence form a small set. The Grothendieck category therefore has
K-injective resolutions, and the locally-small-derived-category theorem gives small ambient Hom
sets, in the same universe as the site and coefficient modules. In particular all Hom sets used in
the counting argument below are small; this does not assume that the collection of all objects of
$\mathcal M$ is small.
Uses: def-weil-size-convention, det-def-sfb-sheaf-tensor-structure,
def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-weil-pbc-ring-sheaves-grothendieck,
lem-sfb-grothendieck-k-injective, lem-pc-derived-category-locally-small.

2. First treat a finite discrete admissible ring $A$. The finite-discrete condensed/constant-ring
isomorphism and its scheme pullback identify the pulled-back coefficient ring with the sheafified
constant ring. The internal-module equivalence in abelian groups supplies the scalar encoding $G$;
use the common encoding $E_T$ on each scheme $T$. The restriction comparison identifies
$j^*(E_X^{-1}M)$ with the encoded restriction of $M$ for every stratum immersion $j$. Thus an
internal constructible module gives an intrinsically constructible ordinary $A$-module sheaf.
Conversely, a local constant finite $A$-module $P$ is finitely presented (a surjection from a
finite free module has finite, hence finitely generated, kernel), and its internal image is the
scalar local model $A_T\otimes_A P$: write $P$ as a cokernel of a matrix $A^m\to A^n$; the
encoding sends the constant regular module to the regular internal module and preserves finite
sums and cokernels, so the encoded presentation is the same scalar matrix on $A_T^m\to A_T^n$.
Applying this on the same finite stratification proves the converse. Consequently $E_X$ identifies
the two constructible hearts. As an equivalence of abelian categories it preserves kernels and
cokernels by their universal properties; applying it termwise therefore gives a derived
equivalence preserving cohomology and cone triangles. This coefficient identification is used only
for finite discrete $A$.
Uses: lem-weil-pbc-finite-discrete-condensed-ring-constant,
lem-weil-pbc-finite-discrete-scheme-ring-constant, lem-weil-pbc-internal-module-ab-equivalence,
def-weil-pbc-common-finite-discrete-encoding, lem-weil-pbc-finite-discrete-restriction-encoding,
lem-weil-pbc-finite-discrete-constructible-encoding, sk-def-sfb-constructible,
def-weil-abstract-derived-category.

3. For finite $A$, the equivalence between intrinsically constructible pro-étale and étale sheaves
reduces smallness of the heart to the étale case. Choose a small skeleton of the étale site. A
finite ring is Noetherian because every ideal is a finite set and its elements generate it. The
locally-Noetherian quasi-separatedness theorem applies to $X$; together with its assumed
quasi-compactness this makes $X$ qcqs. Therefore the affine-free presentation theorem applies:
every constructible étale $A$-module is a cokernel of a map between two finite sums of free
sheaves $A[h_U]$, with $U$ affine étale. Finite lists of objects of the chosen site form a set,
and for each pair of lists the maps between the corresponding free sheaves form a set. Choose one
cokernel for each such map. Their set of isomorphism classes contains every constructible étale
sheaf, so the finite-coefficient constructible heart is essentially small. This counts
presentations, not all arbitrary sheaves on the site.
Uses: lem-weil-pbc-locally-noetherian-quasi-separated,
lem-weil-pbc-finite-ring-constructible-sheaf-origin,
new-constructible-affine-free-presentation-general, def-weil-size-convention.

4. For $\Lambda=E$ or $\Qlb$, the coefficient-heart closure theorem gives kernels, cokernels and
extensions in the ambient module category, and the coefficient-heart smallness theorem supplies a
set of representatives. For $\Lambda=\mathcal O_E$, apply the integral scalar-constant
heart-closure lemma: its coefficient object is the same $p_X^*\underline{\mathcal O_E}$, and its
local models are exactly the finitely presented scalar-module models in the definition used here.
It gives ambient kernels, cokernels and extensions under the present Noetherian hypothesis,
without imposing a ground field or finite-type hypothesis on $X$. Integral-heart smallness is
proved in steps 5–7. The cases $\mathbf Q_\ell$ and $\mathbf Z_\ell$ are respectively $E=\mathbf
Q_\ell$ and its valuation ring. Zero is constructible by its rank-zero local model.
Uses: det-lem-coefficient-heart-closure, det-lem-coefficient-heart-small,
lem-sfb-integral-constant-model-heart-closure, sk-def-sfb-constructible.

5. Fix integral coefficients and one stratum $T$. Its pro-étale site has a small skeleton in the
fixed universe. For the weakly étale objects of a covering, the localization theorem identifies
their pro-étale sites with the corresponding slice sites; cartesian coefficients identify the
restrictions of the coefficient sheaves. Thus the local model identifications can be read as
ordinary restrictions of module sheaves on those slices. Finitely presented scalar $\mathcal
O_E$-modules have a set of representatives: take cokernels of all finite matrices over the set
$\mathcal O_E$. The finite constant local model definition says that any local-model sheaf on $T$
is given on a covering family by the corresponding sheaves $R_U\otimes_{\mathcal O_E}P$. Cover
families can be chosen from a set by removing repeated arrows in the small site, and assignments
of these scalar presentations form a set. Between two fixed model sheaves on an overlap, morphisms
form a set: they are natural linear families in the product of sectionwise function sets over the
small slice site. Thus overlap isomorphisms satisfying the cocycle condition form a set. These
data determine a realization up to isomorphism: local identifications of two realizations agree on
overlaps, so the equalizer sheaf axiom glues a unique morphism on sections; glue the inverses too.
The glued maps are natural and linear because these properties hold locally and the sheaf axiom
detects equality. Retain only data having a realization and choose one realization for each. This
gives a set of local-model sheaves on every fixed stratum, without asserting effectivity for
arbitrary descent data.
Uses: def-weil-size-convention, def-weil-pbc-proetale-site, sk-def-sfb-constructible,
def-weil-pbc-sites-and-cohomology, def-weil-sheaf-of-modules-category,
lem-weil-proetale-weakly-etale-localization, sk-prop-sfb-cartesian-coefficients.

6. For a finite stratification $(a_s:T_s\to X)_s$ and a tuple of local-model sheaves $F_s$ from
step 5, form the finite product $P=\prod_s a_{s*}F_s$. The module pushforward/pullback adjunction
and cartesian coefficient statement give $a_s^*\dashv a_{s*}$, with $a_s^*$ exact and its
underlying abelian-sheaf functor equal to $a_s^{-1}$ up to the stated canonical natural
isomorphism. For a constructible module $F$ with chosen $\varphi_s:a_s^*F\simeq F_s$, define
$u:F\to P$ by $u_s=a_{s*}(\varphi_s)\circ\eta_{s,F}$. Let $N=\ker u$. Exactness identifies
$a_s^*N$ with $\ker(a_s^*u)$. The component $a_s^*u_s$ has left inverse
$\varepsilon_{s,a_s^*F}\circ a_s^*a_{s*}(\varphi_s^{-1})$: its composite with $a_s^*u_s$ is the
identity by the adjunction triangle identity. Thus this component is monic and $a_s^*N=0$. On
underlying abelian sheaves this says $a_s^{-1}U(N)=0$ for every $s$. Apply the Noetherian
finite-stratum zero-detection theorem with identity covers on the strata to get $U(N)=0$, hence
$N=0$. Therefore every such $F$ embeds in $P$. Only untwisted $\mathcal O_E$ coefficients are
used, so the cartesian theorem requires no invertibility hypothesis on $X$.
Uses: sk-def-sfb-module-pushforward-pullback, sk-prop-sfb-cartesian-coefficients,
lem-weil-pbc-noetherian-stratum-detection, def-weil-sheaf-of-modules-category.

7. The finite stratifications of the fixed bounded scheme $X$ form a set: choose finite lists of
locally closed subsets and bounded scheme structures and immersion maps with those images. For
each stratification, step 5 supplies a set of tuples $(F_s)_s$, hence a set of sheaves $P$ in step
6. For fixed $P$, its subobjects form a set directly. Kernels of module-sheaf maps are computed
sectionwise, so a monomorphism is sectionwise injective and may be identified with its image
subsheaf. Such an image specifies a subset of $P(V)$ for every object $V$ of the small site,
subject to restriction, module and sheaf axioms. All these choices lie in the set $\prod_V\mathcal
P(P(V))$. Taking their union over the set of $P$ gives a set of representatives for all integral
constructible sheaves by step 6. This proves integral-heart essential smallness under the original
Noetherian hypothesis. For empty $X$, the empty stratification gives the zero module sheaf and the
argument includes it.
Uses: def-weil-size-convention, def-constructible-stratification,
def-weil-sheaf-of-modules-category.

8. For finite $A$, apply the inverse derived equivalence of step 2 to a triangle of internal
modules. It remains distinguished and its cohomology is the ordinary encoding of the internal
cohomology. The bounded-constructible pro-étale theorem puts the third vertex in the ordinary
bounded-constructible subcategory whenever the other two are there. Applying the derived
equivalence back, and using its identification of constructible hearts from step 2, proves the
corresponding closure for internal modules; the zero object and shifts are preserved as well. Thus
$\Dbc(X,A)$ is triangulated. For the other coefficients, apply the weak-Serre cohomology theorem
to the zero-containing heart in step 4: closure under kernels, cokernels and extensions is
precisely its hypothesis. This gives that $\Dbc(X,\Lambda)$ is triangulated. Concretely, shifts
reindex cohomology, and for a triangle $K\to L\to M\to K[1]$ the long exact cohomology sequence
gives a short exact sequence with middle term $H^n(L)$, left term
$\operatorname{coker}(H^{n-1}(M)\to H^n(K))$ and right term $\ker(H^n(M)\to H^{n+1}(K))$. Thus
constructibility and a finite cohomological range are preserved. In the finite case we will also
need kernel closure in the heart: for $F,G$ in that heart, the cone of $F[0]\to G[0]$ is bounded
constructible, and its cohomology in degrees $-1,0$ is respectively the kernel and cokernel of
$F\to G$. This follows from the same long exact sequence.
Uses: lem-weil-proetale-dbc-triangulated, lem-sbc-cohomology-in-weak-serre-subcategory,
lem-sf-derived-homology-long-exact, lem-sp-derived-cohomology-shift,
det-def-sfb-constructible-tor-amplitude.

9. Let $L$ be an ambient retract of $K\in\Dbc$: choose $i:L\to K$ and $r:K\to L$ with $ri=1_L$.
Functoriality gives $H^n(r)H^n(i)=1$, so $H^n(L)$ is zero whenever $H^n(K)$ is zero. On $H^n(K)$
put $e=H^n(i)H^n(r)$. The split monomorphism $H^n(i)$ identifies $H^n(L)$ with $\ker(1-e)$:
$(1-e)H^n(i)=0$, and any $x$ with $(1-e)x=0$ satisfies $x=H^n(i)H^n(r)x$. The kernel closure of
the appropriate heart from steps 4 and 8 makes this sheaf constructible. Hence $\Dbc$ is closed
under all ambient retracts. Together with step 8 and the definition of thick, it is a thick
subcategory.
Uses: def-weil-abstract-derived-category, pur9-def-thick.

10. The well-definedness assertions of the Tor-amplitude node give closure of finite Tor amplitude
under shifts, triangles and retracts for these same internal module categories. The interval
bookkeeping is as follows. A shift $K[n]$ changes $[a,b]$ to $[a-n,b-n]$. If the first and third
terms of a triangle have finite amplitude, enlarge their intervals to a common interval $[a,b]$;
the middle term then has amplitude in $[a,b]$. In particular, if $K\to L\to C\to K[1]$ is a cone
triangle with $K$ of amplitude $[a_K,b_K]$ and $L$ of amplitude $[a_L,b_L]$, rotate and use the
bounds for $L$ and $K[1]$: $C$ has amplitude in $[\min(a_L,a_K-1),\max(b_L,b_K-1)]$. A retract has
the same amplitude bound as the object of which it is a retract. Therefore
$\Dctf=\Dbc\cap\{\text{finite Tor amplitude}\}$ is an intersection of thick subcategories, and is
thick: each closure operation preserves both defining predicates. In particular this argument does
not assert that standard truncation preserves finite Tor amplitude.
Uses: det-def-sfb-constructible-tor-amplitude, pur9-def-thick.

11. Choose a set $S$ of representatives for the constructible heart, using steps 3, 4 and 7. For a
complex $K$ with constructible cohomology supported in $[a,b]$, put $T_q=\tau_{\leq q}K$. The
explicit truncation formula shows that $H^r(T_q)=H^r(K)$ for $r\leq q$ and zero for $r>q$: below
$q$ the differential is unchanged and at $q$ the quotient is
$\ker(d^q)/\operatorname{im}(d^{q-1})$. Thus $T_{a-1}\simeq0$ and $T_b\simeq K$ by
quasi-isomorphisms, and the truncation-step triangle is $T_{q-1}\to T_q\to
H^q(K)[-q]\xrightarrow{\delta_q}T_{q-1}[1]$. These are truncations in the ambient $D(\mathcal M)$;
no Tor condition is imposed on them.
Uses: lem-weil-pbc-truncation-triangle, def-weil-abstract-derived-category.

12. Fix integers $a\leq b$ and construct a set of representatives for bounded constructible
objects with cohomology in $[a,q]$, by induction on $q=a-1,\ldots,b$. Start at $q=a-1$ with the
single zero object. Given a set $R_{q-1}$ covering all isomorphism classes at the previous stage,
consider every pair $B\in R_{q-1}$, $C\in S$ and every morphism $f:C[-q-1]\to B$. These morphisms
range over a set by step 1. Choose one cone for each $f$ and retain those cones with constructible
cohomology in $[a,q]$; this is still a set. Every $K$ in this interval occurs up to isomorphism:
step 11 and inverse rotation express it as a cone of $-\delta_q[-1]:H^q(K)[-q-1]\to T_{q-1}$.
Choose isomorphisms $\beta:T_{q-1}\xrightarrow{\sim}B$ and $\gamma:H^q(K)\xrightarrow{\sim}C$. The
counted arrow is explicitly $f=\beta\circ(-\delta_q[-1])\circ\gamma[-q-1]^{-1}$. Replacing the
first two vertices by these isomorphic representatives gives a distinguished triangle starting
with $f$ and having third vertex isomorphic to $K$. Cones of a fixed arrow are isomorphic: TR3
extends the identities on the first two vertices to a triangle morphism, and the two-isomorphisms
theorem makes its third component invertible. Thus the chosen cone covers $K$. This proves the
induction, including $q=a$, when the previous term is zero; it does not require a functorial cone.
Uses: def-weil-triangulated-category, lem-sf-triangle-morphism-iso.

13. Take the union of the representative sets in step 12 over the set of pairs $(a,b)\in\mathbf
Z^2$ with $a\leq b$. It covers every bounded constructible object, so $\Dbc$ is essentially small.
Finite Tor amplitude is invariant under isomorphism. Retain exactly those representatives with
finite Tor amplitude; any $K\in\Dctf$ is isomorphic to a retained representative. The full
subcategory $\Dctf$ is therefore essentially small. If $X$ is empty or the coefficient ring is
zero, all these categories have only the zero object up to isomorphism and the same construction
applies.
Uses: det-def-sfb-constructible-tor-amplitude.
-/
theorem det_brown_hypotheses_small
    (l : ℕ) [Fact l.Prime]
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, (l ^ n : A) = 0)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[l])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj l E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[l])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj l)))
    (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X] :
    (constantModelBoundedConstructible Λ X ⊓
      (fun K => DerivedCategory.finiteTorAmplitude _ K)).IsTriangulated ∧
    (constantModelBoundedConstructible Λ X ⊓
      (fun K => DerivedCategory.finiteTorAmplitude _ K)).IsClosedUnderIsomorphisms ∧
    (constantModelBoundedConstructible Λ X ⊓
      (fun K => DerivedCategory.finiteTorAmplitude _ K)).IsStableUnderRetracts ∧
    ObjectProperty.EssentiallySmall.{u + 1}
      (constantModelBoundedConstructible Λ X ⊓
        (fun K => DerivedCategory.finiteTorAmplitude _ K)) := by
  sorry

end AlgebraicGeometry.ProEtale

end
