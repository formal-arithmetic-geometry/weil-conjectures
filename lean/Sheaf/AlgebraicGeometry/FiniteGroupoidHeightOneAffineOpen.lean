module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion

import Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Sober
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts
import Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm
import WeilConjectures.Mathlib.RingTheory.Localization.NormTrace

/-!
# Invariant affine opens at height-one orbits of finite groupoid schemes

Source: Stacks Project, More on Groupoids in Spaces, Tag 0ABI,
`lemma-find-affine-codimension-1`
(blueprint: lem-sfb-finite-groupoid-height-one-affine-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite absolute groupoid on a separated locally Noetherian scheme has an invariant
 affine open containing any orbit whose local rings have Krull dimension at most one.

Source: Stacks Project, Tag 0ABI, `lemma-find-affine-codimension-1`
(blueprint: lem-sfb-finite-groupoid-height-one-affine-open).

The orbit is the image under `t` of the source fibre over `u`. It includes arrows whose
residue fields extend those of their endpoints; no rational-point or base-field restriction
is imposed. Equality of inverse-image opens is equality of the corresponding open subschemes.
Absolute separatedness is `U.IsSeparated`, separatedness over the terminal scheme Spec Z.

Proof:
1. The identity, inverse and composition laws make $O=t(s^{-1}(\{u\}))$ an equivalence class of
   points: for composition choose a common extension of the two residue fields over the common
   intermediate point. The finite fibre of $s$ shows that $O$ is finite. Every affine open of $U$
   has Noetherian coordinate ring, and each stalk is a localization of such a ring, hence
   Noetherian. Locally finite irreducible components imply that a quasi-compact open meets only
   finitely many components (take a finite subcover of the witnessing neighbourhoods). Absolute
   separatedness is a hypothesis here. Apply the common-affine-neighbourhood lemma to the finite
   set $O$, using its assumed local dimension bound, to obtain an affine open $A_0\subseteq U$
   containing $O$. Uses: def-a1-groupoid-scheme, lem-weil-pbc-finite-closed-map-finite-fibres,
   pqf-lem-affine-open-locnoeth, lem-weil-pbc-localization-noetherian,
   lem-sc-locnoeth-components-locally-finite, lem-trf-codimension-one-points-affine-neighbourhood,
   lem-weil-pbc-affine-open-stalk-localization.
2. Set $C=t(s^{-1}(U\setminus A_0))$. It is closed because $s$ is continuous and $t$ is closed. It
   is a union of orbits by inverse and composition. An orbit meeting $U\setminus A_0$ cannot be
   $O$, so $O\cap C=\varnothing$. The identity arrow gives $U\setminus A_0\subseteq C$. Thus
   $U_0=U\setminus C$ is an invariant open containing $O$ and contained in $A_0$. The Noetherian
   scheme $A_0$ has Noetherian open subscheme $U_0$. Restriction to this invariant open is
   harmless: any invariant open of $U_0$ is open and invariant in $U$. Henceforth replace $U$ by
   $U_0$; it has an immersion into an affine scheme and is Noetherian. Uses:
   def-a1-groupoid-scheme, lem-weil-pbc-finite-closed-map-finite-fibres,
   pqf-lem-affine-open-locnoeth, lem-weil-pbc-noetherian-open-subscheme-noetherian,
   lem-sfb-groupoid-subset-saturation-invariant.
3. Apply integral orbit-cover descent to the reduction $U_{\mathrm{red}}\hookrightarrow U$: it is
   a closed immersion and hence integral, its underlying map is the identity, and it meets every
   orbit. The restricted groupoid still has finite source and target. In general for a closed
   immersion $T\hookrightarrow U$, its restricted arrow scheme is $T\times_U R\times_U T$; its
   source is the composite of a closed immersion into $R\times_{s,U}T$ with the finite base change
   of $s$, and similarly for the target. This composite is finite: on affine charts a quotient of
   a finite module is finite. Reduction preserves the prime chains and the local dimension bounds.
   It therefore suffices to work with reduced $U$, remembering to descend the final invariant
   affine back to the original $U$. Uses: lem-sfb-integral-orbit-affine-descent,
   def-weil-pbc-scheme-reduction, lem-weil-pbc-closed-immersion-finite,
   lem-weil-pbc-finite-morphism-permanence, def-a1-groupoid-scheme, pqf-lem-finite-integral-lft,
   lem-weil-pbc-closed-immersion-base-change.
4. Choose the invariant open $W$ and closed thickening $W\prime\subseteq W$ of the
   almost-dense-flat-locus lemma. Since $W$ is reduced, the ideal of a closed subscheme with the
   same underlying space is zero: on each reduced affine chart its elements lie in every prime and
   hence in the zero nilradical. Thus $W\prime=W$, so the restricted maps on $W$ are finite
   locally free. Put $T=\overline{|W|}_{\mathrm{red}}$. Its inclusion is integral, and
   $U=t(s^{-1}(|T|))$ says precisely that it meets every orbit. Choose $u\prime\in O(u)\cap T$ and
   apply integral orbit-cover descent once more. Proving the result on $T$ suffices, since the
   descended invariant open contains $u\prime$, hence all of $O(u)$. Closed-subscheme local rings
   are quotients, so their prime chains are a subset of the original chains and the dimension
   bounds persist. Replace $U$ by $T$, $u$ by $u\prime$, and restrict the groupoid; now $W$ is
   dense as well as open, invariant, and finite locally free for the restricted groupoid. Uses:
   lem-sfb-finite-groupoid-almost-dense-flat-locus, lem-sfb-integral-orbit-affine-descent,
   lem-weil-pbc-reduced-induced-closed-subscheme, def-weil-closed-immersion,
   def-pc-reduced-scheme.
5. All replacements are closed subschemes of the preceding Noetherian scheme and retain an
   immersion into an affine scheme; quotient charts are Noetherian, since an ideal in a quotient
   is generated by the images of generators of its inverse image, and closed subsets of
   quasi-compact spaces are quasi-compact. Their source and target maps remain finite by the
   restricted-arrow calculation above. If $u\in W$, its entire orbit lies in $W$. The
   common-affine-neighbourhood lemma applies inside the separated locally Noetherian open $W$,
   with the same local rings at orbit points and finitely many irreducible components on
   quasi-compact opens. Then finite-locally-free invariant-affine shrinking gives the required
   invariant affine in $W$ and hence in $U$. The remembered integral descents finish this case.
   Otherwise $O(u)\cap W=\varnothing$; assume this case for the remaining steps. Uses:
   lem-trf-codimension-one-points-affine-neighbourhood,
   lem-sfb-locally-free-groupoid-invariant-affine, lem-sc-locnoeth-components-locally-finite,
   pqf-def-locnoeth, def-weil-closed-immersion, lem-trf-immersion-over-separated-base.
6. Consider every strict generalization $\xi$ of any $v\in O(u)$. The local dimension bound
   implies that $\xi$ has no strict generalization: a chain $\eta\leadsto\xi\leadsto v$ would give
   a length-two prime chain in $\mathcal O_{U,v}$. Thus $\xi$ is a component generic point: a
   component through $\xi$ exists by the component-cover lemma, and its unique generic point
   (scheme sobriety) generalizes $\xi$, hence equals $\xi$. It lies in the dense open $W$; it is
   outside $O(u)$ by orbit incomparability. There are finitely many such points
   $\xi_1,\ldots,\xi_m$, because the Noetherian scheme $U$ has finitely many irreducible
   components. The list may be empty. Uses: lem-sfb-finite-groupoid-orbit-incomparability,
   lem-weil-pbc-noetherian-finitely-many-components, def-weil-pbc-krull-dimension-ring,
   def-sc-generic-point, lem-sc-irreducible-components-cover, lem-sc-scheme-sober,
   lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-prime-residue-field-iso.
7. The $R_W$-orbit of each $\xi_j$ consists of component generic points. A point has no proper
   generalization exactly when it is a component generic point: take a component through it and
   its unique generic point, using component cover and sobriety. For an arrow $r$ with
   $s_W(r)=\xi_j$, any generalization $r'$ maps under $s_W$ to $\xi_j$; integral incomparability
   in affine charts forces $r'=r$. For the target, put $B=\mathcal O_{W,t_W(r)}$ and $C=\mathcal
   O_{R_W,r}$. The map $B\to C$ is flat by the definition of flatness, and its maximal ideal
   contracts to the maximal ideal of $B$. Any generalization $v$ of $t_W(r)$ corresponds to a
   prime $\mathfrak p$ of $B$, by the canonical local-spectrum morphism. Apply flat going down to
   $\mathfrak p\subseteq\mathfrak m_B$ and $\mathfrak m_C$: it gives a prime $\mathfrak
   q\subseteq\mathfrak m_C$ contracting to $\mathfrak p$. The canonical morphism
   $\operatorname{Spec}C\to R_W$ sends $\mathfrak q$ to a generalization $r'$ of $r$ with
   $t_W(r')=v$ (in affine charts this is contraction of primes). Thus $r'=r$ and $v=t_W(r)$. The
   target has no proper generalization, so is a component generic point of $W$ and of $U$: every
   generalization of a point of the open $W$ lies in $W$. Uses:
   lem-weil-pbc-integral-incomparability, lem-sc-irreducible-components-cover,
   lem-sc-scheme-sober, def-weil-finite-integral-morphism, def-sc-generic-point,
   pqf-lem-finite-integral-lft, def-pc-finite-locally-free, lem-sc-flat-going-down,
   def-weil-flat-morphism, lem-weil-pbc-spec-local-ring-canonical-morphism.
8. Fix an immersion $j:U\to\operatorname{Spec}A$ inherited from the preceding replacements. Let
   $H=\overline{j(U)}$. The image $j(U)$ is open in $H$, and $j(W)$ is open in $j(U)$, hence open
   in $H$. Choose ideals $I,J\subseteq A$ with $V(I)=H\setminus j(U)$ and $V(J)=H\setminus j(W)$;
   these are closed subsets of $\operatorname{Spec}A$. Thus $V(I)\cup j(U)=H$, $V(J)\cup j(W)=H$,
   and both required disjointness conditions hold. The finite maps on the locally Noetherian
   schemes $U$ and $W$ are of finite presentation. Apply the almost-invariant-function lemma to
   $W$, $j|_W$, $J$, and the list $\xi_j$. It gives $f\in J$ with $F=j^{-1}D(f)\subseteq W$ affine
   and invariant, containing all $\xi_j$. The inclusion follows because $j(U\setminus W)\subseteq
   V(J)$; invariance in $W$ and invariance of $W$ imply invariance in $U$. Uses:
   def-weil-closed-immersion, pqf-lem-finite-fp-locnoeth,
   lem-sfb-finite-groupoid-almost-invariant-function.
9. Let $Z$ be the reduced induced closed subscheme on $U\setminus F=j^{-1}V(f)$. Its underlying
   set is a union of orbits, although $Z$ need not be scheme-theoretically invariant. Restrict the
   groupoid using $R_Z=Z\times_U R\times_U Z$. Its maps are finite by the
   closed-immersion/finite-base-change calculation in step 3. Over common field extensions this
   restriction retains exactly the arrows whose endpoints lie in $Z$, so the $R_Z$-orbit of $u$ is
   precisely $O(u)$. Every strict generalization of a point of $O(u)$ was among the $\xi_j$ and
   belongs to $F$. There are therefore no strict generalizations inside $Z$ at any orbit point:
   all points of $O(u)$ are generic points of components of $Z$. This proves the local
   dimension-zero assertion directly from the prime chains. Uses:
   lem-weil-pbc-reduced-induced-closed-subscheme, def-a1-groupoid-scheme,
   lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-closed-immersion-finite,
   def-weil-pbc-krull-dimension-ring, def-sc-generic-point, lem-sc-irreducible-components-cover,
   lem-sc-scheme-sober.
10. The finite groupoid on $Z$ is of finite presentation, since $Z$ is locally Noetherian.
   Restrict $j$ to $Z$. The ideal $I$ from step 8 is disjoint from $j(Z)$ and $V(I)\cup j(Z)$ is
   closed: it is the complement of the open $j(F)$ in $H$. Apply the almost-invariant-function
   lemma to this immersion, $I$, and the point $u$, whose whole orbit is now generic in $Z$.
   Obtain $h\in I$ such that $Z_h=Z\cap j^{-1}D(h)$ is affine, invariant for the restricted
   groupoid, and contains $O(u)$. No scheme-theoretic invariance of $Z$ in $U$ was assumed or
   used. Uses: pqf-lem-finite-fp-locnoeth, lem-sfb-finite-groupoid-almost-invariant-function.
11. Work only on the invariant affine $F\subseteq W$. Its arrow scheme $R_F$ is affine since its
   source $s_F$ is finite and $F$ is affine. Form the determinant norm
   $g=\operatorname{Norm}_{s_F}(t_F^*(j^*h|_F))\in\Gamma(F,\mathcal O_F)$. The norm-chart theorem
   constructs it even with varying local rank. The affine groupoid norm lemma makes $g$ invariant.
   The prime norm criterion, applied on the finite free charts, says that $g(x)\ne0$ exactly when
   $h(t(r))\ne0$ for every arrow $r$ with $s(r)=x$. The identity arrow then gives $F_g\subseteq
   j^{-1}D(h)$. Invariance of $g$ gives invariance of $F_g$ in $F$ and thus in $U$. Moreover $F_g$
   is affine, being the principal open of the affine scheme $F$. Uses:
   lem-weil-pbc-finite-morphism-permanence, lem-pd-finite-locally-free-norm-charts,
   lem-a1-affine-groupoid-invariant-norm, lem-pd-finite-free-norm-prime-criterion,
   def-weil-affine-spectrum.
12. Set $V=F_g\cup Z_h$ as a subset of $U$. It contains $O(u)$ and is a union of orbits, since $F$
   and its complement $|Z|$ are invariant and each of the two pieces is invariant for the
   corresponding restriction. It is constructible: $F_g$ is open and $Z_h$ is locally closed in
   the Noetherian space $U$. To show $V$ open we check stability under generalization; $F_g$
   already is open, so only a specialization $x\leadsto z$ with $z\in Z_h$ needs consideration. If
   $x\in Z$, nonvanishing of $h$ at $z$ implies its nonvanishing at $x$, so $x\in Z_h$. Uses:
   def-weil-constructible-subset, def-a1-groupoid-scheme.
13. If instead $x\notin Z$, then $x\in F$. Suppose $x\notin F_g$. The norm criterion supplies
   $r_1\in R_F$ with $s(r_1)=x$ and $h(t(r_1))=0$. Since $s:R\to U$ is closed, the closed-map
   specialization lemma lifts $x\leadsto z$ to $r_1\leadsto r_2$ with $s(r_2)=z$. The zero locus
   of the global section $j^*h$ is closed, so $h(t(r_2))=0$. But $t(r_2)$ is in the orbit of $z$,
   hence in $Z_h$ by invariance there; this contradicts its zero value of $h$. Therefore every
   such $x$ lies in $F_g$, establishing stability under generalization. On each affine chart of
   $U$ the constructible subset $V$ is now generalization stable, so the spectrum constructibility
   lemma makes it open. These local opens show that $V$ is open in $U$. Uses:
   lem-pd-finite-free-norm-prime-criterion, lem-weil-pbc-finite-closed-map-finite-fibres,
   lem-trf-closed-map-specializing, lem-trf-spectrum-constructible-generalization-open.
14. We have $V\subseteq j^{-1}D(h)$, hence an immersion $j\prime:V\to\operatorname{Spec}A_h$. It
   is quasi-compact, since $V$ is an open subscheme of the Noetherian $U$. For the image
   $f\prime\in A_h$ of $f$, its inverse-image principal open is $F_g$, which is affine. Also
   $j\prime(V)\cap V(f\prime)=j(Z_h)$ is closed in $\operatorname{Spec}A_h$: the equality
   $V(I)\cup j(U)=H$ and $h\in I$ imply $j(U)\cap D(h)=H\cap D(h)$, closed in $D(h)$, and
   intersecting with $V(f)$ gives exactly $j(Z_h)$. Apply the immersion-principal-affineness
   criterion to $(j\prime,f\prime)$ to obtain that $V$ is affine. It is invariant and contains
   $O(u)$. Finally apply the two integral orbit-cover descents remembered in steps 3 and 4, and
   include the resulting open into the original invariant open from step 2. Each descended
   invariant open contains the distinguished point, hence its full orbit by the identity, inverse
   and composition laws. This gives the asserted affine $W$ in the original $U$ with equality of
   source and target inverse-image opens. Uses: lem-weil-pbc-noetherian-open-subscheme-noetherian,
   lem-sfb-immersion-principal-affineness, lem-sfb-integral-orbit-affine-descent,
   def-weil-affine-spectrum, def-a1-groupoid-scheme. -/
theorem exists_isAffineOpen_invariant_of_orbit_stalk_dimension_le_one
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (_hG : IsGroupoidScheme s t e i c)
    [IsFinite s] [IsFinite t] [IsLocallyNoetherian U] [U.IsSeparated] (u : U)
    (_hdim : ∀ w ∈ t '' (s ⁻¹' ({u} : Set U)), ringKrullDim (U.presheaf.stalk w) ≤ 1) :
    ∃ W : U.Opens, IsAffineOpen W ∧
      t '' (s ⁻¹' ({u} : Set U)) ⊆ (W : Set U) ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W := by
  sorry

end AlgebraicGeometry
