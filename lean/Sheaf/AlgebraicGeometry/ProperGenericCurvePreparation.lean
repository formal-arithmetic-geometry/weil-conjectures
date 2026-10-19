/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.FunctionField
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.Blowup.InvertibleCenter
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.Blowup.Affine.ChartAlgebra
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.RingTheory.NagataRing
import Sheaf.AlgebraicGeometry.NagataAffineOpensProjective
import Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Sheaf.AlgebraicGeometry.NowhereDenseDimZero
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Sheaf.AlgebraicGeometry.NormalizationInseparableBaseChange
import Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve
import Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep
import Sheaf.RingTheory.PurelyInseparableBaseChangeLocalRing
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.FiniteDegree.Algebra

/-!
# Proper generic curve preparation with a Cartier marking

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IX, Section 1.3,
printed p. 132; Stacks Project, Tags 0BXT and 030R
(blueprint: lem-per-proper-generic-curve-preparation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Compactify an affine relative curve and prepare its generic fibre and marking by
inseparable normalization, Stein factorization and a blowup.
Source: ILO, Expose IX, Section 1.3, printed p. 132; Stacks Tags 0BXT and 030R
(blueprint: lem-per-proper-generic-curve-preparation).

The integral certificate on the dense open `U.toScheme` only makes its function field
available to Lean. The map `φ : k(W) → k(P)` is the canonical generic-field map:
its composition with restriction to `U` equals the generic stalk map of `h`.
Restriction along a dense open is an isomorphism, so this equation determines `φ` uniquely.
The algebra in the degree clause is required to be exactly the one induced by `φ`.
The marking's generic fibre is the fibre of `E.subschemeι ≫ f`, with its scheme structure,
so finite etaleness includes reducedness and allows the empty divisor.

Proof, following the node's 24 steps:
1. Write $Y_0=\operatorname{Spec}A$ and $W=\operatorname{Spec}R$. Finite type gives finitely many
   generators of the $A$-algebra $R$, hence a surjection $A[x_1,\ldots,x_m]\twoheadrightarrow R$
   and a closed immersion $W\hookrightarrow\mathbf A^m_{Y_0}$. Use
   [det-nagata-affine-opens-projective] to obtain the schematic closure $C\subset\mathbf
   P^m_{Y_0}$ and a dense open immersion $W\hookrightarrow C$, with $C\to Y_0$ proper. The scheme
   $C$ is integral: its space is the closure of the irreducible $W$, and its structure sheaf
   injects into the direct image of $\mathcal O_W$ by schematic density; on every nonempty open
   its section ring therefore embeds in the function field $k(W)$. In particular its affine rings
   are domains.
2. The scheme $C$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. It is excellent:
   its finite-type affine charts over the excellent ring $A$ are excellent by
   [lem-exc-finite-type-localization-excellent], and [lem-trf-excellent-scheme-affine-cover]
   promotes this to every affine open. Write $f_C:C\to Y_0$ for the structural map. Put $B=Y_0$
   and let $Z\subset C$ be the reduced closed subscheme supported on the closure of $Z_W$
   [lem-weil-pbc-reduced-induced-closed-subscheme]. This closure omits the generic point and
   intersects $W$ in exactly $Z_W$, because $Z_W$ is closed in $W$. The integral generic fibre
   $C_\eta$ has the same function field as the dense open $W_\eta$;
   [lem-sc-closed-irreducible-dimension-trdeg] makes both dimensions one. The notation $B,C,Z$ is
   used in the next steps; the auxiliary component denoted $T$ there is different from the
   original $W$.
3. Put $k=\kappa(B)$ and $X=C_\eta$. This is a proper finite-type $k$-scheme by
   [lem-weil-pbc-proper-fp-permanence](b) and [def-weil-proper-morphism]. It is integral: over a
   nonempty affine $\operatorname{Spec}A\subset B$, an affine chart $\operatorname{Spec}R\subset
   C$ has generic fibre $\operatorname{Spec}((A\setminus\{0\})^{-1}R)$; dominance gives injections
   $A\subset R\subset\kappa(C)$, so this is a nonzero domain with fraction field $\kappa(C)$, by
   [lem-sc-integral-function-field-affine-fraction]. These charts have the same generic point,
   that of $C$, so their union is integral. Its dimension is $1$ by hypothesis. The closed subset
   $Z_\eta$ omits this generic point because $Z\ne C$. Give all closed inverse images below their
   reduced induced structure [lem-weil-pbc-reduced-induced-closed-subscheme].
4. Apply [lem-weil-pbc-normalization-geonormal-insep] to $X$. Obtain a finite purely inseparable
   extension $k_1/k$ such that the normalization $N_1$ of $(X_{k_1})_{\mathrm{red}}$ is
   geometrically normal over $k_1$. By [lem-pc-homeo-pure-insep], $X_{k_1}$ is irreducible and has
   dimension $1$, so its reduction is integral of dimension $1$. By [lem-sc-normalization-exists],
   $N_1$ is integral, finite over that reduction, of finite type over $k_1$, and of dimension $1$.
   Thus [lem-weil-pbc-geonormal-dim-one-smooth] makes $N_1$ smooth. We have not inferred anything
   about the boundary from this smoothness.
5. Let $D_1\subset N_1$ be the reduced inverse image of $Z_\eta$. Its underlying set omits the
   generic point of $N_1$, since the normalization map and the purely inseparable projection send
   that point to the generic point of $X$. Hence [lem-pc-nowhere-dense-dim-zero] gives $\dim
   D_1\le0$, and [lem-pc-zero-dimensional-closed-subscheme-finite] makes $D_1$ finite over $k_1$.
   Its finite-dimensional coordinate algebra is Noetherian (chains of ideals are chains of
   subspaces), so [lem-weil-pbc-noetherian-finitely-many-minimal-primes] gives finitely many
   irreducible components. Apply [lem-pur-finite-inseparable-geometric-reduction] to $D_1$ to
   obtain a finite purely inseparable $K/k_1$ such that $D=(D_1\times_{k_1}K)_{\mathrm{red}}$ is
   geometrically reduced over $K$. It is finite over $K$: base change preserves finite morphisms
   [lem-trf-finite-radicial-basechange], and reduction is a closed immersion, hence finite
   [lem-weil-pbc-closed-immersion-finite]; compose these finite morphisms.
6. Write $D=\operatorname{Spec}H$, with $H$ finite-dimensional and geometrically reduced over $K$.
   It is Noetherian, because ascending chains of ideals are ascending chains of finite-dimensional
   subspaces. Each nonzerodivisor $h\in H$ is a unit: multiplication by $h$ is injective, hence
   surjective on the finite-dimensional space $H$, so $hx=1$ for some $x$. Thus $Q(H)=H$. The
   minimal primes form a finite list by [lem-weil-pbc-noetherian-finitely-many-minimal-primes].
   Apply [lem-weil-pbc-reduced-noetherian-total-ring-fractions]: its canonical decomposition of
   $Q(H)$ identifies $H$ with a finite product $\prod_j E_j$ of fields. Each projection is
   surjective, so $E_j$ is finite-dimensional over $K$. For any extension $\Omega/K$,
   $E_j\otimes_K\Omega$ is a direct factor of the reduced ring $H\otimes_K\Omega$, so is reduced.
   Each $E_j/K$ is separable: if $\alpha\in E_j$ were inseparable, its minimal polynomial would
   have a repeated root over an algebraic closure $\overline K$; hence
   $K[\alpha]\otimes_K\overline K$ would contain a nonzero nilpotent, which remains nonzero in
   $E_j\otimes_K\overline K$ since tensoring an injection of vector spaces is injective. By
   [lem-sc-finite-etale-algebra-criterion], $D$ is finite etale over $K$. If $H=0$, the product is
   empty and the same criterion applies.
7. Use [lem-trf-normalization-inseparable-base-change] for $X$, $k_1/k$ and $K/k_1$. Its
   hypothesis is the geometric normality from Step 4. It identifies the normalization $N$ of
   $(X_K)_{\mathrm{red}}$ with $N_1\times_{k_1}K$, over $X_K$, and identifies the reduced inverse
   image of $D_1$ with $D$. Reduced inverse images depend only on the underlying closed sets
   [lem-weil-pbc-reduced-induced-closed-subscheme], so $D$ is exactly the reduced inverse image of
   $Z_\eta$ in $N$. The scheme $(X_K)_{\mathrm{red}}$ is integral of dimension $1$ by
   [lem-pc-homeo-pure-insep]; [lem-sc-normalization-exists] therefore gives $\dim N=1$. The
   normalization comparison makes $N$ geometrically normal, so
   [lem-weil-pbc-geonormal-dim-one-smooth] makes it smooth. Here $K/k$ is finite purely
   inseparable (degrees multiply, and in positive characteristic one multiplies the exponents that
   put elements into the bottom field).
8. Construct $b_1:B_1\to B$ as the normalization of $B$ in $K$ [def-fin-normalization-extension].
   On a nonempty affine $\operatorname{Spec}A\subset B$, its coordinate ring is the integral
   closure $A'$ of $A$ in $K$. The field of fractions of $A$ is $k$
   [lem-sc-integral-function-field-affine-fraction]. Excellence implies Nagata by
   [lem-exc-quasi-excellent-nagata]; taking the prime $(0)$ in [def-weil-pbc-nagata-ring] and then
   applying [def-weil-pbc-japanese-domain] says exactly that $A'$ is finite over $A$. Thus $b_1$
   is finite [def-weil-finite-integral-morphism]. By
   [lem-weil-pbc-integral-closure-finite-extension-normal], $A'$ is a normal domain with fraction
   field $K$. These rings glue by [lem-weil-pbc-integral-closure-commutes-localization]. The
   resulting scheme is integral: all nonempty charts contain the common point with field $K$.
   Localizing $A'$ by $A\setminus\{0\}$ gives the integral closure of $k$ in $K$, namely $K$.
   Hence $b_1^{-1}(\eta)=\operatorname{Spec}K$ and $b_1$ is dominant.
9. Each finite $A$-algebra $A'$ in Step 8 is excellent by
   [lem-exc-finite-type-localization-excellent]; [lem-trf-excellent-scheme-affine-cover] then
   gives excellence on every affine open of $B_1$. Since $b_1$ is finite, it is of finite type, so
   $B_1$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. It is proper by
   [lem-weil-pbc-finite-proper], and surjective: its image is closed by properness and dense by
   dominance. Thus $b_1$ is an alteration, in fact finite everywhere. This construction used no
   affine, projective or separated structure on the whole of $B$.
10. Form $V=C\times_B B_1$, with projections $p:V\to C$ and $q:V\to B_1$. Let $\xi$ be the generic
   point of $C$. The fibre $p^{-1}(\xi)$ is $\operatorname{Spec}(\kappa(C)\otimes_k K)$, since
   $b_1^{-1}(\eta)=\operatorname{Spec}K$. By [lem-pc-homeo-pure-insep] it has one point $z$. A
   generization of $z$ in $V$ must still map to $\xi$, so is $z$. Since schemes are sober
   [lem-sc-scheme-sober], $\overline{\{z\}}$ is an irreducible component: the generic point of any
   larger irreducible closed set would generize $z$. Let $T$ be its reduced induced closed
   subscheme [lem-weil-pbc-reduced-induced-closed-subscheme]. It is integral, dominates $C$, and
   dominates $B_1$, because $z$ maps to the unique point of $b_1^{-1}(\eta)$.
11. The map $p$ is finite by base change of the finite $b_1$ [lem-trf-finite-radicial-basechange].
   The inclusion $T\hookrightarrow V$ is finite [lem-weil-pbc-closed-immersion-finite], so $T\to
   C$ is finite by the composition clause of [lem-trf-finite-radicial-basechange]. Hence $T$ is
   Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Over the excellent affine charts of
   $C$, its coordinate rings are finite algebras, hence excellent by
   [lem-exc-finite-type-localization-excellent]; these cover $T$, so
   [lem-trf-excellent-scheme-affine-cover] makes $T$ excellent. Also $q$ is proper by base change
   of $f_C$ [lem-weil-pbc-proper-fp-permanence](b); thus $T\to B_1$ is proper by
   [lem-weil-pbc-closed-immersion-proper](b).
12. Normalize $T$ in its function field $F$, obtaining $n:C_1\to T$ [def-sc-normalization]. For
   every nonempty affine $\operatorname{Spec}R\subset T$, the integral closure $\overline R^{\,F}$
   is finite over $R$: excellence gives Nagata [lem-exc-quasi-excellent-nagata], and the
   definitions [def-weil-pbc-nagata-ring, def-weil-pbc-japanese-domain] apply to the degree-one
   extension $F/F$. It is a normal domain with fraction field $F$
   [lem-weil-pbc-integral-closure-finite-extension-normal]; the affine description therefore makes
   $C_1$ integral and $n$ finite and dominant. Its finite affine chart algebras are excellent
   [lem-exc-finite-type-localization-excellent, lem-trf-excellent-scheme-affine-cover], and it is
   Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Put $a_1=pn:C_1\to C$ and
   $f_1=qn:C_1\to B_1$, where $p,q$ are restricted to $T$. The first is finite by
   [lem-trf-finite-radicial-basechange]; the second is proper by
   [lem-weil-pbc-finite-morphism-permanence](c). Both are dominant from the common generic point;
   $a_1$ is proper by [lem-weil-pbc-finite-proper] and surjective by closed dense image. Thus
   $a_1$ is an alteration and $f_Ca_1=b_1f_1$.
13. Let $\eta_1$ be the generic point of $B_1$. By fibre-product associativity, $V_{\eta_1}=X_K$.
   This fibre is irreducible by [lem-pc-homeo-pure-insep]. The point $z$ is its generic point,
   since it has no proper generization in $V$ (Step 10). The closed subscheme $T_{\eta_1}$
   contains $z$, so has its whole underlying space; it is reduced, since its affine rings are
   localizations of the domains on $T$. The uniqueness clause of
   [lem-weil-pbc-reduced-induced-closed-subscheme] identifies $T_{\eta_1}=(X_K)_{\mathrm{red}}$.
   To compute $(C_1)_{\eta_1}$, take $\operatorname{Spec}A'\subset B_1$ and an affine chart
   $\operatorname{Spec}R\subset T$ over it; put $S=A'\setminus\{0\}$. Dominance makes the image of
   $S$ nonzero in $R$. By [lem-weil-pbc-integral-closure-commutes-localization],
   $$S^{-1}(\overline R^{\,F})=\overline{S^{-1}R}^{\,F}.$$ The fraction field remains $F$. These
   equalities agree on overlaps, and the normalization definition [def-sc-normalization]
   identifies $(C_1)_{\eta_1}$ with the normalization $N$ of $(X_K)_{\mathrm{red}}$, compatibly
   with its map to $X$. Thus its generic curve is the smooth integral curve of Step 7.
14. Let $Z_1=(a_1^{-1}Z)_{\mathrm{red}}$. It omits the generic point of $C_1$, since that point
   maps to the generic point of $C$, so it is nowhere dense. Under Step 13, its generic fibre is
   $D$ from Step 7. Indeed both are the reduced closed subscheme in $N$ on the inverse image of
   $Z_\eta$. Reduction commutes with this generic localization: for a ring $R$ and multiplicative
   set $T$, if $r/t$ is nilpotent in $T^{-1}R$, some $u\in T$ kills $r^m$, so $(ur)^m=0$ and
   $r/t=(ur)/(ut)$ comes from the localized nilradical. The reverse inclusion is immediate. Use
   the uniqueness in [lem-weil-pbc-reduced-induced-closed-subscheme] for the resulting closed
   subschemes. By Step 6, $(Z_1)_{\eta_1}=D$ is finite etale over $K$.
15. Apply [lem-trf-stein-smooth-generic-curve] to $f_1:C_1\to B_1$. Steps 9, 12 and 13 verify all
   its hypotheses: the schemes are excellent integral Noetherian, the morphism is proper dominant,
   and its generic fibre is a smooth irreducible curve of dimension $1$. It gives an excellent
   integral Noetherian $B_0$, a finite dominant $q_0:B_0\to B_1$, and a proper map $g:C_1\to B_0$
   with $f_1=q_0g$. Its generic fibre is smooth and geometrically integral of dimension $1$, and
   $L=\kappa(B_0)=H^0(N,\mathcal O_N)$ is finite separable over $K$. The map $g$ is dominant: the
   generic point of $C_1$ maps into the generic fibre of $q_0$, whose sole point is the generic
   point of $B_0$, as checked next.
16. The fibre of the finite dominant map $q_0$ above $\eta_1$ is $\operatorname{Spec}L$: on an
   affine $\operatorname{Spec}A'\subset B_1$, its inverse image is $\operatorname{Spec}R_0$ for a
   finite domain $R_0$ with fraction field $L$ [lem-sc-integral-function-field-affine-fraction].
   Localizing at $A'\setminus\{0\}$ gives a finite-dimensional domain over $K$, hence a field
   (multiplication by any nonzero element is injective and therefore surjective). Its fraction
   field is $L$, so it is $L$. Associativity of fibre products now gives
   $$C_1\times_{B_0}\operatorname{Spec}L\cong C_1\times_{B_1}\operatorname{Spec}K=N.$$ Likewise
   $(Z_1)_{\eta_0}$ is the same scheme $D$ with its induced $L$-structure, not the generally
   larger scheme $D\times_K L$. These identifications use the finite map, integrality, function
   field and factorization supplied by [lem-trf-stein-smooth-generic-curve].
17. The decomposition $H=\prod_jE_j$ in Step 6 is by quotient maps, so the $L$-algebra structure
   of $H=\Gamma(D,\mathcal O_D)$ from Step 16 induces maps $L\to E_j$. For each nonzero field
   factor this is an injection. Each $E_j$ is finite over $L$, since a finite $K$-spanning set is
   also an $L$-spanning set. It is separable over $L$: the minimal polynomial over $L$ of any
   $\alpha\in E_j$ divides its separable minimal polynomial over $K$, and a divisor of a
   square-free polynomial is square-free. Consequently [lem-sc-finite-etale-algebra-criterion]
   makes $(Z_1)_{\eta_0}$ finite etale over $L$. The empty product gives the empty boundary, also
   allowed by that criterion.
18. Set $Q=C_1$ and $Y_1=B_0$, with structure map $g:Q\to Y_1$. The map $a_1:Q\to C$ constructed
   above is finite and surjective, and $Y_1\to B_1\to B=Y_0$ is finite dominant
   [lem-trf-finite-radicial-basechange]. Both bases are affine, since a finite morphism is affine
   [def-weil-finite-integral-morphism]. The finite proper base map has dimension $\dim Y_1=\dim
   Y_0=n$ by [lem-trf-closed-dominant-dimension]. Its excellence, integrality and Noetherianity
   were established above and by the Stein statement. The generic fibre of $g$ is the smooth
   geometrically integral curve of Step 15, and the reduced marking $D=Z_1\subset Q$ is nowhere
   dense with finite etale generic fibre by Steps 14 and 17. All constructions are over $Y_0$.
19. The scheme $Q$ is normal by its construction as the normalization of $T$. Apply
   [lem-sbc-normal-sections-finite-product] to the quasi-compact open $Q$ of itself. The global
   section ring $H=\Gamma(Q,\mathcal O_Q)$ is a finite product of normal domains. It is a nonzero
   domain because restriction embeds it into $k(Q)$, so the product has exactly one nonzero factor
   and $H$ is integrally closed. By the relative-spectrum description in
   [lem-trf-stein-smooth-generic-curve], the affine scheme $Y_1$ is $\operatorname{Spec}H$.
   Localizations of $H$ are integrally closed by
   [lem-weil-pbc-integral-closure-commutes-localization] applied to its integral closure in
   $\operatorname{Frac}H$. Thus every local ring of $Y_1$ is a normal domain, as required.
20. Let $\mathcal I_D$ be the reduced defining ideal of $D=Z_1$ and blow it up:
   $b:P=\operatorname{Bl}_{\mathcal I_D}Q\to Q$. It is proper by [lemma-nagata-blowup-proper]. It
   is integral and birational: the chart cover [prop-nagata-affine-blowup-chart-cover] and
   [def-nagata-blowup-chart-ring] consists, after discarding empty charts, of subrings
   $R[I/a]\subset\operatorname{Frac}R$ for nonzero $a\in I$ in affine domains $R\subset k(Q)$.
   Every chart has the same generic point and field $k(Q)$, and away from $D$ the ideal is the
   unit ideal, so the map is an isomorphism by [cor-nagata-blowup-cartier-iso]. The charts are
   finite-type over excellent Noetherian charts of $Q$;
   [lem-exc-finite-type-localization-excellent], [lem-trf-excellent-scheme-affine-cover] and
   [lem-weil-pbc-finite-type-over-noetherian] give excellence and Noetherianity. Put $E=V(\mathcal
   I_D\mathcal O_P)$. By [det-nagata-boundary-divisor-cartier], $E$ is an effective Cartier
   divisor with support $b^{-1}|D|$.
21. On the generic curve $Q_{\eta_1}$, the reduced finite closed subscheme $D_{\eta_1}$ has
   invertible ideal. Indeed, at any of its points the local ring is a one-dimensional Noetherian
   normal local domain (the generic curve was geometrically normal before Stein and its underlying
   scheme is unchanged); it is a DVR by [lem-sc-normal-dim1-dvr]. The reduced ideal there is the
   maximal ideal, hence generated by a nonzero uniformizer. Away from its finite support the ideal
   is the unit ideal. Local generators give local trivializations of this coherent ideal. Blowup
   commutes with this generic localization by [def-nagata-blowup-flat-base-change-map] and
   [thm-nagata-blowup-flat-base-change]; the generic base-change map is flat since on affines it
   is localization by nonzero elements of the base domain. By [cor-nagata-blowup-cartier-iso],
   $P_{\eta_1}\cong Q_{\eta_1}$, and $E_{\eta_1}=D_{\eta_1}$ as closed subschemes. Thus the curve
   stays smooth geometrically integral and its marking is finite etale, including the empty case.
22. Take $P^\circ=(a_1b)^{-1}(W)$ and $h=(a_1b)|_{P^\circ}:P^\circ\to W$. This is a dense open,
   since $a_1b$ sends the generic point to that of $C$, which lies in $W$. The map $a_1b$ is
   proper by [lem-weil-pbc-finite-proper] and [lem-weil-pbc-proper-fp-permanence], so its
   restriction over $W$ is proper. It is surjective: $a_1$ is finite dominant and $b$ is proper
   birational, so each has closed dense image; base change to $W$ preserves surjectivity here. The
   total transform support is $|E|=b^{-1}|D|$, and $|D|=a_1^{-1}|Z|$, whence $|E|\cap
   P^\circ=h^{-1}Z_W$ because $|Z|\cap W=Z_W$. The composite $f=gb:P\to Y_1$ is proper dominant.
   It is separated over the affine scheme $Y_1$, which is separated over
   $\operatorname{Spec}\mathbf Z$ (on an affine $\operatorname{Spec}H$, the diagonal comes from
   the surjective multiplication map $H\otimes_{\mathbf Z}H\twoheadrightarrow H$), so $P$ is
   separated. The same permanence statement gives properness of $f$ and all commuting structural
   maps.
23. The function field $F=k(Q)=k(P)$ is the residue field of $k(C)\otimes_k K$, with
   $k=\kappa(Y_0)$ and $K/k$ the finite purely inseparable extension. Since $K$ is generated by
   finitely many elements each having a characteristic-power in $k$, their images generate $F$
   over $k(C)=k(W)$ and have the same powers in $k(C)$. Thus $F/k(W)$ is finite purely
   inseparable; finiteness also follows from
   [lem-weil-pbc-purely-inseparable-base-change-local-ring] with $A=k(C)$. In characteristic zero
   this extension is trivial by the definition of purely inseparable. In characteristic $p>0$,
   [lem-weil-pbc-purely-inseparable-pth-root-tower] expresses it as a tower of degree-$p$
   extensions, so multiplication of bases gives $[F:k(W)]=p^r$. The invertible prime $\ell$ is
   different from $p$, and consequently this degree is prime to $\ell$. Stein factorization
   changed only the base and did not extend $F$.
24. To see that $h$ is finite over a dense open, choose a nonempty affine open $V\subset Q$
   disjoint from $D$. The complement $Q\setminus V$ misses the generic point of $Q$. The finite
   map $a_1:Q\to C$ has only that generic point over the generic point of $C$: localizing its
   affine coordinate domain at the nonzero elements of a base domain gives a finite-dimensional
   domain, hence a field. Its closed image $a_1(Q\setminus V)$ therefore misses the generic point
   of $C$. Remove this image and intersect with $W$, obtaining a dense open $W_1$. Above $W_1$,
   $a_1^{-1}(W_1)\subset V$, where $b$ is an isomorphism, so $h|_{W_1}$ is the finite map
   $a_1|_{W_1}$ [def-weil-finite-integral-morphism, lem-weil-pbc-finite-proper]. Finally every
   constructed scheme maps to $Y_0$, so the image of the unit $\ell\in\mathcal O_{Y_0}$ stays a
   unit on it. This verifies all finiteness and invertibility clauses.
-/
theorem exists_proper_generic_curve_preparation
    (ell n : ℕ) [Fact ell.Prime]
    (Y₀ W : Scheme.{u}) [IsAffine Y₀] [IsIntegral Y₀] [IsNoetherian Y₀]
    [IsAffine W] [IsIntegral W] [IsNoetherian W]
    (hY₀ : ∀ V : Y₀.affineOpens, IsExcellent Γ(Y₀, V))
    (hW : ∀ V : W.affineOpens, IsExcellent Γ(W, V))
    (hdim : topologicalKrullDim Y₀ = (n : WithBot ℕ∞))
    (hinv : ∀ y : Y₀, IsUnit (ell : Y₀.presheaf.stalk y))
    (f₀ : W ⟶ Y₀) [IsDominant f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    [IsIntegral (f₀.fiber (genericPoint Y₀))]
    (hcurve : topologicalKrullDim (f₀.fiber (genericPoint Y₀)) = 1)
    (Z_W : Set W) (hclosed : IsClosed Z_W) (hrare : IsNowhereDense Z_W)
    (hmark : topologicalKrullDim
      {x : f₀.fiber (genericPoint Y₀) | f₀.fiberι (genericPoint Y₀) x ∈ Z_W} ≤ 0) :
    ∃ (Y₁ : Scheme.{u}) (_ : IsIntegral Y₁) (q : Y₁ ⟶ Y₀)
      (P : Scheme.{u}) (_ : IsIntegral P) (f : P ⟶ Y₁)
      (E : P.IdealSheafData) (U : P.Opens) (_ : IsIntegral U.toScheme)
      (h : U.toScheme ⟶ W),
      IsAffine Y₁ ∧ IsNoetherian Y₁ ∧
      (∀ V : Y₁.affineOpens, IsExcellent Γ(Y₁, V)) ∧
      (∀ y : Y₁, IsDomain (Y₁.presheaf.stalk y) ∧
        IsIntegrallyClosed (Y₁.presheaf.stalk y)) ∧
      topologicalKrullDim Y₁ ≤ (n : WithBot ℕ∞) ∧ IsFinite q ∧ IsDominant q ∧
      IsNoetherian P ∧ (∀ V : P.affineOpens, IsExcellent Γ(P, V)) ∧ P.IsSeparated ∧
      IsProper f ∧ IsDominant f ∧ E.IsInvertible ∧ Dense (U : Set P) ∧
      IsProper h ∧ Surjective h ∧
      (∃ V : W.Opens, Dense (V : Set W) ∧ IsFinite (h ∣_ V)) ∧
      U.ι ≫ f ≫ q = h ≫ f₀ ∧
      U.ι ⁻¹' (E.support : Set P) = h ⁻¹' Z_W ∧
      Smooth (f.fiberToSpecResidueField (genericPoint Y₁)) ∧
      GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y₁)) ∧
      topologicalKrullDim (f.fiber (genericPoint Y₁)) = 1 ∧
      IsFinite ((E.subschemeι ≫ f).fiberToSpecResidueField (genericPoint Y₁)) ∧
      Etale ((E.subschemeι ≫ f).fiberToSpecResidueField (genericPoint Y₁)) ∧
      (∀ w : W, IsUnit (ell : W.presheaf.stalk w)) ∧
      (∀ y : Y₁, IsUnit (ell : Y₁.presheaf.stalk y)) ∧
      (∀ p : P, IsUnit (ell : P.presheaf.stalk p)) ∧
      (∀ p : U.toScheme, IsUnit (ell : U.toScheme.presheaf.stalk p)) ∧
      (∀ e : E.subscheme, IsUnit (ell : E.subscheme.presheaf.stalk e)) ∧
      ∃ (hh : h (genericPoint U.toScheme) = genericPoint W)
        (φ : W.functionField →+* P.functionField),
        (U.ι.functionFieldMap (genericPoint_eq_of_isOpenImmersion U.ι)).hom.comp φ =
          (h.functionFieldMap hh).hom ∧
        ∀ [Algebra W.functionField P.functionField],
          algebraMap W.functionField P.functionField = φ →
          FiniteDimensional W.functionField P.functionField ∧
          Nat.Coprime (Module.finrank W.functionField P.functionField) ell := by
  sorry

end AlgebraicGeometry
