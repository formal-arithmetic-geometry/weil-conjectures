/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatDvrSpecialFiberCartier
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Sheaf.AlgebraicGeometry.AffineOpenBoundaryCodimensionOne
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Filtration
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.AffinePrincipalAffinizationIsomorphism

/-! # Quasi-affine locus of affinization over a trait

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §6.5 Lemma 6, p.161, and
proof of Theorem 1, p.162, assertions (i) and (iii).
(blueprint: lem-sfb-trait-affine-generic-affinization-locus).

The affinization is Mathlib's adjunction unit `Y.toSpecΓ`. The open is specified by
its points using the project's Stacks quasi-finiteness predicate. Generic and special
fibres use the canonical fraction field and quotient by the maximal ideal.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a smooth separated finite-type scheme over a DVR with affine generic fibre,
the canonical affinization is separated and of finite type. Its quasi-finite locus is
a quasi-compact open, contains the whole generic fibre, embeds openly into the spectrum
of global sections, and meets the special fibre whenever the latter is nonempty.

Source: BLR, Néron Models, §6.5 Lemma 6 and proof of Theorem 1, pp.161--162.
(blueprint: lem-sfb-trait-affine-generic-affinization-locus).

Proof plan (the numbered steps are those of the DAG node):

1. Choose a uniformizer $\pi$ of $R$. A DVR is a PID, so $R$ is a Noetherian integrally closed
domain of dimension one. Its prime localizations are normal, hence $T$ is normal. The
finite-type-over-Noetherian lemma makes $Y$ Noetherian; separatedness over the affine $T$ makes
$Y$ separated as a scheme. Every open of the Noetherian scheme $Y$ is quasi-compact by the
Noetherian-open lemma. In particular intersections of affine opens are quasi-compact, so $Y$ is
quasi-separated; it is also quasi-compact. These facts also show that the canonical map $a$ is
quasi-compact: its source is quasi-compact and its affine target is quasi-separated.
Dependencies: def-sc-discrete-valuation-ring, lem-weil-pbc-pid-noetherian-normal,
lem-sc-dvr-dimension-one, lem-weil-pbc-localization-normal-domain,
lem-weil-pbc-finite-type-over-noetherian, lem-sc-separated-over-affine-scheme-separated,
lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence,
lem-weil-pbc-noetherian-open-subscheme-noetherian.

2. Choose a finite affine cover $V_j=\operatorname{Spec}C_j$ of $Y$ with each $C_j$ finitely
generated over $R$, as in the finite-type definition. On each such chart write $C=C_j$. The same
finite list of algebra generators generates $C$ over $A$, since $R\to C$ factors through the
section map $A\to C$. Thus $a$ is locally of finite type, and its quasi-compactness in step 1
makes it finite type. The composite $Y\xrightarrow a\operatorname{Spec}A\to T$ is the original
separated morphism; separated cancellation gives separatedness of $a$.
Dependencies: def-weil-finite-type-morphism, lem-weil-pbc-separated-cancellation.

3. Apply relative normalization to $a$, writing $Y\xrightarrow i C\xrightarrow
n\operatorname{Spec}A$. In its affine-chart clause (iii), take the entire target. The algebra map
$A\to\Gamma(Y,\mathcal O_Y)=A$ is the identity by the definition of $a$. Its integral closure
inside $A$ is exactly $A$: each element satisfies its monic linear polynomial. Consequently $C$ is
affine and $n$ induces the identity of $A$, so $n$ is an isomorphism by the affine
spectrum--sections correspondence. The normalization isolated-fibre theorem applies because $a$ is
separated and finite type. Its isolated-fibre subset is precisely $W$: quasi-finite points are
isolated, and conversely an isolated fibre point has the required quasi-finite affine
neighbourhoods. Thus its isomorphism $i^{-1}(O)\simeq O$ identifies $W$ with an open of $C$.
Composing with $n$ proves that $a|_W$ is an open immersion. The Noetherian-open lemma makes $W$
quasi-compact, hence quasi-affine by its displayed embedding in $\operatorname{Spec}A$. No
Noetherianity of $A$ is used.
Dependencies: lem-weil-pbc-relative-normalization, lem-weil-pbc-morphism-into-affine-scheme,
lem-sfb-scheme-normalization-isolated-fibre-open, lem-weil-pbc-quasi-finite-at-point-isolated,
lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs,
lem-weil-pbc-noetherian-open-subscheme-noetherian.

4. Apply the qcqs functions localization comparison to $Y\to T$ with multiplicative set
$R\setminus\{0\}$. It identifies $A\otimes_R F$ with $\Gamma(Y_F,\mathcal O)$ through the actual
pullback of functions. Naturality of the affine adjunction identifies $a_F$ with the canonical map
of the affine scheme $Y_F$, so $a_F$ is an isomorphism. For a point $z$ of the generic open of
$\operatorname{Spec}A$, the scheme fibre of $a$ over $z$ equals that of $a_F$, hence consists of a
single reduced point. The isolated-fibre criterion puts every point of $Y_F$ in $W$. Therefore
$W_F=Y_F$, including the empty generic fibre.
Dependencies: lem-sfb-qcqs-functions-local-comparison, lem-weil-pbc-morphism-into-affine-scheme,
lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs.

5. It remains to treat $Y_k\ne\varnothing$. Apply the Dedekind smooth fibre-dense affine lemma
with $D=R$ to obtain an affine open $U\subseteq Y$ dense in both fibres. Its stated geometric
density implies ordinary density: a nonempty affine open in a fibre remains nonempty after
extending its field to an algebraic closure, since its nonzero coordinate vector space stays
nonzero on tensoring with a field extension. If the open missed $U$, its base change would
contradict geometric density. Smoothness gives flatness, and the flat-DVR Cartier lemma says that
multiplication by $\pi$ is injective in each stalk, with special-fibre ideal $(\pi)$. Smooth base
change and the smooth-field lemma make $Y_k$ normal and reduced; normal ascent makes $Y$ normal.
Dependencies: lem-sfb-dedekind-smooth-fibre-dense-affine, lem-pc-smooth-flat,
lem-sbc-flat-dvr-special-fiber-cartier, lem-pc-proper-base-change,
lem-trf-smooth-geometrically-normal, lem-sfb-smooth-normal-ascent.

6. The Noetherian topology and normal-component theorem decompose $Y$ into finitely many disjoint
open integral components. The generic point of any component lies over $F$: otherwise $\pi$ would
be zero at that generic stalk, contradicting its being a non-zero-divisor there. Thus $Y_F$ is
dense in $Y$. Since $U_F$ is dense in $Y_F$, $U$ is dense in $Y$. The same component theorem
applies to the normal Noetherian special fibre $Y_k$, giving generic points of its finitely many
components, each belonging to $U_k$.
Dependencies: lem-weil-pbc-noetherian-scheme-closed-subsets-minimal,
lem-trf-normal-topologically-noetherian-components.

7. Put $Z=|Y|\setminus|U|$. Each generic point $\xi$ of a component of $Z$ has $\dim\mathcal
O_{Y,\xi}=1$ by the affine-boundary lemma. Such a $\xi$ cannot lie in $Y_k$. Indeed, a generic
point $\zeta$ of a component of $Y_k$ containing $\xi$ generalizes $\xi$, and a generic point
$\eta$ of the component of $Y$ containing $\zeta$ generalizes $\zeta$. Here $\eta\ne\zeta$ by step
6. If $\xi\ne\zeta$, this gives a chain of length two, contradicting the stalk-dimension formula.
If $\xi=\zeta$, it belongs to $U_k$ by step 6, contradicting $\xi\in Z$. Therefore all generic
points of $Z$ lie in $Y_F$. Since $Z$ is a finite union of their closures, $Z=\overline{Z\cap
Y_F}$ (closure inside $Y$).
Dependencies: lem-sfb-affine-open-boundary-codimension-one,
lem-sc-scheme-stalk-dimension-generalization-chains.

8. Choose $x\in Y_k$ and let $Y_i$ be its integral open-and-closed component, with generic point
$\eta$. By step 6, $\eta\in U_F$. Since $Y_F$ is affine, its principal-open basis gives
$g\in\Gamma(Y_F,\mathcal O)$ with $\eta\in D(g)\subseteq U_F$. The localization comparison of step
4 writes $g=b/r$ with $b\in A$ and $0\ne r\in R$. Thus $D(b)_F=D(g)$. The germ $b_x$ is nonzero:
on the integral component $Y_i$, restriction of a section to its generic point and to any other
stalk embeds into the same fraction field. Explicitly, on any nonempty affine chart its ring is a
domain, and the stalk maps are its prime localizations, so a section zero on a neighbourhood of
$x$ would vanish at $\eta$. This contradicts $\eta\in D(b)$.
Dependencies: lem-weil-pbc-spec-localization-away-basic-open,
lem-sfb-qcqs-functions-local-comparison, lem-weil-pbc-affine-open-stalk-localization.

9. The local ring $B=\mathcal O_{Y,x}$ is Noetherian: take a Noetherian affine chart and localize
at the prime of $x$. The ideal $(\pi)B$ lies in its maximal ideal, hence in its Jacobson radical.
Krull intersection, with the cyclic finite module $M=B$, gives $\bigcap_n\pi^nB=0$. Since
$b_x\ne0$, the set of $n$ for which $b\in\pi^n A$ is bounded and nonempty, and therefore has a
largest element $n$. Choose $f\in A$ with $b=\pi^n f$. Then $f\notin\pi A$, while
$D(f)_F=D(b)_F\subseteq U_F$ because $\pi$ is invertible over $F$. This proves that division by a
maximal power of $\pi$ terminates, rather than assuming $A$ itself Noetherian or $\pi$-adically
separated.
Dependencies: pqf-lem-affine-open-locnoeth, lem-weil-pbc-affine-open-stalk-localization,
lem-weil-pbc-localization-noetherian, lem-weil-pbc-krull-intersection-jacobson.

10. The natural map $A/\pi A\to\Gamma(Y_k,\mathcal O)$ is injective. To see this directly, if a
section restricts to zero on $Y_k$, its germs belong to the ideal $(\pi)$, so locally it is $\pi
h$. The local quotients $h$ agree on overlaps because multiplication by $\pi$ is injective, and
the sheaf axiom glues them to a global quotient. Hence the kernel is exactly $\pi A$. Since
$f\notin\pi A$, its restriction to $Y_k$ is nonzero. It is nonvanishing at some point of $Y_k$:
otherwise on every affine chart it would lie in every prime ideal, hence be nilpotent, and
reducedness would force it to be zero. Consequently $(Y_f)_k\ne\varnothing$.
Dependencies: lem-sbc-flat-dvr-special-fiber-cartier, lem-trf-smooth-geometrically-normal.

11. The closed set $Y\setminus Y_f$ contains $Z\cap Y_F$ since $D(f)_F\subseteq U_F$. By step 7 it
therefore contains $Z$, so $Y_f\subseteq U$. Inside the affine $U$, this is exactly the principal
open $U_{f|_U}$ and hence is affine. Apply the affine-principal-affinization isomorphism lemma to
the qcqs scheme $Y$: it identifies $a:Y_f\to D(f)\subseteq\operatorname{Spec}A$ with an
isomorphism. Every point of $Y_f$ thus has an isolated fibre for $a$, so the isolated-fibre
criterion gives $Y_f\subseteq W$. Step 10 proves $W_k\ne\varnothing$. If $Y_k$ is empty there is
no special-fibre assertion; if $Y$ is empty all maps and opens above are empty and steps 1--4
already prove the conclusions. The construction makes no componentwise special-fibre density
claim.
Dependencies: lem-weil-pbc-affine-open-section-vanishing-prime,
lem-a1-affine-principal-affinization-isomorphism,
lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs.
-/
theorem trait_affine_generic_affinization_locus
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hGeneric : IsAffine (pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) :
    IsSeparated Y.toSpecΓ ∧ LocallyOfFiniteType Y.toSpecΓ ∧ QuasiCompact Y.toSpecΓ ∧
      ∃ W : Y.Opens,
        (∀ y : Y, y ∈ W ↔ Y.toSpecΓ.IsQuasiFiniteAtPoint y) ∧
        IsCompact (W : Set Y) ∧
        (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) ⁻¹ᵁ W = ⊤ ∧
        IsOpenImmersion (W.ι ≫ Y.toSpecΓ) ∧
        W.toScheme.IsQuasiAffine ∧
        (Nonempty (pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) →
          Nonempty (pullback (C := Scheme.{u}) (W.ι ≫ f)
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) := by
  sorry

end AlgebraicGeometry
