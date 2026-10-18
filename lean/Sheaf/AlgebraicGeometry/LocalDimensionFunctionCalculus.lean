/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.AlgebraicGeometry.GeometricDimensionFunction
public import Sheaf.AlgebraicGeometry.GeometricSpecializationCategory
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic

import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.GeometricImmediateCatenary
import Sheaf.AlgebraicGeometry.StrictLocalizationDiscreteFibres
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.Paper.StrictHenselizationFunctoriality

/-!
# Local existence and codimension calculus for dimension functions

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XIV, Proposition 2.1.4,
Theorem 2.2.1, Corollary 2.2.4 and proof of Lemma 2.2.5, printed pp. 210--213;
Stacks Project, Tag 02IC (blueprint: lem-per-local-dimension-function-calculus).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A universally catenary Noetherian scheme has local dimension functions, and every
dimension function computes the codimension of a geometric specialization. The identity
and isomorphism cases have codimension zero.

Proof (the DAG proof, with its recorded dependencies):

1. Work on an affine neighbourhood $\operatorname{Spec}R$ of a chosen point $x$, represented by a
prime $\mathfrak q_x$. For comparable primes $\mathfrak p\subseteq\mathfrak q$, let
$\ell(\mathfrak p,\mathfrak q)$ be the common length of saturated chains between them (zero when
equal). This is a finite nonnegative integer: the catenary hypothesis in the cited definition
bounds all finite chain lengths, so a chain of greatest length exists and is saturated. For
$\mathfrak p\subseteq\mathfrak r\subseteq\mathfrak q$, concatenate greatest-length chains in the
two intervals; their concatenation is saturated, hence $\ell(\mathfrak p,\mathfrak
q)=\ell(\mathfrak p,\mathfrak r)+\ell(\mathfrak r,\mathfrak q)$. This is just the bounded
saturated-chain definition, without an equidimensionality assumption on $R$.
Uses: def-exc-excellent-ring.

2. The finite-components statement applied to this affine scheme and to each closed intersection
of its irreducible components gives finite decompositions $\operatorname{Spec}R=\bigcup_i Z_i$ and
$Z_i\cap Z_j=\bigcup_k W_{ijk}$. Components of an affine spectrum are $V(\mathfrak p_i)$ for
minimal primes $\mathfrak p_i$, and sobriety supplies a generic prime $\mathfrak r_{ijk}$ for each
irreducible closed $W_{ijk}=V(\mathfrak r_{ijk})$. Delete all $Z_i$ not containing $x$ and all
$W_{ijk}$ not containing $x$. Their union is a finite closed set avoiding $x$, so its complement
$U$ is an open neighbourhood of $x$. A surviving $Z_i$ has $\mathfrak p_i\subseteq\mathfrak q_x$.
Put $a_i=\ell(\mathfrak p_i,\mathfrak q_x)$ and, for $y\in Z_i\cap U$ represented by $\mathfrak
q_y$, put $\delta_i(y)=a_i-\ell(\mathfrak p_i,\mathfrak q_y)$. These are actual integer-valued
functions, each normalized to zero at $x$.
Uses: lem-sc-noetherian-closed-subset-finite-components, lem-weil-pbc-spec-irreducible-components-
minimal-primes, lem-sc-scheme-sober.

3. If $y\in Z_i\cap Z_j\cap U$, choose $W_{ijk}$ containing $y$. It was not deleted, hence
contains $x$. Write $\mathfrak r=\mathfrak r_{ijk}$; then both $\mathfrak q_y$ and $\mathfrak q_x$
contain $\mathfrak r$, and both $\mathfrak p_i$ and $\mathfrak p_j$ lie in $\mathfrak r$. The
additivity proved in step 1 gives $$\delta_i(y)=\ell(\mathfrak r,\mathfrak q_x)-\ell(\mathfrak
r,\mathfrak q_y)=\delta_j(y).$$ Thus the $\delta_i$ define one function $\delta:U\to\mathbf Z$.
For a Zariski immediate specialization $y\rightsquigarrow z$ in $U$, choose a component $Z_i$
containing $y$; it contains $z$ since it is closed. The prime interval from $\mathfrak q_y$ to
$\mathfrak q_z$ is saturated and has length one: any intermediate prime would give a
generalization of $z$, and so belongs to the open $U$. Step 1 gives $\delta(y)-\delta(z)=1$.

4. Let $\bar v\rightsquigarrow\bar w$ be an immediate geometric specialization on $U$; as
$U\subseteq\operatorname{Spec}R\subseteq T$ are open, $U_{(\bar w)}=(\operatorname{Spec}R)_{(\bar
w)}=T_{(\bar w)}$. Its underlying points are distinct: if $v=w$, the image point $p$ of $\bar v$
in $T_{(\bar w)}$ lies in the fibre over $w$, which is discrete by the discrete-fibre statement
and contains the closed point $m$ (strict-localization functoriality); since
$m\in\overline{\{p\}}$, discreteness of the fibre forces $p=m$, whose closure is one point, of
dimension $0\neq1$. So $v\ne w$. Apply the geometric-immediate comparison to
$X=\operatorname{Spec}R$: it is Noetherian (one affine chart), and each of its affine opens is an
affine open of $T$, hence has universally catenary ring by the hypothesis on $T$. Its last
assertion says that $\mathfrak q_v\subset\mathfrak q_w$ is saturated in $R$, so no point of
$\operatorname{Spec}R$, in particular none of $U$, lies strictly between: $v\rightsquigarrow w$ is
a Zariski immediate specialization in $U$. By step 3, $\delta(v)-\delta(w)=1$: the function
constructed in steps 1–3 is a dimension function on $U$. This proves Zariski local existence in
the stated sense. If $T$ is local, apply the construction at its closed point. An open
neighbourhood of the closed point is the whole local scheme: in $\operatorname{Spec}A$, a basic
neighbourhood $D(f)$ of its maximal ideal has $f$ a unit. Therefore the resulting dimension
function is defined on all of $T$.
Uses: lem-per-geometric-immediate-catenary, lem-per-strict-localization-discrete-fibres, lem-weil-
pbc-strict-henselization-functoriality, def-exc-excellent-ring.

5. Now let $\delta$ be any dimension function on $T$ and fix a geometric point $\bar w$. Put
$u:H=T_{(\bar w)}\to T$. The affine strict-local comparison identifies $H$ with the spectrum of
the algebraic strict henselization of $\mathcal O_{T,w}$. The affine stalk-localization and
Noetherian-localization statements make $\mathcal O_{T,w}$ Noetherian, and preservation of
Noetherianity by strict henselization makes $H=\operatorname{Spec}B$ Noetherian local. Its closed
point maps to $w$, by strict-localization functoriality. The affine-chart lemma makes $u$ ind-
etale, and the strict-local invariance statement therefore identifies $H_{(\bar b)}$ with
$T_{(u\bar b)}$ over $T$ for every geometric point $\bar b$ of $H$. The structural-map equality in
the affine comparison and the over-$T$ equality in invariance ensure these are the actual
structural maps, not just abstract isomorphisms of rings.
Uses: lem-exc-affine-strict-local-ring-comparison, lem-weil-pbc-affine-open-stalk-localization,
lem-weil-pbc-localization-noetherian, lem-sc-strict-henselization-noetherian, lem-weil-pbc-strict-
henselization-functoriality, lem-weil-pbc-strict-henselization-affine-chart-ind-etale, lem-trf-
ind-etale-strict-local-invariance.

6. For a Zariski immediate specialization $a\rightsquigarrow b$ in $H$, the local ring at $b$ of
the reduced closure of $a$ has dimension one: its generalization chains correspond exactly to the
chains between $a$ and $b$, so the stalk-dimension statement gives dimension one. The reduced-
closed-subscheme statement supplies this closure as a scheme. Now the forward direction (a) of the
immediate-specialization criterion, which requires only Noetherianity, says that every point over
$a$ in $H_{(\bar b)}$ has one-dimensional closure. There is at least one such point by the
nonempty-fibre assertion for strict localization. Choose a geometric point above it. Under the
over-$T$ isomorphism $H_{(\bar b)}\simeq T_{(u\bar b)}$ of step 5, its image defines an immediate
geometric specialization in $T$, with underlying endpoints $u(a),u(b)$. The geometric-
specialization description is the map from a geometric point into the target strict localization.
Thus $\delta(u(a))-\delta(u(b))=1$. In particular $\epsilon=\delta\circ u$ drops by one on every
Zariski immediate specialization in $H$. No universal catenarity of $H$, no branch
equidimensionality theorem, and no assumed dimension function on $H$ have been used in this
argument.
Uses: lem-per-immediate-specialization-criterion, lem-per-strict-localization-discrete-fibres,
lem-sc-scheme-stalk-dimension-generalization-chains, lem-weil-pbc-reduced-induced-closed-
subscheme.

7. Let the given specialization $\bar v\rightsquigarrow\bar w$ have image point $p\in H$, and let
$m$ be the closed point of $H=\operatorname{Spec}B$. The closure
$C=\overline{\{p\}}_{\mathrm{red}}$ is $\operatorname{Spec}(B/P)$, where $P$ is the prime of $p$:
this is the reduced closed-subscheme construction, since a prime ideal is radical, and the
quotient-spectrum homeomorphism. The finite Krull dimension of the Noetherian local ring $B$
bounds the lengths of all prime chains between $P$ and its maximal ideal. Hence a chain of
greatest length $d$ between these endpoints exists. Any prime chain in $V(P)$ extends to these
endpoints, so $d=\dim C$ by the quotient-spectrum identification and the equality of ring and
topological Krull dimensions. A greatest-length chain is saturated. Telescope step 6 along its $d$
inclusions to obtain $$\delta(v)-\delta(w)=\epsilon(p)-\epsilon(m)=d=\dim C=c_T(\bar v,\bar w).$$
When the underlying endpoints coincide, the strict-local fibre is discrete and contains $m$. Since
$H$ is local, every point specializes to $m$, so a point of that fibre must equal $m$. Its closure
is one point and $d=0$. This includes identity specializations and geometric isomorphisms, and
proves all the zero-codimension clauses.
Uses: lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-spec-quotient-homeomorphism-
zero-locus, lem-weil-pbc-noetherian-local-finite-krull-dimension, lem-weil-pbc-spec-topological-
krull-dimension-ring, lem-per-strict-localization-discrete-fibres.

Source: ILO Exposé XIV, pp. 210--213; Stacks Tag 02IC
(blueprint: lem-per-local-dimension-function-calculus).
-/
theorem local_dimension_function_calculus
    {T : Scheme.{u}} [IsNoetherian T]
    (hcat : ∀ U : T.affineOpens, IsUniversallyCatenary Γ(T, U)) :
    (∀ x : T, ∃ U : T.Opens, x ∈ U ∧
      ∃ δ : U.toScheme → ℤ, Scheme.IsGeometricDimensionFunction U.toScheme δ) ∧
    ((∃ (R : CommRingCat.{u}) (_ : IsLocalRing R), Nonempty (T ≅ Spec R)) →
      ∃ δ : T → ℤ, Scheme.IsGeometricDimensionFunction T δ) ∧
    (∀ (δ : T → ℤ), Scheme.IsGeometricDimensionFunction T δ →
      ∀ (p q : StrictGeometricPoint T) (a : p ⟶ q),
        ∃ n : ℕ, StrictGeometricPoint.codimension a = (n : WithBot ℕ∞) ∧
          δ p.underlying - δ q.underlying = (n : ℤ)) ∧
    (∀ (p : StrictGeometricPoint T),
      StrictGeometricPoint.codimension (𝟙 p) = 0) ∧
    (∀ (p q : StrictGeometricPoint T) (e : p ≅ q),
      StrictGeometricPoint.codimension e.hom = 0) := by
  sorry

end AlgebraicGeometry
