/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.KrullDimension
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-! # Constructible closure avoids whole geometric fibres

Source: Deligne, Le lemme de Gabber, Lemma 4.6, printed p.144, final dimension count;
Stacks Project, Morphisms, Tags 02JU and 0BAG, and Morphisms of Spaces, Tag 0BAX
(blueprint: lem-sfb-constructible-closure-fibre-avoidance).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A constructible locus of sufficiently high geometric-fibre codimension has closure
containing no entire geometric fibre; its open complement is smooth and surjective.
Purity is written on the irreducible components of the actual geometric-fibre point space.
The conditional dimension bound is `-∞` when `r - c` is negative, so it forces emptiness.
The map `q` is a map of algebraic spaces to the represented arithmetic scheme `T`;
surjectivity uses its canonical map on field-valued point classes.

Source: Deligne, Le lemme de Gabber, Lemma 4.6, printed p.144, final dimension count;
Stacks Project, Tags 02JU, 0BAX and 0BAG
(blueprint: lem-sfb-constructible-closure-fibre-avoidance).

Proof plan (the node's twelve steps):
1. Put $n=r-c$. Since $T$ is nonempty and $c>\dim T$, $D=\dim T$ is finite and nonnegative. If
$n<0$, the hypothesis makes the inverse image of $Z$ in every geometric fibre empty: a nonempty
space has a length-zero irreducible closed chain. Any point of $Z$, represented by a field-valued
point of $X$, persists after taking an algebraic closure of that field and would give a point of
one of those inverse images. Thus $Z=\varnothing$; then $W=X$ proves both conclusions. Henceforth
assume $n\geq0$. Inputs: def-kun-topological-krull-dimension, def-weil-geometric-point,
lem-pc-algebraic-closure-exists-unique.

2. The arithmetic finite-type hypothesis makes $T$ Noetherian. Since $q$ is quasi-compact and $T$
is quasi-compact, $|X|$ is quasi-compact: take finitely many affine opens of $T$ and finite
subcovers on their inverse images. Choose a representable surjective etale atlas $p:U\to X$ with
$U$ affine. The composite $f=q p:U\to T$ is smooth, surjective, and locally of finite type, by the
chartwise calculus. Thus $U$ is locally Noetherian; being affine it is quasi-compact, and its
point space is Noetherian by the cited topology theorem (applied also to schemes as algebraic
spaces). Inputs: lem-weil-pbc-finite-type-over-noetherian, lem-sfb-qc-space-affine-etale-atlas,
lem-sfb-stack-chartwise-smooth-etale-calculus, pqf-lem-locnoeth-lft,
lem-sfb-noetherian-space-topology.

3. In a Noetherian space every open is quasi-compact: among finite unions from an open covering
choose a maximal union, using stabilization of ascending opens; if it is not the whole open,
adjoining a covering member increases it. Consequently every inverse image under $f$ of an affine
open of $T$ is quasi-compact. Since $f$ is locally of finite type, it is of finite type. Its
ordinary and geometric fibres are therefore finite-type schemes over their fields. They are
separated: $U$ is affine and hence separated over $\operatorname{Spec}\mathbf Z$, and the relative
diagonal of $f$ is the pullback of the absolute diagonal of $U$ along $U\times_TU\to
U\times_{\operatorname{Spec}\mathbf Z}U$; base change gives the same assertion for its fibres.
Inputs: def-weil-finite-type-morphism, lem-sfb-finite-type-composition-base-change.

4. Let $E=|p|^{-1}(Z)$ and $H=\overline E\subseteq|U|$. Constructibility expresses $Z$ as a finite
union of locally closed subsets; continuity of $|p|$ therefore gives the same kind of expression
for $E$. Since $p$ is open and continuous, $H=|p|^{-1}(\overline Z)$. Indeed continuity gives one
inclusion, and for $u\in|p|^{-1}(\overline Z)$ every open neighbourhood $N$ of $u$ has open image
$p(N)$ meeting $Z$, so $N$ meets $E$. Give $H$ its reduced induced closed subscheme structure. Its
map $H\to T$ is locally of finite type: its inclusion in $U$ is an immersion and hence locally of
finite type, and compose with $f$. Inputs: def-weil-constructible-subset,
lem-a1-space-point-open-calculus, lem-weil-pbc-reduced-induced-closed-subscheme,
lem-weil-pbc-immersion-base-change-lft, lem-sfb-stack-chartwise-smooth-etale-calculus.

5. Fix $t\in T$, put $k=\kappa(t)$, and choose an algebraic closure $\Omega/k$. Write $U_t$,
$U_{\bar t}$, and $X_{\bar t}$ for the fibres, and $E_t,E_{\bar t},Z_{\bar t}$ for the inverse
images of $E,E,Z$. (Thus $E_{\bar t}=p_{\bar t}^{-1}(Z_{\bar t})$.) The map $p_{\bar t}:U_{\bar
t}\to X_{\bar t}$ is surjective etale. Let $B$ be the reduced closed subspace of $X_{\bar t}$
supported on $\overline{Z_{\bar t}}$; by hypothesis $\dim|B|\leq n$. It is separated, hence
quasi-separated: its diagonal is obtained from the diagonal of the separated space $X_{\bar t}$ by
the closed-subspace base-change calculation. The scheme $V=U_{\bar t}\times_{X_{\bar t}}B$ is
etale over $B$. On each scheme chart of $B$, etale maps are locally quasi-finite by the cited
etale lemma and etale composition. The source-dimension inequality for locally quasi-finite maps
therefore gives $\dim V\leq\dim|B|\leq n$. The closed support of $V$ in $U_{\bar t}$ contains
$E_{\bar t}$, hence also its closure. Inputs: lem-pc-algebraic-closure-exists-unique,
lem-trf-space-representable-etale-scheme-tests, lem-sfb-space-reduced-closed-support,
lem-a1-etale-space-locally-quasi-finite, lem-sfb-space-quasifinite-source-dimension-bound.

6. For later comparisons use the following direct chain argument: if $A\subseteq B$ are subspaces,
taking closures in $B$ of a strict chain of irreducible closed subsets of $A$ keeps it
irreducible, closed, and strict, since intersecting these closures with $A$ recovers the original
chain. Hence $\dim A\leq\dim B$; homeomorphisms preserve dimension by transporting chains both
ways. Applied to the closed support in the previous step, this gives $\dim\overline{E_{\bar
t}}\leq n$. Inputs: def-kun-topological-krull-dimension.

7. Let $A_t$ be the reduced induced closed subscheme on $\overline{E_t}\subset U_t$. It is
separated and of finite type over $k$: its inclusion is a closed immersion (locally finite type,
with quasi-compact inverse images of affine opens), and $U_t$ is separated of finite type. The
scalar-extension projection $v:U_{\bar t}\to U_t$ is open by universal openness over a field. The
neighbourhood argument of step 4 gives
$v^{-1}(\overline{E_t})=\overline{v^{-1}(E_t)}=\overline{E_{\bar t}}$. The closed-support
base-change theorem identifies this inverse image with the point space of $(A_t)_\Omega$.
Field-extension dimension invariance, applied to the separated finite-type scheme $A_t$ viewed as
an algebraic space, now gives $\dim A_t=\dim(A_t)_\Omega\leq n$. This uses openness only for this
field extension, not a closure identity for an arbitrary base change. Inputs:
lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-immersion-base-change-lft,
lem-sfb-finite-type-composition-base-change, lem-sc-scheme-over-field-universally-open,
lem-sfb-space-reduced-closed-support, lem-sfb-space-field-extension-dimension.

8. The closed subset $H$ of the Noetherian scheme $U$ has finitely many irreducible components
$C_i$, with generic points $\eta_i$. Each $\eta_i$ belongs to $E$. To check this, remove the other
components to obtain an open subset of $H$ containing $\eta_i$ and contained in $C_i$; density of
$E$ in $H$ then makes $E\cap C_i$ dense in $C_i$. Express this intersection as a finite union of
locally closed subsets. Irreducibility forces one of their closures to be all of $C_i$. That piece
is open in its closure, so contains a dense open of $C_i$, and thus contains its generic point.
This proves the claim without making any assertion about closure in a fibre. Inputs:
lem-sc-noetherian-closed-subset-finite-components, lem-sc-scheme-sober,
def-weil-constructible-subset.

9. Fix a generic point $\eta$ of $H$ and put $t=f(\eta)$. By step 8 its corresponding point
$u_t\in U_t$ lies in $E_t$, so its irreducible closed point closure is contained in $|A_t|$ and
has dimension at most $n$ by steps 6 and 7. The finite-type-over-a-field point-closure formula
identifies its dimension with $\operatorname{trdeg}_{\kappa(t)}\kappa_{U_t}(u_t)$. The fibre-point
residue-field formula gives $\kappa_{U_t}(u_t)=\kappa_U(\eta)$ compatibly over $\kappa(t)$: in
that formula the tensor product is
$\kappa_U(\eta)\otimes_{\kappa(t)}\kappa(t)\simeq\kappa_U(\eta)$. The closed immersion
$H\hookrightarrow U$ induces an isomorphism on residue fields. Thus every component generic point
of $H$ satisfies $\operatorname{trdeg}_{\kappa(t)}\kappa_H(\eta)\leq n$. Inputs:
def-pc-scheme-fibre, lem-sc-closed-irreducible-dimension-trdeg,
lem-weil-pbc-fibre-product-point-residue-field, lem-weil-pbc-closed-immersion-residue-field-iso.

10. Apply the generic-residue-field dimension bound to $H\to T$. Its target is locally Noetherian
by step 2, its morphism is locally of finite type by step 4, and step 9 supplies the bound at
every irreducible-component generic point. With $d=D$ and $n=r-c$ it gives $\dim H\leq D+r-c<r$.
Empty $H$ is included in the same inequality. Inputs:
lem-sfb-generic-residue-transcendence-dimension-bound.

11. If $\overline Z$ contained all of a geometric fibre $X_{\bar t}$ over an algebraically closed
field $\Omega$, step 4 and closed-support base change would make the closed immersion $H_{\bar
t}\hookrightarrow U_{\bar t}$ have full underlying support. The geometric atlas dimension theorem
gives $\dim U_{\bar t}=\dim|X_{\bar t}|=r$, since that fibre is nonempty and pure of dimension
$r$. On the other hand, for $t$ its underlying point, the field-extension inequality gives $\dim
H_{\bar t}\leq\dim H_t$, and the ordinary fibre homeomorphism identifies $|H_t|$ with a subspace
of $|H|$, of dimension at most $\dim H$ by step 6. Here $H_t$ is locally of finite type over
$\kappa(t)$ by base change. Thus $r=\dim H_{\bar t}\leq\dim H<r$, a contradiction. The argument
covers arbitrary algebraically closed extensions, not only the closures chosen in step 5. Inputs:
lem-sfb-space-reduced-closed-support, lem-sfb-space-etale-atlas-topological-dimension,
lem-sf-field-extension-dimension-upper-bound, def-pc-scheme-fibre, lem-weil-pbc-lft-base-change.

12. The complement $W$ is an open subspace. On etale scheme charts its map to $T$ is the
restriction of a smooth scheme morphism to an open subscheme, hence smooth by the cited
open-immersion composition theorem; smoothness of $W\to T$ is tested on these charts by the
chartwise calculus. For surjectivity use the chart test of the chartwise calculus for the map
$W\to T$, which is representable by algebraic spaces: let $T'\to T$ be a morphism from a scheme
and $U'\to W\times_TT'$ a surjective etale scheme chart. For $t'\in T'$ over $t\in T$, choose an
algebraically closed field $\Omega$ containing $\kappa(t')$; the geometric fibre of $W$ over the
resulting geometric point $\operatorname{Spec}\Omega\to T$ is nonempty by step 11. The point-space
image/base-change criterion, applied first to $W\to T$ and $\operatorname{Spec}\Omega\to T'\to T$,
and then to $W\to T$ and $T'\to T$, puts $t'$ in the image of $|W\times_TT'|\to|T'|$. The chart
$U'\to W\times_TT'$ is representable surjective, so its point map is surjective by the same
calculus; hence $U'\to T'$ is surjective, and $W\to T$ is surjective. These statements also handle
the case $Z=\varnothing$ separated out in step 1. Inputs: def-a1-space-open-subspace,
lem-pc-open-immersion-smooth-composition, lem-a1-space-point-open-calculus,
lem-sfb-stack-chartwise-smooth-etale-calculus.
-/
theorem constructible_closure_geometric_fibre_avoidance
    (T : Over (Spec (.of (ULift.{u} ℤ)))) [Nonempty T.left]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    (D : ℕ) (hD : topologicalKrullDim T.left = (D : WithBot ℕ∞))
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (q : X.obj.obj ⟶ yoneda.obj T)
    (hq : MapToSchemeIsLocally (@Smooth) X T q)
    (hsurj : Function.Surjective (mapPoint q))
    (hsep : MapToSchemeIsSeparated X T q)
    (hlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T q)
    (hqc : MapIsQuasiCompact q)
    (hqs : MapIsQuasiCompact (pullback.diagonal q))
    (r : ℕ)
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T.left),
      ∀ C ∈ irreducibleComponents
        (Point (Limits.pullback q
          (yoneda.map (Over.homMk (U := Over.mk (t ≫ T.hom)) t rfl)))),
        topologicalKrullDim C = (r : WithBot ℕ∞))
    (Z : Set (Point X.obj.obj)) (hZ : Topology.IsConstructible Z)
    (c : ℤ) (hc : (D : ℤ) < c)
    (hfibre : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T.left),
      topologicalKrullDim (closure
        (mapPoint (Limits.pullback.fst q
          (yoneda.map (Over.homMk (U := Over.mk (t ≫ T.hom)) t rfl))) ⁻¹' Z)) ≤
        if c ≤ (r : ℤ) then (((r : ℤ) - c).toNat : WithBot ℕ∞) else ⊥) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T.left),
      ¬ Set.range (mapPoint (Limits.pullback.fst q
        (yoneda.map (Over.homMk (U := Over.mk (t ≫ T.hom)) t rfl)))) ⊆ closure Z) ∧
    ∃ W : OpenSubspace X,
      pointImage W.val.ι = (closure Z)ᶜ ∧
      (∀ (U : Over (Spec (.of (ULift.{u} ℤ))))
        (a : yoneda.obj U ⟶ W.val.toFunctor), IsEtale a →
          Smooth (yoneda.preimage (a ≫ W.val.ι ≫ q)).left) ∧
      Function.Surjective (mapPoint (W.val.ι ≫ q)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
