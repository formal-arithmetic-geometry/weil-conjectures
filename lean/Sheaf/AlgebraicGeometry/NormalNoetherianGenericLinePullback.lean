/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.RingTheory.LocalGenericUnitFactorization
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Generic-fibre-trivial lines over a normal Noetherian base

Source: Stacks Project, Divisors, Tag 0BD7, lemma-in-image-pullback
(blueprint: lem-sfb-normal-noetherian-generic-line-pullback).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- An invertible module trivial on the generic fibre of a flat family with integral
fibres over an integral normal locally Noetherian base is pulled back from the base,
provided the source is locally Noetherian and the family is quasi-compact or locally
of finite type. All module pullbacks below are the explicit tensor pullback.

Source: Stacks Project, Divisors, Tag 0BD7, lemma-in-image-pullback
(blueprint: lem-sfb-normal-noetherian-generic-line-pullback).

Proof plan, following the eight steps of the node:
1. First $Y$ is integral. Here are the affine details of Tag 0BCM. For a nonempty affine
$W=\operatorname{Spec}B$ mapping into an affine $V=\operatorname{Spec}R\subset T$, $R$ is a domain
and $B$ is flat over $R$ by [lem-weil-pbc-flat-morphism-affine-criterion]. By
[lem-trf-flat-module-torsionfree-domain], $B\to B_K$ is injective: a fraction $b/1$ is zero only
if some nonzero $r\in R$ kills $b$. Also $B_K\ne0$, since otherwise some nonzero $r$ kills $1_B$.
By [lem-weil-pbc-fibre-product-affine-spectra], $\operatorname{Spec}B_K$ is the nonempty open
$W_\eta$ in the integral fibre $Y_\eta$, so $B_K$ and hence $B$ are domains. Such $W$ form a
basis; thus $Y$ is reduced and every nonempty open meets $Y_\eta$. Any two nonempty opens meet
there since $Y_\eta$ is irreducible. Hence $Y$ is nonempty, reduced and irreducible, and is
integral by [def-pc-integral-scheme]. This is the elementary localization argument, not an
assumption of geometric integrality.

2. Choose a generating section $s_\eta$ of $M|_{Y_\eta}$. Write $k(Y)$ for the function field of
the integral scheme $Y$. By [lem-sc-integral-function-field-affine-fraction], rings on nonempty
affine opens embed in $k(Y)$. Localizing an affine ring $B$ over $R$ at $R\setminus\{0\}$ does not
change its fraction field: every fraction in either ring is a fraction in $\operatorname{Frac}B$,
and conversely $b/c$ is still a fraction of elements of $B_K$. Thus $Y$ and $Y_\eta$ have the same
generic function field. The generic value of $s_\eta$ defines a nonzero rational section $s$ of
$M$, meaning a nonzero vector in its one-dimensional generic fibre. In any local frame $v$ of $M$,
write $s=qv$, $q\in k(Y)^\times$. Equality of these rational expressions detects equality of
regular sections by the injectivity just cited. All base scalars in $K$ act through the injective
maps of these function fields.

3. Fix $x\in Y$, put $t=f(x)$, $A=\mathcal O_{T,t}$, $B=\mathcal O_{Y,x}$, and choose a frame $v$
near $x$. The rings are Noetherian domains, and $A$ is normal. Noetherianity of these
localizations follows by localizing finite generators of the contraction of any ideal. By
[def-weil-flat-morphism] the stalk map $A\to B$ is flat and local, and by
[lem-weil-pbc-flat-local-hom-faithfully-flat] it is faithfully flat and surjective on spectra. For
a prime of $A$ corresponding to a generalization $t'$ of $t$, its fibre is the localization of an
affine open of $Y_{t'}$ at the functions inverted in passing to $B$. Indeed the affine fibre
formula of [lem-weil-pbc-fibre-product-affine-spectra] and the fraction map $(b/a)\otimes
c\mapsto(b\otimes c)/(a\otimes1)$ of [lem-weil-pbc-localization-tensor-over-base] identify its
ring with that localization. It is a domain since $Y_{t'}$ is integral, and is nonzero by
surjectivity on spectra. The frame $v$ pulls back to a frame on $\operatorname{Spec}B$ and its
generic fibre. The coefficient $q$ of $s$ in this frame is a unit of $B_K$: the given $s_\eta$ and
its inverse in this frame restrict to that affine generic fibre. Apply
[lem-sfb-local-generic-unit-factorization] to get $q=h_xu_x$, with $h_x\in K^\times$, $u_x\in
B^\times$. Set $g_x=h_x^{-1}$. Then $f^*g_x\,s=u_xv$ is a regular generator near $x$, since the
unit germ and its inverse have regular representatives on a neighbourhood.

4. For any fixed $g\in K^\times$, let $W(g)$ be the locus where the rational section $f^*g\,s$ is
a regular generator of $M$. This locus is open: in a local frame its coefficient must be a unit,
and a unit germ together with its inverse spreads to a neighbourhood. It is saturated for $f$. To
see this, suppose $x\in W(g)$ lies over $t$, and let $x'\in Y_t$. Step 3 supplies $g'\in K^\times$
and a neighbourhood $W'\ni x'$ on which $f^*g'\,s$ generates. The two nonempty opens $W(g)\cap
Y_t$ and $W'\cap Y_t$ intersect since $Y_t$ is integral; take a point $z$ in their intersection.
At $z$, their ratio $f^*(g/g')$ is a regular unit. The final clause of
[lem-sfb-local-generic-unit-factorization], applied to $\mathcal O_{T,t}\to\mathcal O_{Y,z}$ with
the hypotheses verified in step 3, gives $g/g'\in\mathcal O_{T,t}^{\times}$. Its pullback is a
unit at $x'$, so $f^*g\,s$ generates at $x'$. Thus $W(g)=f^{-1}(V(g))$ for the subset
$V(g)=f(W(g))$ of $T$. Here the topology of the scheme fibre agrees with the subspace fibre by
[def-pc-scheme-fibre].

5. The map $f$ is surjective since all its fibres are nonempty. If $f$ is quasi-compact,
[lem-weil-pbc-flat-qc-surjective-quotient-map] applied to $W(g)=f^{-1}(V(g))$ says that $V(g)$ is
open. If $f$ is locally of finite type, choose Noetherian affine opens on $T$ and affine
finite-type presentations on their inverse images. By
[lem-weil-pbc-finite-type-noetherian-finite-presentation], these algebra presentations are finite
presentations, so $f$ is locally of finite presentation. By [lem-weil-pbc-flat-lfp-open], $f$ is
open; hence again $V(g)=f(W(g))$ is open. For each $t$, choose $x$ above it and $g=g_x$ from step
3. Then $t\in V(g)$ and $f^*g\,s$ generates on all of $f^{-1}V(g)$. Choose one such pair
$(V_i,g_i)$ for each $t$; the $V_i$ cover $T$.

6. On $V_i\cap V_j$, the rational function $a_{ij}=g_i/g_j$ is a regular unit. At any $t$ in the
overlap, choose $x$ above $t$. Both $f^*g_i\,s$ and $f^*g_j\,s$ generate at $x$, so the
unit-reflection clause of [lem-sfb-local-generic-unit-factorization] gives $a_{ij}\in\mathcal
O_{T,t}^{\times}$. A rational function and its inverse which belong to a stalk have regular
representatives near that point; the representatives agree on overlaps because their values in $K$
agree, by [lem-sc-integral-function-field-affine-fraction]. They therefore give a regular unit on
the entire overlap. The identities $a_{ii}=1$ and $a_{ij}a_{jk}=a_{ik}$ hold as rational functions
and hence as regular functions. Construct $N$ by gluing frames $n_i$ with $n_i=a_{ij}n_j$.
Explicitly $N(V)$ consists of families $b_i\in\mathcal O_T(V\cap V_i)$ satisfying $b_j=b_i a_{ij}$
on overlaps, with componentwise restriction and module operations. The sheaf axiom follows
componentwise from that of $\mathcal O_T$. On $V_i$ a family is determined by $b_i$ and the
displayed cocycle determines all other components, so $N|_{V_i}\cong\mathcal O_{V_i}$. Thus $N$ is
an invertible module in the sense of [def-sc-invertible-module].

7. On $f^{-1}V_i$ define $f^*N\to M$ by sending the pulled-back frame $n_i$ to $f^*g_i\,s$. This
is a module isomorphism because the latter is a regular generator. On overlaps, $n_i=a_{ij}n_j$
pulls back to the identical relation $f^*g_i\,s=f^*(a_{ij})f^*g_j\,s$; the tensor-pullback
definition [def-pc-module-pullback] sends a scalar to its image under $f^\sharp$. Hence the maps
and their inverses agree on overlaps and glue, by the sheaf axiom, to $f^*N\cong M$.
-/
theorem normal_noetherian_generic_line_pullback
    {Y T : Scheme.{u}} (f : Y ⟶ T)
    [IsLocallyNoetherian Y] [IsLocallyNoetherian T] [IsIntegral T]
    (hnormal : ∀ t : T,
      IsDomain (T.presheaf.stalk t) ∧ IsIntegrallyClosed (T.presheaf.stalk t))
    [Flat f]
    (hfibres : ∀ t : T, IsIntegral (pullback f (T.fromSpecResidueField t)))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f)
    (M : Y.Modules) [M.IsInvertible]
    (hgeneric : Nonempty
      ((Scheme.Modules.tensorPullback
        (pullback.fst f (T.fromSpecResidueField (genericPoint T)))).obj M ≅
          SheafOfModules.unit
            (pullback f (T.fromSpecResidueField (genericPoint T))).ringCatSheaf)) :
    ∃ N : T.Modules, N.IsInvertible ∧
      Nonempty ((Scheme.Modules.tensorPullback f).obj N ≅ M) := by
  sorry

end AlgebraicGeometry
