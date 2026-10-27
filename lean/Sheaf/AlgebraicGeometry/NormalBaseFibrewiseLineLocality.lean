/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.CartesianFamilyGenericLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Fibrewise trivial lines over a normal base

Source: Stacks Project, Divisors, Tag 0BD7, lemma-in-image-pullback, combined with
normal Noetherian approximation and Limits, Tags 0B8W and 01ZR
(blueprint: lem-sfb-normal-base-fibrewise-line-locality).

The arbitrary normal-base extension is the DAG's approximation/locality prerequisite;
Tag 0BD7 itself is used only on the integral locally Noetherian models.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An invertible module trivial on each residue-field fibre of a smooth separated,
finitely presented family with nonempty geometrically connected fibres over a normal
base is Zariski locally on the base pulled back from an invertible module.

Source: Stacks Project, Divisors, Tag 0BD7, lemma-in-image-pullback, together with
normal Noetherian approximation (pione.tex, Tag 0EZJ) and module limit descent
(Tags 0B8W and 01ZR) (blueprint: lem-sfb-normal-base-fibrewise-line-locality).

Proof plan:
1. Fix $s\in S$ and set $T=\operatorname{Spec}R$ for $R=\mathcal O_{S,s}$. By the normality
hypothesis $R$ is an integrally closed domain; it is local. Form $X_T=X\times_ST$, with line
$L_T$. Smoothness is preserved by [lem-pc-proper-base-change](2), separatedness by
[lem-weil-pbc-separated-base-change], and finite presentation by
[lem-weil-pbc-qcqs-morphism-permanence](3). The same permanence statement (2) makes $X_T$
quasi-compact and quasi-separated. Its fibres remain nonempty and geometrically connected: for a
field-valued point of $T$, the composite to $S$ factors through its image's residue field, and the
fibre is the corresponding field extension of the original fibre. These identifications follow by
applying the universal property [def-pc-fibre-product] twice. In local rank-one frames tensor
pullback sends the frame to $1\otimes e$, so $L_T$ is invertible and the given fibre
trivializations pull back to every such field-valued fibre [def-sc-invertible-module,
def-pc-module-pullback]. Uses: lem-pc-proper-base-change, lem-weil-pbc-separated-base-change,
lem-weil-pbc-qcqs-morphism-permanence, def-pc-fibre-product, def-sc-invertible-module,
def-pc-module-pullback, def-weil-residue-field.

2. Apply [lem-sfb-normal-domain-smooth-family-models] to $X_T\to T$. Work on its directed tail,
writing $T_i=\operatorname{Spec}A_i$ and $X_i\to T_i$. These are normal integral Noetherian bases
and smooth separated finitely presented families with nonempty geometrically connected fibres. The
limit is the original family and the transition maps are affine. By
[lem-trf-invertible-affine-limit-descent] there is, after increasing the starting index, an
invertible module $L_i$ on $X_i$ whose pullback to $X_T$ is $L_T$. At every later stage put $L_j$
equal to its tensor pullback. This is invertible by pulling back rank-one frames
[def-sc-invertible-module, def-pc-module-pullback]. Uses:
lem-sfb-normal-domain-smooth-family-models, lem-trf-invertible-affine-limit-descent,
def-sc-invertible-module, def-pc-module-pullback.

3. Write $K=\operatorname{Frac}R$, $\eta_i=\operatorname{Spec}\operatorname{Frac}A_i$, and
$X_{i,\eta_i}=X_i\times_{T_i}\eta_i$. Apply [lem-sbc-cartesian-family-generic-limit] to the
systems from step 2. Its hypotheses hold: the base stages are integral qcqs, every $T\to T_i$ is
dominant, all transition and comparison squares are cartesian, and the family components are qcqs.
Thus $X_{T,K}$ is the limit of the qcqs $X_{i,\eta_i}$ with affine transitions. The map
$\operatorname{Spec}K\to S$ factors through $\operatorname{Spec}\kappa(t)$ at its image $t$: on an
affine neighbourhood it is a ring map $B\to K$ with prime kernel $\mathfrak p$; the injection
$B/\mathfrak p\hookrightarrow K$ extends to its fraction field $\kappa(t)$
[def-weil-residue-field]. Consequently the assumed triviality of $L_t$ pulls back to a specified
isomorphism $L_T|_{X_{T,K}}\cong\mathcal O_{X_{T,K}}$; associativity of the fibre-product
universal property and functorial tensor pullback give the identification [def-pc-fibre-product,
def-pc-module-pullback]. Apply [lem-trf-fp-module-limit-isomorphism-descent] to the two fixed
models $L_i|_{X_{i,\eta_i}}$ and $\mathcal O_{X_{i,\eta_i}}$. Both are finitely presented since
locally they are free of rank one. It gives, at some later $j$, an isomorphism
$L_j|_{X_{j,\eta_j}}\cong\mathcal O_{X_{j,\eta_j}}$, including its inverse. Only this
generic-fibre trivialization is descended; no assertion that all fibre trivializations descend is
needed. Uses: lem-sbc-cartesian-family-generic-limit, lem-trf-fp-module-limit-isomorphism-descent,
def-pc-fibre-product, def-pc-module-pullback, def-weil-residue-field.

4. The smooth family $f_j:X_j\to T_j$ is flat by [lem-pc-smooth-flat]. Each of its residue-field
fibres is integral and nonempty by [lem-trf-smooth-connected-fibre-normal-integrality], applied to
its nonempty geometrically connected fibres. Its source is Noetherian, hence locally Noetherian,
as part of the model lemma in step 2. The normality, integrality and local Noetherianity of $T_j$
are supplied by the model lemma in step 2. Also $f_j$ is quasi-compact, since it is finitely
presented. Step 3 supplies generic triviality. All hypotheses of
[lem-sfb-normal-noetherian-generic-line-pullback] now hold, so $L_j\cong f_j^*N_j$ for an
invertible module $N_j$ on $T_j$. Uses: lem-pc-smooth-flat,
lem-trf-smooth-connected-fibre-normal-integrality,
lem-sfb-normal-noetherian-generic-line-pullback.

5. Pull this isomorphism back to $X_T$. Functoriality [def-pc-module-pullback] gives $L_T\cong
f_T^*N$ with $N$ the pullback of $N_j$ to $T$. It is invertible, since rank-one frames pull back
to rank-one frames. An invertible module on the spectrum of a local ring is trivial: by
[def-sc-invertible-module] there is an open neighbourhood of the closed point on which it is free
of rank one; this open contains some basic $D(a)$ through the closed point. Then $a$ is outside
the unique maximal ideal, hence a unit, so $D(a)=T$. Thus $N\cong\mathcal O_T$ and
$L_T\cong\mathcal O_{X_T}$. Uses: def-pc-module-pullback, def-sc-invertible-module.

6. Choose an affine open $V\subseteq S$ containing $s$ and use the directed system of affine
neighbourhoods $W\subseteq V$ of $s$ in
[lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods]. It has limit $T$, qcqs stages and
affine transitions. By [lem-weil-pbc-scheme-over-limit], the system $X_W=X\times_SW$ has limit
$X_T$ with affine transitions; take its starting stage to be $X_V$. Each $X_W$ is qcqs by
[lem-weil-pbc-qcqs-morphism-permanence](2),(3), since $p$ is finitely presented and $W$ is affine.
On the starting stage the two modules $L|_{X_V}$ and $\mathcal O_{X_V}$ are finitely presented
(locally free of rank one). Their pullbacks to the limit are isomorphic by step 5. The isomorphism
and its inverse therefore descend by [lem-trf-fp-module-limit-isomorphism-descent] to some affine
neighbourhood $U_s$ of $s$. We obtain $L|_{X_{U_s}}\cong\mathcal O_{X_{U_s}}$. This argument uses
the spectrum of the local ring, not an integral open neighbourhood of $s$. Uses:
lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods, lem-weil-pbc-scheme-over-limit,
lem-weil-pbc-qcqs-morphism-permanence, lem-trf-fp-module-limit-isomorphism-descent.

7. As $s$ varies these $U_s$ cover $S$. Take $N_s=\mathcal O_{U_s}$. Tensor pullback of the
structure sheaf is the structure sheaf (the maps $b\otimes a\mapsto b\,f^\sharp(a)$ and $b\mapsto
b\otimes1$ are inverse). Hence step 6 gives $L|_{X_{U_s}}\cong p_{U_s}^*N_s$, as required
[def-pc-module-pullback]. If $S$ is empty take the empty covering. There is no requirement to glue
the local isomorphisms or to choose them uniquely. Uses: def-pc-module-pullback.
-/
theorem normal_base_fibrewise_line_locality
    {X S : Scheme.{u}} (p : X ⟶ S)
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    [Smooth p] [IsSeparated p] [QuasiCompact p] [GeometricallyConnected p]
    (L : X.Modules) [L.IsInvertible]
    (hfibres : ∀ s : S, Nonempty
      ((Scheme.Modules.tensorPullback (pullback.fst p (S.fromSpecResidueField s))).obj L ≅
        SheafOfModules.unit _)) :
    ∃ U : S → S.Opens, (∀ s : S, s ∈ U s) ∧
      ∃ N : ∀ s : S, (U s).toScheme.Modules,
        (∀ s : S, (N s).IsInvertible) ∧
        ∀ s : S, Nonempty
          ((Scheme.Modules.tensorPullback (pullback.fst p (U s).ι)).obj L ≅
            (Scheme.Modules.tensorPullback (pullback.snd p (U s).ι)).obj (N s)) := by
  sorry

end AlgebraicGeometry
