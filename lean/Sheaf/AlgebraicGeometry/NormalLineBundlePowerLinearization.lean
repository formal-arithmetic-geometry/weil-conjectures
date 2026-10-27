/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.AlgebraicGeometry.EquivariantCoherentGZero
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange

/-! # Positive powers of line bundles admit connected affine group linearizations

Source: Brion, Algebraic group actions on normal varieties, Lemma 2.9;
Stacks Project, Tags 0357 and 0BD7; Milne, Algebraic Groups, Proposition 12.48.
(blueprint: lem-sfb-normal-line-bundle-power-linearization)

The action groupoid presentation and its normalized tensor-pullback laws are the
existing ones. The forward isomorphism is written `theta`; its inverse satisfies
the existing descent convention. All equations are equations of module sheaf maps.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.EquivariantCoherent

namespace AlgebraicGeometry

/-- A positive tensor power of any invertible module on a normal separated finite-type
scheme has a linearization for any smooth connected affine finite-type group action.
The auxiliary `D` presents exactly this action's groupoid: its composition is pinned
by `ActionGroupoidModel.group_coordinate`, not chosen as an arbitrary groupoid law.
The isomorphism `theta` goes from projection pullback to action pullback. Its inverse
satisfies the recorded normalized identity and cocycle equations. Pullback along any
base change preserves these sheaf-map equalities, also for nonreduced base changes.

Source: Brion, Algebraic group actions on normal varieties, Lemma 2.9;
Stacks 0357, 0BD7; Milne, Algebraic Groups, Proposition 12.48.
(blueprint: lem-sfb-normal-line-bundle-power-linearization)

Proof plan (the accepted DAG split):
1. The case $X=\varnothing$ has the unique isomorphism and identities, with $m=1$; hence assume
$X\ne\varnothing$. Since $\operatorname{Spec}k$ is locally Noetherian (its ring has just two
ideals), [pqf-lem-locnoeth-lft] makes $X$ locally Noetherian. For a quasi-compact open $V\subseteq
X$, choose a finite affine open cover. Each coordinate ring is Noetherian by [pqf-lem-affine-open-
locnoeth], so each affine is a Noetherian space by [lem-sc-affine-noetherian-underlying-space],
with finitely many irreducible components by [lem-sc-noetherian-finite-irreducible-components].
The closures in $V$ of these finitely many irreducible subsets cover $V$, so every maximal
irreducible closed subset of $V$ is one of their maximal closures. Thus $V$ has finitely many
components. Apply [lem-sfb-normal-locally-finite-components]: write $X$ as a disjoint open cover
by normal integral schemes $X_i$. Each $X_i$ is clopen and therefore quasi-compact because $X$ is
quasi-compact. Cover it by finitely many principal affine opens inside finite-type affine charts
of $X$; adjoining the inverse of a principal-open equation preserves finite generation. Thus each
$X_i$ is separated and finite type over $k$.
Dependencies: pqf-lem-locnoeth-lft, pqf-lem-affine-open-locnoeth, lem-sc-affine-noetherian-
underlying-space, lem-sc-noetherian-finite-irreducible-components, lem-sfb-normal-locally-finite-
components.

2. The identity of $G$ is a $k$-point. By [lem-sbc-connected-rational-point-geometrically-
connected], $G_K$ is connected for every field extension $K/k$, and remains connected after any
further extension. Smooth maps are flat and locally finitely presented by [lem-pc-smooth-flat];
[lem-sfb-scheme-flat-smooth-point-base-change] therefore makes all projections $G\times_kT\to T$
smooth. Apply [lem-sbc-smooth-connected-generic-geometry-core] first over $\operatorname{Spec}K$
and then over each $X_i$: its fibres are the geometrically connected $G_{\kappa(t)}$, and the
identity section ensures nonemptiness. This proves that every $G_K$ and every $Y_i=G\times_kX_i$
is integral, and that $Y_i$ is normal. By [lem-sfb-finite-type-composition-base-change] the
projections $p_i:Y_i\to X_i$ and $Y_i\to\operatorname{Spec}k$ are finite type. Hence [pqf-lem-
locnoeth-lft] gives local Noetherianity of $Y_i$. These products are separated: their diagonals
impose the two factor-diagonal equations; on affine charts the corresponding defining surjections
remain surjective after tensoring. Thus $G$ and $Y_i$ meet the integral separated finite-type
hypotheses of Rosenlicht factorization.
Dependencies: lem-sbc-connected-rational-point-geometrically-connected, lem-pc-smooth-flat, lem-
sfb-scheme-flat-smooth-point-base-change, lem-sbc-smooth-connected-generic-geometry-core, lem-sfb-
finite-type-composition-base-change, pqf-lem-locnoeth-lft, def-weil-proper-morphism.

3. Choose $m\geq1$ from [lem-sfb-affine-group-picard-stable-exponent] and put $M=L^{\otimes m}$.
On $Y_i$ set $D_i=(a|_{Y_i})^*L\otimes(p_i^*(L|_{X_i}))^\vee$ and $E_i=D_i^{\otimes m}$. Here the
dual of a locally free rank-one sheaf is formed by the dual local frames, so evaluation identifies
$D_i^{\otimes m}$ with $(a|_{Y_i})^*M\otimes(p_i^*(M|_{X_i}))^\vee$. Tensor pullback preserves
those frames and their transition functions [def-sc-invertible-module, def-pc-module-pullback,
def-pur-sheaf-tensor-product]. If $\eta_i$ is the generic point of $X_i$ and $K_i=\kappa(\eta_i)$,
the generic fibre of $p_i$ is $G_{K_i}$. The new Picard-exponent node applied to $D_i|_{G_{K_i}}$
gives $E_i|_{G_{K_i}}\cong\mathcal O_{G_{K_i}}$. This uses an arbitrary function field $K_i$,
rather than assuming it algebraically closed.
Dependencies: lem-sfb-affine-group-picard-stable-exponent, def-sc-invertible-module, def-pc-
module-pullback, def-pur-sheaf-tensor-product.

4. Apply [lem-sfb-normal-noetherian-generic-line-pullback] to $p_i:Y_i\to X_i$ and $E_i$. Both
schemes are locally Noetherian; $X_i$ is normal integral; $p_i$ is smooth and therefore flat by
[lem-pc-smooth-flat]; every fibre $G_{\kappa(x)}$ is nonempty integral by step 2; $p_i$ is finite
type and the generic restriction is trivial by step 3. Obtain an invertible $B_i$ with
$p_i^*B_i\cong E_i$. Pull back along $s_i:x\mapsto(e,x)$. Since $p_is_i=1$ and $as_i$ is the
inclusion of $X_i$, the pullback composition identities [def-pc-module-pullback] give $B_i\cong
s_i^*E_i\cong\mathcal O_{X_i}$. Consequently $E_i$ is trivial. Contracting its trivialization with
the second line factor gives $\theta_i:p_i^*(M|_{X_i})\xrightarrow{\sim}(a|_{Y_i})^*M$. The
disjoint open cover $\{Y_i\}$ of $G\times_kX$ glues these maps and their inverses to an
isomorphism $\theta:p_2^*M\xrightarrow{\sim}a^*M$. No assertion that the action preserves $X_i$ is
needed here: $a|_{Y_i}$ has target $X$, and $M$ is defined on all of $X$.
Dependencies: lem-sfb-normal-noetherian-generic-line-pullback, lem-pc-smooth-flat, def-pc-module-
pullback.

5. Along $s:x\mapsto(e,x)$, $s^*\theta$ is an automorphism of $M$. In a local frame this is
multiplication by a unit $b$; changing the frame cancels the frame factor, so the local units glue
to $b\in\Gamma(X,\mathcal O_X)^\times$. Replace $\theta$ by $\theta\circ
p_2^*(b^{-1}\operatorname{id}_M)$. Its restriction to $s$ is now $b
b^{-1}\operatorname{id}_M=\operatorname{id}_M$. This modification is a global sheaf isomorphism,
not a choice on closed-point fibres.
Dependencies: def-sc-invertible-module, def-pc-module-pullback.

6. On $Z=G\times_kG\times_kX$, put $r(g,h,x)=(gh,x)$, $t(g,h,x)=(g,hx)$, and $v(g,h,x)=(h,x)$. The
action identity identifies the targets of $A=r^*\theta$ and $B=(t^*\theta)\circ(v^*\theta)$; both
map the pulled-back line $M_x$ to $M_{ghx}$. Thus $A^{-1}B$ is an automorphism of one invertible
sheaf. The same local-frame calculation as in step 5 yields a global unit $u\in\Gamma(Z,\mathcal
O_Z)^\times$. Restricting to $h=e$ gives $A=B=\theta_{g,x}$, and restricting to $g=e$ gives
$A=B=\theta_{h,x}$, by the normalization and the unit action identity. Hence $u(g,e,x)=u(e,h,x)=1$
as equalities of regular functions on those subschemes.
Dependencies: def-pc-module-pullback, def-sc-invertible-module.

7. Fix $i$. A closed point exists on the nonempty finite-type $X_i$ by [lem-sc-lft-over-field-
jacobson-space], and is a $k$-point $x_i$ by [lem-weil-pbc-closed-point-residue-field-base]. Apply
[lem-sfb-rosenlicht-product-unit-factorization] to the two nonempty integral separated finite-type
schemes $G$ and $Y_i=G\times_kX_i$, the unit $u|_{G\times_kY_i}$, and the basepoints $e$ and
$(e,x_i)$. Its regular-function identity yields
$$u(g,h,x)=u(g,e,x_i)\,u(e,h,x)\,u(e,e,x_i)^{-1}=1.$$ All three factors are $1$ by step 6.
Therefore $u=1$ on the disjoint open cover of $Z$ by these products. It follows that $A=B$
globally, which is exactly the required cocycle identity for $\theta$.
Dependencies: lem-sc-lft-over-field-jacobson-space, lem-weil-pbc-closed-point-residue-field-base,
lem-sfb-rosenlicht-product-unit-factorization.

8. The normalized isomorphism for $M=L^{\otimes m}$ satisfies both required identities, so it is
the asserted linearization. Applying any scheme base-change pullback functor preserves inverses,
compositions and these equalities [def-pc-module-pullback]. Thus the identities remain identities
after arbitrary base change, including nonreduced base changes; no pointwise-to-sheaf inference is
involved. The construction used no ampleness, quasi-projectivity, or connectedness of $X$.
Dependencies: def-pc-module-pullback.
-/
theorem exists_normal_line_bundle_tensorPow_linearization
    {k : Type u} [Field k] [IsAlgClosed k]
    (G X : Over (Spec (.of k))) [GrpObj G] [ModObj G X]
    [Smooth G.hom] [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (hX : ∀ x : X.left, IsDomain (X.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.left.presheaf.stalk x))
    (L : X.left.Modules) [L.IsInvertible] :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ D : ActionGroupoidModel G X,
      ∃ theta : (Scheme.groupoidModulePullback (source G X)).obj (L.tensorPow m) ≅
        (Scheme.groupoidModulePullback (target G X)).obj (L.tensorPow m),
        Scheme.groupoidModuleUnitLaw (source G X) (target G X) (identityArrow G X)
          D.laws.source_id D.laws.target_id (L.tensorPow m) theta.symm ∧
        Scheme.groupoidModuleCocycleLaw (source G X) (target G X) D.comp
          D.laws.source_comp D.laws.target_comp (L.tensorPow m) theta.symm := by
  sorry

end AlgebraicGeometry
