# WeilConjectures.ConstantPurityFrobenius.commonStageDerivedPullback_map_inclusion

## Reason

Correct the transport node's prose to its existing Lean declaration. Its old prose
repeated transport of the whole Frobenius equation; its attachment has always been the
strictly smaller pullback-map formula. No Lean signature, definition, instance,
global attribute, public import, or target statement changes.

## Old

Given the rational-stage normalized constant-unit Frobenius coherence for the least finite coefficient field, the prescribed common-stage inclusion and pullback comparison satisfy the corresponding common-stage coherence equation.

## New

Let $\ell$ be prime, $\Omega$ an algebraic closure of $\mathbf Q_\ell$, and $f:X\to Y$ a scheme morphism such that $\ell$ is invertible in every residue field of $X$ and $Y$. Use the common-stage categories and finite-stage inclusions $j_L$ of [def-weil-algebraically-closed-coefficients], and the rational and common-stage pullback functors of [def-weil-derived-pullback-tensor-hom]. For any finite coefficient stage $L$ and arrow $a:P\to Q$ in the rational constructible category of $Y$ with coefficient field $L$, the common-stage pullback of $j_L(a)$ is heterogeneously equal to $j_L(Lf_L^*(a))$. The endpoint equalities are the prescribed object formulas identifying $Lf_\Omega^*(j_L(P))$ and $Lf_\Omega^*(j_L(Q))$ with $j_L(Lf_L^*(P))$ and $j_L(Lf_L^*(Q))$, respectively.

The Lean declaration recorded in the node's `lean.statement` stays verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonConstantUnitFrobenius | J6 | Same Lean signature; the proved map formula is used in commonUnit_frobenius. |

No base DAG node cites this transport node. The same delivery adds it as a proof
dependency of `lem-pur-common-constant-unit-frobenius` without changing that statement.
There is no effect on any untouched consumer or on the locked targets.

## Status

landed 20261028T034818-L-3551272 2026-10-28 (merge of deliver/J6/Sheaf.Paper.CommonConstantUnitFrobenius)
