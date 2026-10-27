# AlgebraicGeometry.ProEtale.sp_cofinal_finite_reduction_constructibility proof context

## Reason

The completed projection proof, universal derived comparison and K-flat/Tor
transfer require exact coefficient-universe instances. Broad inherited instances
leave unconstrained universe maxima when synthesizing essentially-smallness and
sheafification. Disable those instances only inside a section, supply the existing
size-specific site-smallness proof locally, and reuse proved private helper APIs
through private `import all`. No public signature, public import, definition body,
mathematical predicate, target, or adopted-source module is changed.

## Old

Before the main theorem there was no proof-context section or private site-smallness
helper. The global commands remain verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The three original theorem proofs were `by sorry`.

## New

The same global commands and all public declarations remain unchanged. The new
proof-context commands, verbatim, are:

```lean
section
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify

private theorem cofinalSiteSmall : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] cofinalSiteSmall
```

The section ends after the main theorem. All removals are section-scoped and the
new instance registration is explicitly local. The other new declarations are
proved private helpers `cofinalPresentationScalarIso`, `cofinalTorIso`, and
`cofinalTorVanishing`. None occurs in a public signature or data definition.
All three original theorem proofs are complete.

## Users

`tools/downstream.py Sheaf.Paper.CofinalFiniteReductionConstructibility --uses
sp_cofinal_finite_reduction_constructibility sp_cofinal_finite_ideal_le
sp_cofinal_finite_quotient_compatibility` found zero downstream modules and only
the item itself mentioning these declarations. The module remains assigned by
its DAG parents; zero current importers is not used to withdraw it.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | D9 | Proofs completed; all public declarations and definitions unchanged. |

## Status

landed 20261025T143053-L-933369 2026-10-25 (merge of deliver/D9/Sheaf.Paper.CofinalFiniteReductionConstructibility)
