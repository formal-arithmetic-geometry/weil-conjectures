## Worker report

The module `Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback` states the Cartier
line-bundle pullback comparison.  Its main declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_tensorPullback_dual_toModules_iso`.
The helper `tensorPullbackUnitDualMap` is the canonical dual structure-sheaf comparison used
when rendering the section clause.  Both declarations have the source place and blueprint id in
their docstrings.

The node's hypotheses are rendered as follows.  The morphism of schemes `h : T' ⟶ T` is the
first explicit Lean binder.  The effective Cartier divisor on `T` is represented by
`J : T.IdealSheafData` and `hJ : J.IsInvertible`; its scheme-theoretic inverse image is the
comap ideal `J.comap h`, and the hypothesis that it is again effective Cartier is
`hJ' : (J.comap h).IsInvertible`.  These are exactly the three hypotheses in the node, with no
flatness or separatedness hypothesis.

The conclusion's line-bundle objects are
`(Scheme.Modules.tensorPullback h).obj J.toModulesᵛ` and `(J.comap h).toModulesᵛ`, using the
recorded tensor pullback and dual definitions.  The existential iso `e` is the canonical
comparison to be constructed.  The canonical-section clause is the displayed equality
```
tensorPullbackUnitDualMap h ≫
  (Scheme.Modules.tensorPullback h).map (Modules.dualMap J.toModulesι) ≫ e.hom =
  Modules.dualMap (J.comap h).toModulesι
```
which says that the dual of the ideal inclusion is carried to the dual of the pulled-back
ideal inclusion.  Away from the closed subscheme these inclusions are bases, so this same
formula renders the node's complement-trivialization clause; the module statement does not
introduce an additional arbitrary trivialization.

The dependency declarations used are:

- `AlgebraicGeometry.Scheme` from Mathlib (`def-pc-scheme`);
- `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`
  (`def-nagata-effective-cartier-ideal`);
- `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules` and
  `AlgebraicGeometry.Scheme.Modules.dual` from
  `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
  (`def-pc-divisor-line-bundle`);
- `AlgebraicGeometry.Scheme.Modules.tensorPullback` from the recorded
  `WeilConjectures.AlgebraicGeometry.TensorPullback` interface
  (`def-pc-module-pullback`);
- `CategoryTheory.Limits.pullback` is the recorded Mathlib fibre-product interface
  (`def-pc-fibre-product`);
- `AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit` from
  `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`;
- `AlgebraicGeometry.Scheme.Modules.picardTensorDualComparison` and its isomorphism theorem
  from `Sheaf.AlgebraicGeometry.PicardTensorDualComparisonIso`, used only to build the
  canonical structure-sheaf dual map in the helper.

I checked the edge cases named by the source and node: the empty divisor (unit ideal), an empty
source scheme `T'`, an open disjoint from the divisor, and a non-flat map preserving Cartier
regularity (for example `Z[t] → F_p[t]` with divisor `(t)`).  The zero pullback example
`k[t] → k` sending `t` to zero is excluded exactly because the comap ideal is not invertible.
No reducedness, Noetherian, or flatness assumption was added.

Searches for existing declarations were made before writing the module.  `msearch.py leanfinder`
with query `Cartier line bundle dual ideal pullback canonical section` returned only generic
ideal-sheaf/basic-open declarations and no exact comparison.  `msearch.py loogle` with query
`IdealSheafData, tensorPullback, dualMap` returned zero hits (the identifier is not in the
Loogle environment).  `msearch.py grep` with query `Cartier|tensorPullback|dualMap` in
`AlgebraicGeometry` returned no hits.  `rg` over `WeilConjectures/` found only the older
nonempty pullback-dual theorem, which has no section or complement clause.  `rg` over
`lean/Sheaf` found the generic `supportedDivisorSection`, but no theorem with this arbitrary
Cartier-preserving pullback statement.  `tools/blueprint_refs.py search 'Cartier pullback'`
reported no blueprint node beyond this item.  The exact node and its existing stage-1 split
were also checked with `grep -rl`.

No new DAG definition node was needed, and no statement correction or
`STATEMENT-DISPUTED` flag was found.  The module compiles cleanly with `scompile.py`; the only
proof placeholder is the main theorem's required `sorry`.

## Second reading by Q111

I reread the copied node and the complete module independently.  `h`, `J`, `hJ`, and `hJ'`
match the node's scheme morphism, effective Cartier divisor, and Cartier-preserving pullback
hypotheses.  The two modules in the existential iso are the tensor pullback of the dual ideal
and the dual of the comap ideal, exactly the recorded line bundles.  The equality has the
structure-sheaf dual comparison first, then the pulled-back dual ideal inclusion, then `e.hom`,
and equals the dual inclusion of the actual comap ideal; hence it preserves the canonical
section.  The complement statement is the basis/trivialization consequence of this equality
for an invertible ideal.  I checked that no flatness, nonempty, or affine hypothesis entered and
that the helper uses the canonical transpose-of-evaluation comparison rather than an arbitrary
choice.  No mismatch was found.
