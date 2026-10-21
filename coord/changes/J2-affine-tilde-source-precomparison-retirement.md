# AlgebraicGeometry.affineTildeTensorSourcePrecomparison

## Reason

Retire the zero-hole Sheaf precomparison compatibility module in favor of the
complete adopted source implementation, as listed in `coord/retire-items.tsv`.
V5 already restored its complete theorem through a public source import; its
former quarantine/rework row has been reconciled. Retaining this extra module
is unnecessary once its actual direct consumer uses the canonical source chain.

The current sole direct consumer is
`Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal`, held by K7.
Its complete source core-final implementation is already publicly imported.
Make the one forced import substitution needed for retirement, preserving all
other lines of K7's module verbatim. The legacy associated-sheaf abbreviation
must stay publicly available, so the retired wrapper import becomes the legacy
normalization import. The source core-final import supplies the precomparison,
ordinary source isomorphism, derived counit, generic helpers and full proof.

No source-library file is changed. No data construction or theorem signature
changes. The target statements and unit route are unchanged. No quarantine
archive or DAG node is removed or rewritten.

## Old

The item has no local declarations; it publicly imports:

```lean
public import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase
public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre
```

Its direct consumer currently publicly imports:

```lean
public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal
```

## New

Withdraw the item's active path via `deleted.txt`:

`lean/Sheaf/Algebra/Homology/AffineTildeTensorSourceComparisonCorePre.lean`.

In the current core-final compatibility module, replace only import line 8:

```lean
public import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
```

All other source lines, public imports, visibility and docstrings of the K7-held
consumer are unchanged. Its source core-final module publicly imports the
canonical source precomparison, which publicly imports the canonical prebase
and helpers. The retained normalization import supplies `affineTildeFunctor`
and its zero-map instance. Thus the old consumer API remains available without
the withdrawn path. Neither a theorem nor its proof is removed from the adopted
source library.

The old precomparison signature preserved in V5's change record is identical
to the source signature after expanding the legacy tilde abbreviation and
renaming its unused `let H` to `_H`. This was checked by normalized textual
comparison and by applying the source theorem to the entire old signature in
Lean. The same check for `exists_affineTildeTensorSourceComparisonCore` passed.
The complete old core-final proof is identical to the source proof after the
tilde abbreviation substitution and ignoring whitespace.

The independent reader can inspect the replacement argument in the source
precomparison: apply `affineTilde_scalarExtension_comparison`, transport by the
ordinary affine pushforward comparison, and use `leftCounit_naturality` to
obtain the required counit equation. Its construction and every mathematical
hypothesis are retained. A zero complex or zero ring introduces no exceptional
case; no new statement is asserted by this retirement.

## Users

Source-only downstream checks plus searches of active and quarantined Lean
find the following complete chain. The only adapted module is K7's direct
consumer; the change is forced solely by retirement. The quarantined outer
parent remains attached to its existing node and retains its core-final import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre | J2 | Assigned retirement; its source theorem remains proved. |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal | K7 | Forced one-line import migration; all other lines and exported declarations unchanged. |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison | W6 | Quarantined outer parent; same core-final path and unchanged exported API. No edit. |

The four quarantined users of the outer parent likewise need no adaptation:
`AffineTildeDerivedTensorMate`, `AffineTildeTensorOrdinaryExchange`,
`AffineTildeTensorOrdinaryExchangePreNormalization`, and
`AffineTildeTensorOrdinaryExchangePreNormalizationChain`.

No DAG node attaches to the retired module. The existing
`lem-pc-affine-tilde-tensor-source-comparison` attaches to the outer parent;
its dependencies, proof steps and attachment remain unchanged. That parent's
complete proof still uses the same core-final theorem, now obtained through
the canonical source chain. Retirement is justified by this actual replacement
argument, not by a lack of active imports. The unit realization
`sk-thm-picard-semicon` is unchanged.

The original consumer necessarily fails when its imported item path is
withdrawn (`object file .../AffineTildeTensorSourceComparisonCorePre.olean
does not exist`). Existing compiled artifacts of the old wrapper are not
valid dependencies for this counterfactual. `deliver3.py` records this explicit
withdrawal and checks the adapted module; CODEX verifies the single-line diff.

## Status

landed 20261021T182254-L-1171910 2026-10-21 (merge of deliver/J2/Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre)
