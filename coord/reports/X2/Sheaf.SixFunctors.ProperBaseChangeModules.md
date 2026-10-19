## What changed

Proved `AlgebraicGeometry.Etale.properBaseChangeModules` in
`Sheaf.SixFunctors.ProperBaseChangeModules`, preserving its complete signature.
The proof extracts the compatibility equation and invertibility equivalence from
`exchange_forget_coefficients`, converts the chosen Cartesian square using
`IsPullback.of_iso_pullback`, converts local torsion to stalkwise torsion degree by
degree, applies abelian bounded-below proper base change, and rewrites the canonical
base-change comparison. The final implication of the equivalence supplies module
invertibility.

Public imports now name the statement's actual ingredients: proper morphisms,
chosen Cartesian squares, the canonical derived exchange comparisons, and torsion
abelian sheaves. The two theorems used only by the proof are imported privately.
The existing DAG node `det-properbasechange-modules` now records this argument and
its actual proof dependencies. No definitions or statements changed. The import
interface change is recorded in
`coord/changes/properBaseChangeModules-imports.md`.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Etale.properBaseChangeModules`
(node `det-properbasechange-modules`). Proved 1 of 1 original sorries; 0 split off;
0 new holes; 0 sorries left in the item. This proof uses the existing declared
proper-base-change theorem; it does not claim to close its upstream dependencies.

The retained proof passed a fresh `deliver3.py --no-push` compile, axiom probe,
and preflight in this session. A fresh `lcompile.py --all` check in
`scratchpad/consumer-check` compiled the revised item and all five
current unchanged direct consumers in import order:

- `Sheaf.AlgebraicGeometry.BirationalBadLocusComparison`.
- `Sheaf.AlgebraicGeometry.GabberOpenImmersionSheafFiniteness`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorsionStalk`.
- `Sheaf.AlgebraicGeometry.ProperFiniteTorAmplitude`.
- `Sheaf.Paper.OrientedProperFibreExchange`.

All compiled without errors or warnings. Consumer sources are unchanged and are
not part of this delivery. The change record lists the downstream modules.

## No longer needed

Removed the direct import of
`Sheaf.AlgebraicGeometry.ModuleCohomologyConventions`. Its theorem
`module_cohomology_conventions` (node `det-pbc-conventions-module-cohomology`)
is unnecessary as a separate proof dependency: the exact source and target
comparison isomorphisms in the statement are already used by the exchange-forgetting
lemma. The conventions node remains a statement dependency, and its mathematical
content remains below the canonical comparison constructions; this is not a claim
that the module is globally unreachable.

Removed the redundant direct import of
`WeilConjectures.SixFunctors.BaseChange.Derived`: the canonical derived exchange
comparison module already publicly imports its definitions. Replaced the public
imports of `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients` and
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` with private imports,
retaining explicit public imports of the definitions appearing in the signature.

No new lemma, node, or module is needed. The unit route is preserved: the proof
uses `thm-weil-pbc-bounded-below` exactly as planned and retains the exchange
compatibility step.

## Where the brief, the DAG or earlier work was wrong

The retained report listed four direct consumers. The current source has five;
all five compiled against the revised item. No mathematical error was found.
The planned separate use of the cohomology
conventions theorem is redundant in Lean because the named endpoint isomorphisms
in the conclusion are precisely the ones in `exchange_forget_coefficients`.
Boundedness of the forgotten object is already built into its `DerivedCategory.Plus`
type; no extra boundedness lemma is needed. Two elementary interface conversions
are needed explicitly: the chosen pullback identification to `IsPullback`, and
`Sheaf.IsTorsion` to `Scheme.IsTorsionSheaf`.

Searches: Lean Finder for module-coefficient proper base change returned general
condensed-module/sheaf infrastructure, not this theorem. Loogle located
`CategoryTheory.IsPullback.of_iso_pullback`. Repository searches located
`exchange_forget_coefficients`, `isIso_baseChange_of_isProper`,
`baseChange_eq_derivedBaseChangeMapPlus`, and
`Scheme.isTorsionSheaf_iff_isTorsion`, whose signatures were read before use.
No new statement needs edge-case exclusions: the proof introduces no assumptions
on the coefficient ring, no nonemptiness assumption, no restriction on the base-change
map, and no extra bound on K. In particular it retains zero-ring, zero-complex,
empty-scheme, and identity-square cases.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
