## What changed

Repair of the return naming delivery `57b41cc966` and old base `e0d550965`:
compared the retained module with the version recorded at the returned head. That head
already contains the complete retained proof, which this packet preserves. The shared
working tree still exposes the original quarantined file rather than a live source file;
its unchanged public theorem signature and original docstring are preserved as well.
The delivery tool constructs the new packet against its freshly fetched current base.

Made a further proof improvement in `finite_stalk`: replace the explicit tensor-base-change
equivalence and surjectivity argument with Mathlib's `Module.Finite.of_isLocalizedModule`.
The helper now uses the direct localization finiteness API, imported privately from
`Mathlib.RingTheory.Localization.Finiteness`. This is a compiled proof change to the
returned version, not just a rebase or an unchanged re-push.

Restored `Sheaf.AlgebraicGeometry.RegularCurveTorsionfreeFree` from quarantine and proved
`AlgebraicGeometry.Scheme.Modules.regular_curve_torsionfree_iff_finiteLocallyFree` without
changing its signature. The proof obtains local Noetherianity and regular stalks from the given
affine neighborhoods, obtains finite stalks by localization of finite affine sections, and uses
the field/DVR dichotomy and the already-proved coherent free-stalk criterion. A finite stalk
basis proves the converse. The proved upstream `isFiniteLocallyFreeOfRank_rank` supplies the
constant generic-rank clause. The sole new helper `finite_stalk` is private and proved.

Made `WeilConjectures.AlgebraicGeometry.Coherent` a public statement import and replaced the
unused public torsion-subsheaf import by the function-field and canonical scheme stalk-module
imports. Updated the node proof and its dependency list to match the formal proof.

Change record: `coord/changes/K7-regular-curve-public-statement-imports.md`.

## Proved and sorry left

The original quarantined module had one hole, now closed:
`AlgebraicGeometry.Scheme.Modules.regular_curve_torsionfree_iff_finiteLocallyFree`
(node `lem-sc-regular-curve-torsionfree-free`). Added zero holes; zero holes remain in the
item, and no new modules or unproved statements are delivered. Relative to the already-proved
returned head, this repair closes zero additional holes and leaves zero holes. The original
quarantine-to-proof change closes one hole; no decomposition is involved.

The unchanged theorem covers dimension zero, dimension one, the zero sheaf and arbitrary
finite ranks. The field branch and empty finite basis are included. Searches via msearch.py
(LeanFinder, Loogle and grep) found no direct theorem for the full generality. The smooth-curve
upstream theorem has stronger hypotheses, so its stalk argument is used instead.

## No longer needed

Removed the public import `Sheaf.AlgebraicGeometry.TorsionSubsheafQuotient` and its proof
node `lem-sc-torsion-subsheaf-quotient`: torsion-freeness in the existing statement is already
stalkwise, and both directions can be proved directly without constructing the torsion subsheaf.
Its statement dependency stays to document the meaning of the torsion terminology.

Removed private imports `WeilConjectures.AlgebraicGeometry.FunctionField` (the integral
function field is Mathlib's), `Sheaf.AlgebraicGeometry.CoherentFiniteType` (the actual coherent
hypothesis is used through the proved coherent/finite-type equivalence), and
`Sheaf.AlgebraicGeometry.IsRegularScheme` (the explicit affine regularity hypothesis suffices).
The definition nodes `def-weil-regular-scheme`, `pqf-def-coherent`, `def-pc-integral-scheme` and
`def-sc-function-field` still document notions used in the proof. The DVR and coherent
free-stalk dependencies are retained. No upstream declaration or module is removed.

## Where the brief, the DAG or earlier work was wrong

The returned landing reported an intervening write after the old delivery base. The
returned head contains the completed proof, whereas the shared working tree exposes only
the original quarantine source. This repair preserves the returned proof and simplifies
its localization helper rather than overwriting it with a pre-sync version. The resulting
module compiles against the current published build.

The item was not at lean/ when assigned: the upstream sync moved it to quarantine/. Its recorded
failure was public visibility of `RingedSpace.IsCoherent`; the repair makes that import public.
The mathematical statement and its Stacks Tag 0CC4 proof plan were correct. Finite generation of
stalks needed explicit Lean glue, supplied by the proved private localization helper.

Reused `pqf-lem-coherent-ft-locnoeth`,
`lem-weil-pbc-quasi-coherent-finite-type-affine` and
`lem-sbc-affine-module-germ-localization` as existing tool results for that helper. Their
published declarations are proved and state exactly the quasi-coherence, finite affine sections
and germ-localization facts used. They do not change the unit route. No new nodes are needed.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
