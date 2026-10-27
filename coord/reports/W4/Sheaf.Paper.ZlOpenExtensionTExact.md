## What changed

Proved `WeilConjectures.ZlOpenTExact.quasiCompact` directly from Mathlib:
`LocallyOfFiniteType.isLocallyNoetherian` applied to the structure morphism gives
local Noetherianity of X, and the existing instance for open immersions into a
locally Noetherian scheme gives quasi-compactness of j. This works for empty
schemes and needs no separatedness or dimension assumption.

To keep the existing module within the compile limit, made the canonical category
and shift arguments of `AllStages` explicit and restored transparency checking before
the large normalization predicates. The proved instance `ordinaryOpenShift` names the
canonical ordinary derived-functor shift. The definition `stageStandardTStructure`
reexports the existing rational standard t-structure on the library's named finite
stage, and `AllStages` consistently uses that presentation. Localization retains its
existing canonical shift. All witnesses and equations are unchanged; no mathematical
conclusion is weakened. The final module compiled cleanly in 45.9 seconds.

The existing node's Lean attachment records the two new proved interfaces. The change
record is `coord/changes/W4-open-extension-comparison-elaboration.md`.

The theorem keeps its existing signature. Its local unused-section-variable
linter setting records that the stronger existing context is retained even
though the proof uses fewer assumptions.

## Proved and sorry left

Closed one of the item's two holes:
`WeilConjectures.ZlOpenTExact.quasiCompact`.

The existing hole in `WeilConjectures.ZlOpenTExact.openExtension_tExact` remains
unchanged, at node `lem-zl-open-extension-texact-coefficient-stages`. Its
all-stage argument and source proof remain in its docstring and DAG node.
No new holes were added and no statements were split off. This is a partial
module delivery under the brief's rule permitting one hole to be closed while
another is left untouched.

## No longer needed

No imports, nodes, or modules are pruned. All five existing public imports
are needed by the item's statements or definitions. The main theorem's
planned dependencies remain needed; closing its geometric auxiliary does
not withdraw them.

## Where the brief, the DAG or earlier work was wrong

The auxiliary's documentation argues from Noetherianity; Mathlib supplies
the slightly more general local-Noetherian open-immersion instance directly.
No mathematical correction or statement change is needed. The existing module's
large implicit-instance elaboration exceeded the file limit; the explicit instance
repair above is required to make this partial proof delivery compile. The main
all-stage theorem still requires assembling its normalized integral,
scalar, rational, and common-stage comparisons.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
