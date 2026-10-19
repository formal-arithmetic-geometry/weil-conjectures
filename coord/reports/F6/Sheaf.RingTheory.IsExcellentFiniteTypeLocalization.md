## What changed

Proved `isExcellent_finiteType_localization` in
`Sheaf.RingTheory.IsExcellentFiniteTypeLocalization`, with its signature and public imports
unchanged. No other library module changes. Retained and checked the earlier attempt's
finite-type proof, integrating its two proved private transport helpers into the item;
the earlier attempt's two unlanded helper modules are not delivered.

The finite-type case combines `Algebra.FiniteType.isNoetherianRing` and
`isGRing_of_finiteType` with transitivity of finite type. The J-2 and universal-catenarity
quantifiers in `IsExcellent R` range over `Type u`; `Algebra.FiniteType.small` and
`Shrink.algEquiv` transport a finite-type algebra in another universe to that universe.
The private helpers prove invariance of open regular loci and catenarity under ring
equivalence, including correspondence of every insertable intermediate prime.

For localization, `IsLocalization.isNoetherianRing` supplies Noetherianity and
`Algebra.WeaklyEtale.of_isLocalization` (Stacks 092J(1)) supplies weak etaleness.
Apply the existing `RingHom.isExcellent_of_weaklyEtale` to the canonical algebra map.
This route is shorter given the existing statements than constructing all four
localization invariance arguments separately. The DAG proof and dependencies now record
this route. The existing theorem docstring still describes the original valid
componentwise argument; its mathematical statement is unchanged.

The item is below unit `sk-prop-a1-kummer`; it realizes no unit statement or proof step.
`lem-exc-weakly-etale-excellent` is an existing theorem of this same unit, used as a tool;
no unit route is bypassed. Existing unused tool approvals are removed, and the approval
for finite-type G-rings is retained. No new maintainer approval is written.

Validation: the complete combined item compiled cleanly through `lcompile.py` in
3.1 seconds against the current published build on resumption. No injectivity, nonzero-ring, or denominator-nonzero assumption is introduced.
The same proof covers the zero ring and submonoids containing zero. Searches retained
in `searches.jsonl` cover LeanFinder, Loogle and grep; no Mathlib excellence theorem
was found. The import-direction check permits the weakly-etale ascent import; its DAG dependencies
have no path back to this item. The retained proof and node changes were checked against
the current shared sources before delivery.

## Proved and sorry left

Closed: `isExcellent_finiteType_localization`
(node `lem-exc-finite-type-localization-excellent`), one of one original holes.
Added: zero holes. Left in the delivered module: zero holes. Split off: zero.
Both private helpers, `catenary_equiv` and `open_regular_equiv`, are proved.

The proof uses existing library declarations, including
`RingHom.isExcellent_of_weaklyEtale`, whose own proof is currently `sorry` in the shared
library (node `lem-exc-weakly-etale-excellent`). That existing hole is not added, moved,
or claimed closed by this delivery. The stage-3 proof is complete from those statements;
no claim is made that its transitive axiom closure is already free of `sorryAx`.

## No longer needed

Removed direct proof imports:

- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`
- `Sheaf.RingTheory.AdicCompletionRingEquiv`
- `Sheaf.RingTheory.GRing`
- `Sheaf.RingTheory.RegularRingEquiv`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `Mathlib.RingTheory.RegularLocalRing.Defs`
- `Sheaf.AlgebraicGeometry.IsRegularScheme`

The first, second, fourth and seventh modules are unnecessary as direct proof
dependencies because the localization proof uses weakly-etale ascent. The G-ring
notion, prime-spectrum topology and regular-local-ring API remain available through
the public imports of `ExcellentRing`, so their redundant direct imports are removed.
`FiniteTypeGRing` and `Localization.Submodule` remain needed.

Removed from this node's direct `proof_deps`:
- `lem-weil-pbc-localization-prime-residue-field-iso`
- `lem-weil-pbc-adic-completion-ring-equiv`
- `def-weil-pbc-g-ring`
- `lem-weil-pbc-regular-ring-map-ring-equiv`
- `lem-weil-pbc-localization-spectrum-embedding`
- `def-weil-regular-scheme`

The regular-local-ring conditions themselves still occur through the excellence
definition. These removals describe this proof's direct dependencies; other target
branches may still require these nodes and modules. The retained attempt's unlanded
`IsExcellentFiniteType` and `IsExcellentLocalization` modules are omitted entirely;
no public duplicate permanence declarations or new nodes are introduced.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had three compiling modules but no report or node records and
had two lines exceeding 100 characters. Its proof ideas are retained, the line widths
are fixed, and the unnecessary extra modules are eliminated.

The DAG's original localization proof is mathematically valid but longer than the
route through the already stated weakly-etale excellence theorem. The finite-type
part additionally needs explicit universe transport because the excellence
predicates quantify over algebras in the base ring's universe. This is handled by
proved ring-equivalence transports, with no changed definitions or statements.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
