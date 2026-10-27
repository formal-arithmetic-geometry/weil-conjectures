## What changed

Reduced `WeilConjectures.PurityFiniteSetting.SectionRestriction.coherence` without changing
its signature. The main proof transports ordinary-etale functoriality through the canonical
source comparisons, derives family and normal functoriality, derives mixed Rees and normal
base-change naturality, and assembles the six required clauses.

Moved the existing definitions and proved geometry verbatim into
`Sheaf.Paper.PuritySectionRestrictionData`, publicly re-exported by the original module.
This supplies an acyclic prerequisite for the cohomological proof steps, with the original
full declaration names and mathematical constructions. The existing definition node's
Lean attachment follows this move; no second definition of any notion is introduced.
The change record is `coord/changes/Y2-section-restriction-proof-prerequisites.md`.

## Proved and sorry left

This is a decomposition, not a completed proof of section restriction coherence.
One original hole is closed relative to four added holes (net minus three).
The original module had one hole: `WeilConjectures.PurityFiniteSetting.SectionRestriction.coherence`.
Its proof is now complete relative to the named smaller steps. The moved data module has
zero holes. The additional theorem `rees_pairMap_comp` is proved by affine-chart gluing.
Four holes remain, each the entire proof of a named public theorem in a separate
new module, with a source, proof docstring, and matching node:

- `restrictionEtale_functorial`: `lem-pur-section-restriction-etale-functorial`.
- `section_base_comparison_laws`: `lem-pur-section-base-comparison-laws`.
- `section_fibre_squares`: `lem-pur-section-fibre-squares`.
- `section_normalized_specialization`: `lem-pur-section-normalized-specialization`.

Names above are in `WeilConjectures.PurityFiniteSetting.SectionRestriction`.
The proof preserves arbitrary nonflat base change, dimension zero, empty bases, the
counit-normalized rho/compositor formula, the actual Rees and normal maps, and the specified
DNC comparison. No orientation or coefficient-line frame is supplied. All seven delivered modules compile
through `lcompile.py`; the main coherence module and Rees composition compile without
errors or warnings.

## No longer needed

No mathematical dependency or module is withdrawn. All original public imports are preserved
transitively through the publicly imported data module. Their relocation does not prune their
mathematics. The original node's long proof is factored through the five smaller nodes; its
former proof dependencies remain prerequisites of those nodes or of the canonical data.
No upstream declaration is changed or removed. The pure Rees-composition module imports
`SectionReesBaseChangeEtale` directly; it does not need the section-cohomology data module.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned delivery `31f1d1e1064` (reviewer `C-31f1d`): the review
passed, but the landing rejected a reviewer fix named
`Y2-section-restriction-proof-prerequisites.md`. The change record was present
in the returned commit at `coord/changes/Y2-section-restriction-proof-prerequisites.md`.
The landing tool instead requires the fix-directory alias
`Y2-section-restriction-proof-prerequisites.change.md`. The change record now
documents that exact alias so the reviewer can apply any correction. The seven Lean
files match the passed head, the current item source still matches that head's base,
and maintainer-owned node metadata has been refreshed from current `sheaf-dag`.
The delivery tool will recreate the packet on current `sheaf-dag`; the repair changes
the packet instructions rather than re-pushing an unchanged packet. All seven modules
compiled cleanly on the repair retry. An earlier compile encountered transient server
temporary-directory exhaustion; the unchanged retry completed with exit code zero.

The original DAG describes valid mathematical steps but does not directly supply all the
fixed-map coherence glue. Ordinary-etale rho/compositor equations and structural-locality
coherence are different presentations and need an explicit counit-normalization calculation.
The existing `SectionExceptionalFibreCoherence` theorems help with fibre squares and normalized
specialization; none is definitionally the complete statement here. The Rees composition
formula is a separate relative-gluing calculation, absent as a public theorem in the current
source. The four geometric theorem holes mentioned by the old Lean-record note were already
closed before this assignment; the actual input has only the coherence hole.

## New nodes

`lem-pur-section-restriction-etale-functorial` states ordinary-etale restriction identity and
composition before pro-etale transport. The main proof carries out that transport.

`lem-pur-section-rees-map-composition` states coefficientwise Rees composition for commuting
closed centres, with no smoothness, Cartesian, or flatness hypothesis. The main proof derives
mixed naturality and the normal-map equations from this formula.

`lem-pur-section-base-comparison-laws` states the cohomological restriction square and base
pasting; the main proof supplies its missing geometric Rees and normal naturality clauses.

`lem-pur-section-fibre-squares` states four endpoint squares and no delta equation.

`lem-pur-section-normalized-specialization` derives delta naturality from those squares using
normalized family uniqueness, and includes the standard rank-zero normalization.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
