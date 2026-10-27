## What changed

Replaced `WeilConjectures.PurityFiniteSetting.composition_model_orientation_descent`'s
single hole by a complete Lean assembly of five strictly smaller argument steps.
The assembly proves the chosen source comparison's normalization directly from
`existsUnique_compositionSourceFixed`, proves the even-block sign, and derives the
quotient-automorphism equation from the first global equality by inverse cancellation.
It retains every conjunct and every original hypothesis, including the free covering
universe and the empty-scheme cases.

Moved the 23 existing coordinate definitions, without changing their signatures or
bodies, to `Sheaf.Paper.CompositionModelOrientationDefinitions`; the original module
publicly re-exports them. This permits each remaining argument step to live in its
own module without circular imports. The public prerequisites move with the definitions.
The new definition node owns those declarations. No adopted source-library file changes.
Change record: `coord/changes/V3-model-orientation-coordinate-definitions.md`.

The five remaining steps separate: ordered affine integration and zero-section/beta
normalization; eight-factor naturality; Tate-line concentration and automorphism
detection; zero-section-to-chart assembly; and chart-to-global descent. The last
step states only the first global equality; the main proof establishes the quotient
identity. The naturality lemma works for arbitrary maps, rather than restating the
main theorem's finite-Tor naturality conjunction.

Repair of returned head `e15d33d4a91` (reviewer `C-e15d3`): retained the reviewed
Lean proof and all five split statements, and compared the packet with the current
shared source. The original item remains present; the six supporting modules and
six new nodes have not landed. The existing node differs only in the proof,
proof dependencies, proof origin, Lean attachment, and obsolete tool approvals.
The delivery tool rebuilds this packet on the current `sheaf-dag` tip.

The landing failure was a reviewer-fix filename mismatch, not a missing change
record. `tools/batch_land.py` matches a change-record override as its stem followed
by `.change.md`. The record is included at
`coord/changes/V3-model-orientation-coordinate-definitions.md`; a reviewer override
must therefore be named `V3-model-orientation-coordinate-definitions.change.md`.
The rejected basename omitted `.change`. This repair records the exact mapping in
both the report and change record; no launcher or repository tool is modified.

Second repair, returned head `bd535618050` (reviewer `C-bd535`): the reviewer
passed the mathematics again, but an editor backup named
`V3-model-orientation-coordinate-definitions.change.md.orig` was included in the
reviewer override directory. That file is absent from this sandbox and is not a
delivery file. `tools/batch_land.py` checks every directory entry, including backup
files, against the exact supported override basenames. The override directory must
contain only intended fixes: use
`V3-model-orientation-coordinate-definitions.change.md` for this record, and keep
`.orig`, `.bak`, editor swap files, and other backups outside that directory. Do
not rename the repository change record to make a backup appear to be a delivery
file. This packet updates the change record with that constraint and otherwise
preserves the independently passed Lean reduction and its node attachments.
The current source comparison still has the original item and no landed copy of
any of the six supporting modules or six new nodes. All seven files are compiled
again, and the normal delivery command rebuilds the packet on the current tip and
runs preflight before pushing.

## Proved and sorry left

Closed the original direct hole in
`WeilConjectures.PurityFiniteSetting.composition_model_orientation_descent` by
reduction to the following five named public theorems, each in its own new module:

- `WeilConjectures.PurityFiniteSetting.model_affine_integration_orientation`
  (`lem-pur-model-affine-integration-orientation`).
- `WeilConjectures.PurityFiniteSetting.model_orientation_source_naturality`
  (`lem-pur-model-orientation-source-naturality`).
- `WeilConjectures.PurityFiniteSetting.model_orientation_tate_detection`
  (`lem-pur-model-orientation-tate-detection`).
- `WeilConjectures.PurityFiniteSetting.model_chart_orientation_assembly`
  (`lem-pur-model-chart-orientation-assembly`).
- `WeilConjectures.PurityFiniteSetting.model_orientation_chart_descent`
  (`lem-pur-model-orientation-chart-descent`).

Each proof is exactly `by sorry` and has a complete source-based proof in words in
its docstring and node. No definition contains a hole; no witness is selected from
an arbitrary unproved existence theorem. The affine family is existentially
eliminated only within a proposition. This is a decomposition, not a completed
proof: one original hole closed, five lower holes added, net minus four. The original
module and the new definitions module have zero direct holes.

## No longer needed

No mathematical dependency or module is pruned. The unit route and pending parent
`thm-pur-composition-coherence` remain preserved. In particular, zero current Lean
importers is not used to withdraw the item.

The main theorem no longer imports the following proof dependencies directly:
`PurTwistSheafLocallyFree`, `DerivedPullbackTensorIso`,
`AffineOrderedIntegrationTransposes`, `AffineCoefficientCounitNormalization`,
`VectorBundlePurity`, `VectorIntegrationSiteComparison`, `CompactSupportSiteCoherence`,
`DegreeZeroDerivedMapGluing`, and `Mathlib.CategoryTheory.Adjunction.Mates`.
These are retained as dependencies of the relevant lower steps; the explicit
standalone `DerivedPullbackTensorIso` and `Mates` imports are redundant with the
remaining statement/dependency closures. The DAG now records each dependency at its
actual step. The six previous top-level tool-use approvals are removed from the main
node because its assembly uses the new lemmas; the underlying tools remain needed
below the corresponding new nodes. No whole-library progress is claimed from
moving these imports.

## Where the brief, the DAG or earlier work was wrong

The existing declared integration, vector-purity and DNC lemmas do not literally
state all coordinate expressions collected by this module. The remaining work is
the translation through the specified maps, not another theorem with the same full
conclusion. The new nodes isolate these missing translations.

Edge cases checked while designing the reduction: d=0, e=0, empty bases and empty
X; arbitrary positive coefficient levels with no ramification divisibility; and
schemes that are only relatively separated. The Tate-detection step retains a
finite-type structure morphism to the fixed field, ensuring the coefficient prime
is invertible. The chart-assembly hypothesis quantifies beta identification on all
affine smooth pairs, because an affine smooth map need not admit a single global
coordinate chart. The unchanged main theorem supplies precisely that hypothesis.

The change is entirely below the unit level and preserves the prescribed direct-sum,
DNC, and degree-zero descent route. No target signature or mathematical definition
changes. The definitions relocation is recorded for independent-reader review.

## New nodes

`def-pur-composition-model-orientation-coordinates` owns the unchanged 23 coordinate
definitions in the new shared definitions module and avoids a dependency cycle.

`lem-pur-model-affine-integration-orientation` states the affine normalized Gamma
family, rank-zero identity, affine and zero-section multiplication, and the three
actual normal-frame beta identifications; these are Steps 2–5 of the existing plan.

`lem-pur-model-orientation-source-naturality` states naturality of the fixed
comparison on all derived inputs, the map part of Step 1.

`lem-pur-model-orientation-tate-detection` states concentration, rank one and
injectivity of automorphism restriction on any open covering, Step 8.

`lem-pur-model-chart-orientation-assembly` takes zero-section multiplication and
all beta identifications to the affine beta-delta equation, Steps 5–6.

`lem-pur-model-orientation-chart-descent` takes those affine equations and target
automorphism detection to the first global orientation equality, Steps 7–9.

All node files are under `dag/nodes/sec-smooth-purity/`. All new statements were
checked against the existing DAG and current blueprint; no duplicate statement was
found. LeanSearch, LeanFinder/Loogle, and Mathlib grep searches found only generic
categorical, sheaf, or manifold results, not these specified comparison equations.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
