## What changed

Replaced the `sorry` in `AlgebraicGeometry.Scheme.Modules.cechCup_resolution_representatives`
by a reduction through Cech total homology. The three private proved helpers show
surjectivity of cycle classes, surjectivity of computing resolution classes, and
that pairing global cycles gives a target cycle. Two proof-only imports supply the
new comparison-existence and total-pairing statements. The new comparison-data
module constructs `cupCechDouble` by existing functors and specifies comparison
maps by their actual components; it chooses no data from an unproved existence.
All existing signatures, definitions and visibility are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.cechCup_resolution_representatives` (1 of 1).
The three private helper theorems are proved without additional holes.
Added two named holes:

- `AlgebraicGeometry.Scheme.Modules.exists_cupCechResolutionComparison`, node
  `lem-sc-cech-cup-resolution-comparison-exists`.
- `AlgebraicGeometry.Scheme.Modules.cupCechResolution_total_pairing`, node
  `lem-sc-cech-cup-resolution-total-pairing`.

This is a decomposition, not a completed sorry-free proof: one original hole
closed and two strictly smaller holes added, so the delivery-local net is -1.
The target and both split statements still depend on `sorryAx`; the three proved
helpers use only the standard allowed axioms. No other delivered declaration
contains `sorry`, and no definition contains or chooses arbitrary witnesses from
an unproved existence theorem. The global ledger determines import-closure totals.

## No longer needed

No original imports were removed and no whole module is claimed pruned.
The original direct proof dependencies `lem-sc-module-cup-godement-aw`,
`lem-sc-module-cup-flasque-acyclicity` and
`lem-sc-cech-comparison-map-naturality` are absent from the upper theorem's new
`proof_deps`. The first two remain in the plan of comparison existence. The
canonical predicate and its injective alpha theorem suffice for the third part;
the separate coefficient-naturality theorem is not needed by this reduction.
`lem-sc-module-cup-pairing-exists` is also not used directly: its theorem supplies
an arbitrary computing pairing, without exposing flasque terms needed here.
Godement modules remain reachable through existing public imports of
`CechCupProduct`, so the earlier claim that they were pruned was incorrect.

## Where the brief, the DAG or earlier work was wrong

The original plan's general flasque construction and signed total comparison
require interfaces not supplied by the original imports. The worker split these
into comparison existence and a total pairing. The earlier report incorrectly
said the upper proof uses the existing pairing theorem, and claimed Godement
module pruning without removing an import. The total-pairing node also cited
Godement and pairing existence unnecessarily, although its section pairing is
already an argument. The second reading corrected these records and made the
new nodes' natural-language statements match their quantifiers and hypotheses.

## Earlier second reading (a previous round; superseded)

The earlier brief review is superseded by the independent checks below.

## New nodes

`def-sc-cech-cup-resolution-comparison-data` records the actual functor-built
Cech double complex and the comparison structure with restriction, augmentation,
quasi-isomorphism and class-identification fields. It has no postponed data.

`lem-sc-cech-cup-resolution-comparison-exists` supplies one computing pairing
whose three resolutions admit these comparison data. Its docstring explains the
flasque construction, cochain equations, alpha quasi-isomorphism and cancellation
through an injective comparison. It does not assert cup compatibility or choose
any representatives, and is strictly part of the original argument.

`lem-sc-cech-cup-resolution-total-pairing` supplies the bilinear total homology
pairing and its two axis formulas for given resolutions. Its docstring gives the
sign, component construction, two Leibniz calculations, boundary descent and axis
identifications. It requires neither a cover nor a chosen resolution construction;
it does not conclude the original representative-existence statement.

No existing statement or definition changes; no change record is required.

## Second reading by N3

1. Compared every delivered module with the repository. Only the item's module
   exists there; its complete existing theorem signature is byte-for-byte
   unchanged. Its changes are proof-only imports, three private proved helpers,
   an elaboration budget and the proof body. The other three modules are new.
   No existing public definition, statement, visibility or target was changed.
   Verdict: pass.
2. Compiled all four modules in import order using the required local launcher.
   No errors or warnings. Scanned for forbidden declarations and data holes;
   only the two named split theorems contain `sorry`. A scratch copy printed
   axioms for the target, all three private helpers, both split statements and
   the new comparison definitions. Only `propext`, `Classical.choice`,
   `Quot.sound` and the reported `sorryAx` dependencies appear. Verdict: pass.
3. Read the new statements and docstring arguments against Stacks Tags 01EQ,
   0FKV and 07MB. Checked resolution-first total signs: (-1)^(i*s) is one on
   both axes; boundary descent follows from Leibniz. At p=q=0 the beta equation
   is augmentation compatibility. Zero factors give zero by bilinearity; an
   empty cover need not be a cover for the total-pairing statement, while an
   empty covering scheme has zero sections and cohomology. No quasi-coherence,
   flatness or finite-cover assumption is needed by these two statements.
   Repeated leanfinder, loogle and Mathlib grep searches with different phrases,
   and searched Sheaf and upstream sources. The existing computing-pairing
   theorem does not expose flasque terms or Cech comparisons; generic homology
   and total-complex tools do not supply these axis formulas. The existing
   class-surjectivity and paired-cycle helper proofs are private in another
   module; importing its public paired-cycle construction would add unrelated
   dependencies. No duplicate public statement or shorter complete proof found.
   Neither hole could be closed by a short application of an existing lemma.
   Verdict: pass; two genuine intermediate holes remain.
4. Read the proof from the conclusion down: injectivity of the target total
   identification reduces the class equality to the two pairing squares;
   surjectivity supplies representatives and Leibniz supplies their product
   cycle. Each new hole is a strict part of that argument. All imports serve
   signatures or this reduction. The original dependency list is accounted for
   above. The unit `sk-prop-av-cube` and its `realized` fields are unchanged;
   this intermediate reduction preserves its cube/Kunneth route. Verdict: pass.
5. Checked the four nodes against the Lean. Removed the unused existing-pairing
   dependency from the upper proof, replaced irrelevant Godement dependencies
   of the total-pairing statement with its actual supplied data, and expanded
   the comparison-existence construction plan. New nodes retain the item's
   chapter/unit, provenance, source, creation and Lean records. Recorded the
   actual new signatures verbatim and genuine repeated search results.
   Verdict: pass after repairs.

Changed in this reading: DAG statements, signatures, dependency plans and search
records; report accounting, pruning claims and review; total-pairing docstring
now explicitly explains independence of cycle representatives via boundaries.
The correct upper Lean proof and all existing signatures were retained.
