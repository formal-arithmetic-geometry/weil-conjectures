## What changed

Proved the original theorem `AlgebraicGeometry.Scheme.pbc_adic_cohomology_torsion_normal_form`
from two strictly smaller geometric and algebraic steps. Its signature, coefficient universe,
quotient indexing, hypotheses and conclusion are unchanged. Removed the unused public import of
`Sheaf.Paper.LevelwiseAdicTruncations`; all other original public imports remain.

The item now has three fully proved private comparisons. `pullbackScalarIso` obtains commutation
of derived scalar extension and geometric pullback from the scalar and geometric adjunctions
and the ring-sheaf-change comparison of their right adjoints. `pullbackHomologyIso` transports
homology along a local derived isomorphism. `pullbackTorIso` applies scalar commutation twice,
with degree-q homology and the degree-zero single functor between those applications, then
negative-first homology and coefficient restriction. This proves that the original ambient Tor
source is isomorphic to the constant model's Tor source. The main proof composes its hom with
the model epimorphism and composes the homology comparison with the model splitting.

Added `Sheaf.Paper.AdicUnliftedPerfectCharts`: extract actual perfect valuation-ring values
and local derived isomorphisms on finite strata and their covers. It asserts no free/torsion
splitting, nilpotence or Tor quotient. Added `Sheaf.Paper.ConstantPerfectDvrTorsionCalculation`:
the elementary-divisor and periodic-resolution calculation for one given constant perfect
value. It assumes no constructibility, noetherian base, stratification or local-model existence.
Its arguments are a perfect coefficient-module complex and an arbitrary scheme map.

Each new module has one public named theorem, its complete proof in words and its own node.
No data definition chooses an arbitrary witness of an unproved existence theorem. No existing
module besides the assigned item is changed, and there are no consumer adaptations. The sole
direct importer, `AdicTorFlatCriterion`, already publicly imports the removed re-export itself.
An unchanged sandbox copy validated this consumer and was then removed.

## Proved and sorry left

Closed the item's one original hole, by declaration name:

- `AlgebraicGeometry.Scheme.pbc_adic_cohomology_torsion_normal_form`
  (`lem-weil-pbc-adic-cohomology-torsion-normal-form`).

Two new holes remain, each as the entire body of its own public theorem:

- `AlgebraicGeometry.Scheme.pbc_adic_unlifted_perfect_charts`
  (`lem-weil-pbc-adic-unlifted-perfect-charts`).
- `AlgebraicGeometry.Scheme.pbc_constant_perfect_dvr_torsion_calculation`
  (`lem-weil-pbc-constant-perfect-dvr-torsion-calculation`).

This is a decomposition: one original hole closed, two strictly smaller holes added, zero
holes in the item and two across the delivered Lean files. It is not a proof of the entire
normal-form result from the three permitted axioms alone and does not claim positive net
sorry reduction. All three private comparisons and the final assembly are complete Lean.

Validation: `lcompile.py --all` compiled the chart module in 11.7 s, the constant-perfect
calculation module in 13.1 s, and the item in 52.9 s. Each file is below the 60 s limit.
The earlier isolated compile of the three private comparisons also passed (6.8 s).
After removing the unused import, the item compiled in 14.8 s. The unchanged direct
consumer also compiled successfully (the tool reported 60.1 s elapsed and exit code 0);
its temporary sandbox copy was removed. This check emitted no warnings.

Edge cases checked in the source argument: the perfect zero complex; free rank zero;
absence of torsion (N=0 and the epimorphism to zero); empty strata and covering schemes;
and quotient n=0 when the largest torsion exponent is zero. The periodic resolution for
A/(pi^(n+2)) -> A/(pi^(n+1)) begins with pi^(n+1), then pi, so Tor degree -1 is the required
quotient N/pi N when n is at least the torsion exponent. Extra degree-q cohomology coming
from adjacent torsion blocks is projected away, rather than incorrectly discarded.

## No longer needed

No existing module is withdrawn and no global module pruning is claimed. Removed the unused
public import `Sheaf.Paper.LevelwiseAdicTruncations`. Neither the original statement nor the
new proof needs any of its declarations. All other original public imports remain. The only
direct importer already publicly imports the removed module independently, preserving its
exported context. The new proof imports are all used. No unused proof import was added.

The removed edge previously reached `SfP1ChartExchange` through normalized constructible
effectivity, finite derived origin, etale derived stability/smooth duality and the projective
line trace modules. The other remaining imports of this item do not reach that module.
These modules remain needed by the direct consumer's independent imports; they are not
claimed globally pruned. The statement-dependency record for levelwise truncations is
retained; no target, definition or mathematical theorem changes. The item node now directly cites
the two new steps and the existing scalar adjunction, ring-sheaf-change and geometric operations interfaces used in the proved glue.

The original proof dependencies below are no longer *direct* dependencies of the item's
assembly, but are retained in the new nodes' proof plans, so none is claimed globally pruned:
`def-pc-kflat-complex`, `lem-pc-bounded-above-flat-kflat-site`,
`lem-sc-dvr-saturation-line-smith-normal-form`, `lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-pbc-completed-constant-finite-complex-realization`,
`lem-weil-pbc-completed-constant-sheaf-reduction`,
`lem-weil-pbc-constant-module-section-properties`,
`lem-weil-pbc-integral-stratified-perfect-characterization`,
`lem-weil-pbc-proetale-immersion-limit-preservation`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`lem-weil-proetale-weakly-etale-localization`.
There are no obsolete `tool_uses` entries to remove from the original item node.

## Where the brief, the DAG or earlier work was wrong

The existing integral normal-form theorem is a separate still-holed declaration, with E in
the smaller universe and the lifted coefficient datum. Applying it directly is impossible;
restating or importing that whole obligation would not produce the requested reduction.
The existing stratified-perfect characterization likewise needs actual coefficient transport,
not definitional equality. Its scalar-equivalence and chart-extraction work is precisely the
geometric new statement, whose conclusion is strictly the local perfect-model step.

The local algebra new statement has none of those geometric existence obligations. It starts
with an actual perfect module complex, so it isolates exactly the bounded DVR block argument
and periodic-resolution calculation of the original proof steps 2--3. It is not the original
statement with its constructibility hypothesis renamed. The item proves the comparison for
the actual ambient Tor source, instead of postponing this comparison with the new statement.

The source PDF was read at Bhatt--Scholze Lemma 6.5.8, Proposition 6.6.11 and Proposition
6.8.11. Stacks `more-algebra.tex`, `lemma-modules-PID` (Tag 0ASV), was read as the module
structure input, not falsely treated as a theorem on complexes or derived sheaves. Mathlib
supplies the submodule Smith theorem and PID module classification, but no direct completed
constant perfect-complex Tor obstruction. Fresh LeanSearch, LeanFinder, Loogle and grep
queries are recorded on the new nodes. Blueprint searches for "perfect chart", "torsion
normal form" and "periodic quotient" found no duplicate; the broader uniformizer search
was checked against the existing normal-form and parent Tor-flatness nodes.

The current rework row was checked before copying the item. The assigned source exists in
the read-only library; its attachment and mathematical dependencies are preserved. The item
has a genuine parent (`AdicTorFlatCriterion`), so withdrawal based on a missing or quarantined consumer
would be incorrect. The unit `sk-rem-rest` has no separate realized statement or proof step
bypassed by this decomposition. No target or existing definition changes meaning.

## New nodes

`lem-weil-pbc-adic-unlifted-perfect-charts`, module
`Sheaf.Paper.AdicUnliftedPerfectCharts`: geometric step 1 of the original normal-form plan,
using the actual unlifted Padic coefficient datum. The remaining work is coefficient transport
from the existing integral characterization and passage from covering sieves/slice models
to chart scheme pullbacks. No torsion or Tor assertion is included.

`lem-weil-pbc-constant-perfect-dvr-torsion-calculation`, module
`Sheaf.Paper.ConstantPerfectDvrTorsionCalculation`: algebraic steps 2--3 of the original plan
for a supplied perfect valuation-ring value, without the global category or existence of
strata. Its proof in words spells out the bounded-complex Smith induction, zero and unit
blocks, the correctly indexed periodic resolution, and projection from additional summands.

Change record: `coord/changes/T6-adic-normal-form-drop-levelwise-reexport.md` documents the
unused public-import removal, the unchanged direct consumer and all reported transitive
importers. All existing public signatures and definitions are unchanged. The only existing
node edited belongs to the assigned module.

The first delivery attempt pushed nothing: the tool refused preexisting unused-simp warnings
in an unpublished `SfP1ChartExchange` dependency, although all three submitted files compiled
(10.1 s, 9.3 s and 45.8 s). The unused import is removed to eliminate that dependency path;
no unrelated module or launcher tool was edited.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
