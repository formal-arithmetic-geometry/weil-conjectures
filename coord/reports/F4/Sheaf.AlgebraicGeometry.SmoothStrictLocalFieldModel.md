## What changed

`Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel` closes its original proof hole
by assembling the geometric core and coefficient-field conclusions. Its existing
theorem signature and docstring are unchanged, byte for byte; all original public
imports are unchanged. The two new modules are proof-only imports.

`SmoothStrictLocalFieldModelCore` states the regular-local-domain, dimension,
residue-identification and algebraic-function-field part. `SmoothStrictLocalFieldModelCoeff`
states the coefficient field and the two transcendence degrees. Both have named
proof holes, complete source-based proofs in their docstrings, and matching new nodes.
The coefficient proof plan explicitly depends on the core for its residue and
fraction-field comparisons; neither new node depends on the original theorem.
No definition or existing statement changes, and there are no forced adaptations.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.smooth_strict_local_field_model`.

Holes added and left:

- `AlgebraicGeometry.Scheme.smooth_strict_local_field_model_core`, in
  `SmoothStrictLocalFieldModelCore.lean`, node `lem-sc-smooth-strict-local-field-model-core`.
- `AlgebraicGeometry.Scheme.smooth_strict_local_field_model_coeff`, in
  `SmoothStrictLocalFieldModelCoeff.lean`, node `lem-sc-smooth-strict-local-field-model-coeff`.

This is a decomposition, not a complete proof of the mathematical result. One upper
hole closes and two lower holes open (net -1 before any independent pruning).
The original module has no textual `sorry`; its theorem still depends on `sorryAx`
through the two listed statements. Neither component was closed during this review.
All three files compile, and scratch-copy `#print axioms` checks show only the
allowed standard axioms and `sorryAx`.

## No longer needed

The following old proof-only direct imports were removed from the original module;
the dependencies needed by the two source arguments are imported in those new modules:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Properties`
- `Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence`
- `Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization`
- `Sheaf.RingTheory.StrictHenselizationTriples`
- `Sheaf.RingTheory.SmoothOverFieldRegularLocal`
- `Sheaf.RingTheory.StrictHenselizationRegular`
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
- `Sheaf.RingTheory.StrictHenselizationFaithfullyFlat`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.RingTheory.StrictHenselizationDimension`
- `Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula`
- `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`
- `Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `Mathlib.FieldTheory.Separable`
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`
- `Sheaf.RingTheory.HenselianLocalRootLifting`
- `Sheaf.AlgebraicGeometry.StrictHenselization`

Every old direct `proof_deps` edge of `lem-sc-smooth-strict-local-field-model` is now
indirect through the two new nodes. No old dependency node is discarded: their union
contains every original dependency. No module is claimed pruned from the targets'
import closure. All original public imports stay in place. In particular, this
delivery makes no net progress claim from relocating imports.

## Where the brief, the DAG or earlier work was wrong

The first worker's new theorem docstrings only named the components; they did not
provide the required complete proofs in words. Its new-node search records had no
corresponding searches in this sandbox. The original dependency summaries also
omitted facts their arguments need, including the coefficient calculation's use of
the core and generic-point transcendence degree; one primitive-element dependency
used a nonexistent `def-` id. These defects are repaired using the original node's
expanded source proof and fresh recorded searches.

The initial report overstated the reduction as a proved target without giving its
hole balance. It is now explicitly reported as a decomposition. The copied
proof-only imports and unnecessary linter suppression were removed from the item.
The decomposition change record was removed: no existing interface changed, so it
was neither needed nor a valid record of a statement change.

The local checkout contains the citation tables but not the cited blueprint or
Stacks text files. I read the original node's complete eleven-step source expansion
and the cited Lean APIs, and checked Stacks Tags
[04HX](https://stacks.math.columbia.edu/tag/04HX),
[06LN](https://stacks.math.columbia.edu/tag/06LN),
[0A21](https://stacks.math.columbia.edu/tag/0A21), and
[04GG](https://stacks.math.columbia.edu/tag/04GG) online.
No source error or unit-route departure was found.

## New nodes

`lem-sc-smooth-strict-local-field-model-core`: the first five steps of the original
source argument, without the generic-point transcendence calculation needed only
by the coefficient component. Its proof uses the existing chart/triples comparison,
strict-henselization regularity, faithful flatness and dimension results, followed
by the generic-prime argument in the ind-etale presentation. It does not assert a
coefficient field or either of the final transcendence-degree conclusions.

`lem-sc-smooth-strict-local-field-model-coeff`: the separating-basis and compatible
simple-root lifting argument, followed by the transcendence-degree calculation.
Its plan uses the core as a strictly earlier input and the existing henselian,
primitive-element, uniqueness and dimension APIs. It does not assert regularity,
Krull dimension, or either structural compatibility. The signatures of both new
nodes match their Lean statements verbatim. No change record is needed.

## Second reading by F4

1. Compared every delivered module against the repository. The item is the only
   existing module; its entire theorem signature matches byte for byte. The only
   changes there are proof imports and the proof body. The other two modules and
   their declarations are new. No target, definition, visibility or existing
   public import changed. Verdict: pass after the repairs below.

2. Compiled all three modules in import order with `lcompile.py --all`. Each is a
   `module` with `@[expose] public section`; no errors or warnings. Searched for
   forbidden declarations and hidden holes: the only two holes are the complete
   `by sorry` bodies of the new named theorems. There is no new definition or
   data selection. Scratch copies with appended `#print axioms` commands show
   only standard axioms and `sorryAx`; the delivery tool also probes declarations.
   Verdict: pass as a decomposition, not as a sorry-free target proof.

3. Read both new statements and their complete arguments. In the core, the chart
   is nonempty because it contains y; smoothness gives Noetherian regularity,
   faithful flatness supplies the injection, and the kernel prime in an etale
   stage supplies algebraicity without assuming that stage maps are injective.
   In the coefficient argument, K is perfect, residue finite generation gives a
   finite separating basis, nonzero residual polynomials give units, and unique
   prescribed simple-root lifts give compatibility over all finite subextensions.
   The spectral hypotheses force K-linearity of all maps used in the two towers.
   Checked a=0 (empty basis), a=d (generic point, zero local dimension), d=0,
   positive characteristic (F is only required separably closed), and Omega
   transcendental over the residue field (use the relative separable closure,
   not Omega). All are consistent; a>d is ruled out by the dimension formula.
   Fresh msearch.py LeanFinder/Loogle/grep searches are logged in searches.jsonl
   and recorded with actual results on each node. LeanSearch was also attempted
   for each component; it returned Internal Server Error and is recorded as
   unavailable, with no no-match claim. Separate rg searches of both
   library roots and the source checkout found no matching theorem; the existing
   local-presentation, residue-model and complete/Artinian coefficient-field
   results do not assert either complete component. Verdict: true proper
   components, with remaining substantial formalization work; neither merely
   renames the whole original theorem.

4. The top proof assembles dependent existential witnesses from the two parts;
   it does not choose arbitrary data in a definition. Removed every old direct
   proof import from that module, retaining imports required by the source plans
   of the two open lemmas. The original source argument is partitioned, not
   bypassed: all old dependency nodes remain in their union. Inspected
   dag/units/sk-prop-sf-cbc.json: its realized.statement and realized.steps are
   empty, and this helper is not a realized unit statement or step. No unit or
   chapter route was changed. Verdict: pass; no closure pruning claimed.

5. Checked the Lean statements against all three node records. The original
   node names exactly the two calls of its proof. The core has source steps
   1-5; the coefficient plan uses the core, source steps 6-11, and the explicit
   generic-point dimension input. proof_deps is the union of uses, and the graph
   has no cycle through the original item. Both new nodes have self-contained
   statements, source, origin, creation, blueprint ancestry, statement/proof
   dependencies, the required search kinds (LeanSearch attempted but unavailable), and
   verbatim Lean signatures.
   Verdict: pass after correcting the incomplete dependency summaries.

Changes made in this reading: completed both docstring proofs and new-node plans;
made the coefficient node depend on the core; repaired primitive-element and
missing generic-point dependencies; replaced unsubstantiated search entries with
fresh logged results; removed copied imports from the original module and narrowed
the new modules' public imports; removed the unused i.toAlgebra local instance and
linter suppression; removed the unnecessary change record; corrected the report's
hole accounting. The mathematical statements and the successful witness assembly
are preserved.
