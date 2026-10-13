## What changed

Replaced the sorry in `RingHom.exists_complete_local_map_cohen_presentation` with a
compiling proof, with its signature and visibility unchanged. The proof applies the existing
Cohen presentation to `ULift A` to obtain coefficients in the required common universe,
transports the surjection back to A, and applies the proved new parameter-extension theorem
to `f.comp q`. It handles the field and Cohen cases separately and uses uniqueness of residue
characteristic to prove all the characteristic-dependent conclusions, including `t.head?`.

The private, fully proved `RingHom.flat_and_regular_fibre_of_parameters` derives flatness
and the regular closed fibre from the two parameter lists. It restricts weak regularity to
the initial list, upgrades it using the local Nakayama criterion, applies the existing
flatness theorem, and identifies the initial-parameter ideal with the mapped maximal ideal.
No nonempty-list hypothesis is used.

Added `Sheaf.RingTheory.CohenPowerSeriesParameterExtension`, whose public theorem is proved.
Its private helpers prove the complete-target local lift, including closedness of the
presentation kernel, and the maximal-ideal formula from the constant-coefficient kernel.
The public proof compares residue characteristics, obtains the target Cohen presentation in
the common universe, lifts the fixed source map by existing formal smoothness results, and
applies the final perturbation lemma. All maps are constructed inside theorem proofs;
there are no new definitions or data selected by a definition from an existence theorem.

Added `Sheaf.RingTheory.PowerSeriesParameterPerturbation` for the remaining construction on
fixed power-series rings. This statement has no A or B, no Cohen presentation to choose,
no formal-smoothness lift, and no flatness or closed-fibre assertion: it starts with an
already lifted local map and adjoins exactly n independent variables to its fixed target.

Validation: `lcompile.py --all` compiled all three modules without errors or warnings after
removing unused direct proof imports. The only new public open statement has a complete
source-based proof in its docstring and a matching DAG node. No existing definition,
statement, target, or other group's module was changed. The unit `sk-thm-p1` and its
`realized` steps remain unchanged.

## Proved and sorry left

Closed original hole:
- `RingHom.exists_complete_local_map_cohen_presentation`
  (`lem-weil-pbc-complete-local-map-cohen-presentation`).

Added and fully proved:
- `MvPowerSeries.exists_cohen_power_series_parameter_extension`
  (`lem-weil-pbc-cohen-power-series-parameter-extension`).
- The private helpers `RingHom.flat_and_regular_fibre_of_parameters`,
  `MvPowerSeries.local_lift_of_formally_smooth`, and
  `MvPowerSeries.power_series_maximalIdeal` are fully proved.

Added hole, and the only sorry anywhere in this delivery:
- `MvPowerSeries.exists_power_series_parameter_perturbation`
  (`lem-weil-pbc-power-series-parameter-perturbation`). Its proof is exactly `by sorry`.

This is a decomposition: one original hole closed and one strictly smaller hole added,
net zero holes closed. The original module has no sorry. Existing dependencies may still
rest on sorry; no claim of an axiom-free target proof is made.

## No longer needed

Removed these five direct proof imports from the original module:
- `Sheaf.RingTheory.FieldCohenPowerSeriesFormallySmooth`
  (`lem-weil-pbc-field-cohen-power-series-formally-smooth`).
- `Sheaf.RingTheory.FormallySmoothAdicLiftIntoComplete`
  (`lem-weil-pbc-fs-adic-lift-into-complete`).
- `Sheaf.RingTheory.PowerSeriesAdicEvaluation`
  (`lem-weil-pbc-power-series-adic-evaluation`).
- `Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete`
  (`lem-weil-pbc-power-series-field-cohen-regular-complete`).
- `Sheaf.RingTheory.PowerSeriesQuotientVariables`
  (`lem-weil-pbc-power-series-quotient-variables`).

These are no longer direct proof dependencies of the original node. Their required content
is still used transitively by the parameter-extension and perturbation nodes, so this
removes no module from the overall target closure. No global node/module pruning is claimed.
The new proved parameter-extension module also omits direct imports of adic evaluation and
power-series regular completeness, which only its perturbation dependency needs.

Neither `CompleteLocalMapRegularPresentation` nor `CompleteLocalFlatPresentation` is imported:
the former already depends on this item and would create a cycle. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original planned lifting and perturbation
steps are genuine arguments not supplied by a single existing declaration. They are now
separated: all the presentation and lifting work is proved, leaving only the perturbation
of a fixed local power-series map open. The original source and parameter clauses are kept.

The local source checkout contains the citation lists but not
`literature/stacks-project/more-algebra.tex`. Read Stacks 07NN directly at
https://stacks.math.columbia.edu/tag/07NN; its final proof paragraph is the source of the
new open theorem. WANTED: the local Stacks source file, More on Algebra, Tag 07NN, for the
new nodes. Repository literature files were not modified because the brief restricts all
writes to this sandbox.

LeanSearch returned Internal Server Error for both new-statement queries. These attempts
are recorded as unavailable, without a mathematical verdict; successful LeanFinder,
Loogle, and Mathlib-source grep searches found no existing theorem supplying the missing
parameter construction. In particular `MvPowerSeries.map.isLocalHom` concerns coefficient
maps and does not perform the required variable perturbation. Searches are recorded in
`searches.jsonl` and in the new nodes. A whole-blueprint search found no matching node;
the existing regular-presentation theorem has a different interface and depends on this item.

Edge cases checked in the new statement's source argument: n=0 gives no new variables;
e=0 still permits a Cohen uniformizer; c=0 gives the empty parameter list when n=0;
c≠0 is necessarily prime by the Cohen hypotheses. The list and dimension calculations
include these cases. The main flatness/fibre proof has no positive-dimension assumption.

## New nodes

`lem-weil-pbc-cohen-power-series-parameter-extension` records the proved bridge for a fixed
Cohen power-series source mapping locally into a complete Noetherian local ring. Its proof
uses the existing Cohen presentation, formal-smoothness, complete-target lift and kernel
nodes, then the fixed-map perturbation node. Module:
`Sheaf.RingTheory.CohenPowerSeriesParameterExtension`.

`lem-weil-pbc-power-series-parameter-perturbation` records the one remaining hole: adjoining
independent variables to the fixed target of a local map of power-series rings. Its proof
uses the existing adic-evaluation, quotient-variables and regular-completeness declarations.
Module: `Sheaf.RingTheory.PowerSeriesParameterPerturbation`. This is strictly the construction
in the last paragraph of Stacks 07NN, with parameters proved by generation and length.

Updated only `proof`, `proof_deps` and `proof_origin` of the existing item node. There are no
change records or forced adaptations because all existing interfaces remain identical.

## Second reading by U3

1. I compared the delivered item module with the repository version. The target signature and all existing declaration signatures are unchanged; only the proof and proof-only imports changed.
2. I compiled all three delivered modules with `lcompile.py --all`; they compile without errors or warnings. There are no axioms, unsafe declarations, or hollow definitions. The sole `sorry` is the explicitly named perturbation theorem listed above.
3. I checked the new public statements and their nodes. The parameter-extension theorem is proved and strictly smaller than the item. The perturbation theorem is a genuine fixed-map construction, with its source proof and edge cases documented, and is not a restatement of the item or an existing library theorem.
4. I checked the proof route and pruning. The item uses the parameter-extension bridge and the regular-generators/flatness results; removed direct imports are not needed by the item proof. The unit `sk-thm-p1` and its realized steps remain intact, and no unnecessary target-level bypass was introduced.
5. I checked that the DAG proof, dependencies, origins, and new-node Lean records match the delivered declarations. The item node records the shorter route, and the two new nodes carry their source, proof, and split status.

I changed only this report section after the first delivery dry run; no Lean code or DAG content was altered.
