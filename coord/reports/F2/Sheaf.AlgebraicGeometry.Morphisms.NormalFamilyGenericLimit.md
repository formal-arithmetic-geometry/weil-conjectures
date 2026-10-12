## What changed

Replaced the sole sorry of `AlgebraicGeometry.Scheme.exists_normal_family_generic_limit`
with a compiling proof, preserving its signature and all public imports.
The geometric existence argument is reduced to two strictly separate inputs:
`exists_normal_pointed_family_approximation` (normal Noetherian models, the family,
its section, and invertibility) and `exists_dominant_function_field_limit`
(the generic-point spectra and their limit). Neither is the original theorem renamed:
the first has no generic-fibre data, and the second has no family, section, normality,
Noetherianity, smoothness, geometric connectedness, or integer.

Added `CartesianFamilyGenericLimit`, with a complete proof from the function-field
limit input. It uses `PullbackCone.combine` to construct actual pointwise pullbacks,
constructs their cone by pullback lifts, proves its universal property explicitly,
and proves the transition maps affine by pasting and cancellation of pullback squares.
Quasi-compactness and quasi-separatedness follow by base change of the family maps.
This construction uses no arbitrarily chosen data in a definition.

The item's proof constructs each generic section by the unique pullback lift of
`(identity, t_i ≫ τ_i)`. Pullback `hom_ext` proves naturality and compatibility with
the supplied generic section. `IsPullback.of_iso` transports the generic-fibre
squares to the actual spectra of the stage function fields; the two section equations
and the family comparison equation are then proved by the projection identities.
Only the linter for unused existential binder names is disabled locally around the
existing declaration, whose binder names must remain unchanged. All compilation is
through the prescribed `lcompile.py`; all four delivered modules compile without warnings.

## Proved and sorry left

Closed the original hole:
- `AlgebraicGeometry.Scheme.exists_normal_family_generic_limit`
  (`lem-sbc-normal-family-generic-limit`): complete Lean proof from the new inputs.

Also proved the new categorical assembly theorem:
- `AlgebraicGeometry.Scheme.exists_cartesian_family_generic_limit`
  (`lem-sbc-cartesian-family-generic-limit`): no local sorry; it uses the field-limit input.

The delivery adds exactly two named whole-proof sorries:
- `AlgebraicGeometry.Scheme.exists_normal_pointed_family_approximation`
  (`lem-sbc-normal-pointed-family-approximation`), in
  `Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation`.
- `AlgebraicGeometry.Scheme.exists_dominant_function_field_limit`
  (`lem-sbc-dominant-function-field-limit`), in
  `Sheaf.AlgebraicGeometry.Morphisms.DominantFunctionFieldLimit`.

There is no sorry left in the item's module or in `CartesianFamilyGenericLimit`.
This is a decomposition: one original hole closed, two lower holes added, net -1
before any closure-specific ledger effects. The original theorem still rests on those
holes; it is not an axiom-free completion of the target.

Checked the statements' edge cases: on a singleton system over an already Noetherian
normal base, the first input is witnessed by the original base, family, and section;
the second is witnessed by its single function-field spectrum and identity limit cone.
The generic-fibre assembly works for an arbitrary qcqs family and requires neither
smoothness nor a section. In a general cofiltered category the slice over a fixed stage
is cofinal; dominant projections force each transition to be dominant. Thus the field
calculation does not implicitly assume a linearly ordered index or injective maps
without dominance. For n=1 invertibility is automatic; n=0 gives no extra case, since
an integral nonempty base has nonzero global section ring. No finiteness assumption
on the function-field extension is used.

## No longer needed

Removed these direct proof imports from the item:
- `Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Slicing`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`

The second reading restored these three modules as plain proof imports in
`NormalPointedFamilyApproximation`, as required for its still-open proof plan.
Their corresponding nodes remain needed in the proof plan of
`lem-sbc-normal-pointed-family-approximation`: normalization finiteness,
absolute Noetherian approximation, finite-presentation spreading out, and the relative
component through a smooth section. These were moved below the geometric input,
not discarded from the mathematical route. No existing DAG node or module is claimed
as globally pruned. The cartesian-family generic-fibre assembly does not require affine
family transition maps as a separate hypothesis: its generic transitions are affine
by base change of the function-field spectrum transitions. Removed that unused
hypothesis from both new intermediate interfaces before delivery.

The new generic-fibre and field-limit modules need only the Mathlib affine-transition
limit and function-field statement imports (plus the categorical pullback proof import
in the former). No smoothness, geometric connectedness, or Noetherian import remains
in those two modules. The new pointed approximation module has no function-field import.

## Where the brief, the DAG or earlier work was wrong

The existing DAG's third and fourth steps contained substantial arguments without
named interfaces. The delivery separates the function-field limit into its own node
and proves the categorical generic-fibre and pointed compatibility assembly in Lean.
The original theorem is unchanged, and the blueprint unit's limit-reduction route is kept.
No statement is disputed, no interface of another existing module changes, and there
are no forced adaptations or change records.

Read the source at Stacks Tag 0EZJ and its linked Tags 01ZA, 0C0C, and 055R.
The smoothness-descent citation in the new docstring is 0C0C, the tag actually linked
by 0EZJ. Source mathematics was not replaced by a different unit route.
Searched the source library, Sheaf modules, DAG, and blueprint for normal approximation
and generic-fibre limits; none provided these combined residual interfaces.
LeanFinder returned normalization constructions and unrelated inverse-system results;
Loogle returned basic function-field declarations. LeanSearch was unavailable with
HTTP Internal Server Error, recorded as unavailable, not as a negative search result.
All searches recorded in the nodes were actually run through `msearch.py`.

## New nodes

`lem-sbc-normal-pointed-family-approximation` records steps 1 and 2 of the original
argument: normal Noetherian approximation and descent of the smooth pointed family,
including cartesian transitions and compatible limit cones. Its docstring and node
retain normalization finiteness, spreading out, and the relative-section-component
route as the next worker's proof plan. Module:
`Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation`.

`lem-sbc-dominant-function-field-limit` isolates the field-colimit calculation in step 3.
Its hypotheses concern only an integral affine-transition limit with dominant
projections. Its proof in words specifies the actual generic stalk maps and the
fraction calculation on a cofinal slice of affine opens. Module:
`Sheaf.AlgebraicGeometry.Morphisms.DominantFunctionFieldLimit`.

`lem-sbc-cartesian-family-generic-limit` records the proved pullback assembly in step 3.
It consumes the field-limit result and constructs the generic-fibre diagram, its
limit cone, qcqs properties, affine transitions, and comparison maps without using
sections. Module: `Sheaf.AlgebraicGeometry.Morphisms.CartesianFamilyGenericLimit`.

## Second reading by F2

1. **Unchanged interfaces: pass.** Compared the item with the repository using `diff`.
   Its existing theorem signature is byte-for-byte identical, including all existential
   binders; its public imports and existing docstring are unchanged. The three additional
   modules are new. No existing definition, target, statement, or visibility changed,
   and no change record or forced adaptation is required.
2. **Proof and kernel checks: pass as a decomposition.** Independently compiled all four
   delivered modules in import order with `lcompile.py`, both before and after the repair,
   without errors or warnings. Inspected every proof: the only two textual sorries are
   the two reported whole-theorem residuals. There are no new definitions, hollow data,
   prohibited declarations, or arbitrary witnesses chosen in definitions. Scratch-copy
   `#print axioms` checks for all four public theorems report exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; the last comes from the open residuals.
   The pullback construction and section compatibility proofs are actual Lean proofs,
   but the original theorem is not yet an axiom-free completion.
3. **Residual statements: pass.** Read both source arguments and docstrings against
   [Stacks 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ),
   [01ZA](https://stacks.math.columbia.edu/tag/01ZA), and
   [055R](https://stacks.math.columbia.edu/tag/055R). The normal approximation residual
   ends before the generic-fibre argument; the field-limit residual has no family or
   section. Each is strictly a part of the original argument. Checked singleton systems,
   integral fields, the identity family, n=1, and the impossible n=0 hypothesis over an
   integral base. In a general cofiltered system, dominance of projections implies
   dominance of transitions; a cofinal slice over an affine open gives injective domain
   maps and the fraction-field colimit calculation. Neither residual has a quick direct
   proof from the existing interfaces. Independently searched with new LeanFinder
   queries about generic-point residue fields and smooth models over the integers,
   Loogle for `Scheme.functionField`, and `msearch.py grep` for descent and colimits;
   the actual searches are recorded in `searches.jsonl`. Also searched both library
   roots and inspected upstream `FunctionFieldLimit`: its proved limit is indexed by
   nonempty affine opens of a single scheme, not by the given family of stage fields.
   It supplies useful background but does not duplicate either residual.
4. **Route, imports, and pruning: pass after repair.** Read the proof from its conclusion
   backwards. The categorical assembly explicitly combines actual pullbacks, constructs
   the limiting cone and proves uniqueness, and obtains affineness by pullback pasting.
   The main proof explicitly constructs the sections and their comparison equations.
   Existing public imports support the original signature; new statement imports are
   public and proof-only imports are plain. The three old direct proof imports move below
   the normal approximation residual, with all four old DAG proof dependencies retained
   there; no old node is globally discarded. Thus pruned modules: none. The unit
   `sk-prop-input-spreading` retains its normal-model/descent/generic-fibre route. Its
   pre-existing `realized` arrays are empty; this delivery does not bypass a realized
   node or change the unit, and this item is not its key statement node.
5. **DAG correspondence: pass.** All four node Lean statements are byte-for-byte the
   corresponding declaration signatures. Each `proof_deps` is exactly the union of
   the proof steps' `uses`, and every cited node exists. The two proved nodes describe
   the actual applications, pullback lifts, limit uniqueness and section equations;
   the two open nodes retain source proofs and have the required provenance, search,
   blueprint, chapter, unit and Lean records.

Second-reading changes: restored the three plain proof-dependency imports in
`NormalPointedFamilyApproximation` and corrected the import accounting above. Added
independent search evidence to the two residual nodes and this review record. The
correct proofs and all signatures were left as written. Original holes closed: one;
new holes added: two; net -1, a decomposition, with no global module pruning.
