## What changed

Closed `AlgebraicGeometry.etaleSetSection_finite_matching` with its exact original
signature. The proof applies a fixed-pair eventual-matching theorem to each ordered
pair, chooses a common predecessor using `IsCofiltered.inf_objs_exists`, and uses
thinness to identify all composite arrows to the original stage.

Added two fully proved modules. `EtalePairRestrictionDetection` constructs the
scheme fibre product explicitly, proves its structure map qcqs, and constructs the
factorization after arbitrary base change with two `pullback.lift` calls.
`EtaleSetSectionPairMatchingEventually` applies existing section eventual equality
on that overlap, then proves persistence using comparison composition and
restriction naturality. Updated the target node's proof route and added nodes for
both helper theorems. No existing statement or definition was changed.

All three modules compiled without warnings through `lcompile.py --all`.
The empty finite family is handled by the same common-predecessor construction;
equal objects and empty overlaps use the ordinary pullback universal property.
The existing blueprint unit and its realized statement/steps remain unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.etaleSetSection_finite_matching`
(node `lem-weil-pbc-sets-section-finite-matching`).

Also fully proved the new declarations:
`AlgebraicGeometry.etaleSetSection_pair_matching_eventually`
(node `lem-weil-pbc-sets-section-pair-matching-eventually`) and
`AlgebraicGeometry.etale_pair_restriction_detection`
(node `lem-weil-pbc-etale-pair-restriction-detection`).

No direct `sorry` remains in any delivered module. No holes were added.
The existing `etaleSetSectionEventualEquality` and section comparisons remain
imported dependencies; this delivery does not claim their transitive proofs closed.

## No longer needed

Removed the target's direct proof imports
`Sheaf.AlgebraicGeometry.EtaleSetSectionComparisonLaws`,
`Sheaf.AlgebraicGeometry.EtaleSetSectionEventualEquality`, and
`Sheaf.AlgebraicGeometry.EtaleSetSectionComparisonNaturality`.
Their nodes remain required transitively by the proved fixed-pair helper, so no
existing node or module leaves the target import closure. No whole module is pruned.

The overlap detector imports only Mathlib and needs no section comparison,
eventual equality, limit cone, or cofiltered-system theory. Both new helpers are
proved, rather than being new stage-3 items requiring further proof work.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. Lean's inherited comma morphism `.w` includes
an extra identity map, so the explicit geometry uses `MorphismProperty.Over.w`.
Some equalities required explicit `change` steps through the module-exposed
etale category before pullback projection rewrites could apply.

The original DAG route is retained mathematically, with its overlap geometry
and fixed-pair persistence factored into reusable, fully proved helpers.

## New nodes

`lem-weil-pbc-etale-pair-restriction-detection` states and proves the qcqs overlap
and its base-change restriction detection, independent of any inverse system.
Its module is `Sheaf.AlgebraicGeometry.EtalePairRestrictionDetection`.

`lem-weil-pbc-sets-section-pair-matching-eventually` states and proves the
fixed-pair eventual equation at every later stage. Its module is
`Sheaf.AlgebraicGeometry.EtaleSetSectionPairMatchingEventually`.

No change records are needed: no existing statement or definition was modified.

## Second reading by B3

1. **Statements unchanged.** Compared the delivered target module with the repository version. The target declaration signature is byte-for-byte unchanged; only proof imports and proof body changed. The two added helper declarations are new nodes with signatures matching their DAG records.

2. **Proof validity.** Compiled all three delivered modules with `lcompile.py --all`; there are no direct `sorry`, axioms, unsafe declarations, or hollow definitions. The proofs use only ordinary category-theoretic constructions and the existing eventual-equality/comparison results.

3. **New statements.** Checked the overlap detector on equal and empty overlaps and arbitrary base change: the scheme pullback supplies the required factorization, and functorial restriction gives the conclusion. The fixed-pair theorem is strictly simpler than finite matching and is used by the target; neither duplicates an existing declaration found by repository search.

4. **Pruning and route.** The target's removed comparison-law, eventual-equality, and comparison-naturality imports were redundant direct imports; they remain transitively required by the fixed-pair helper. The unit's realized route is preserved through the target and fixed-pair overlap step.

5. **DAG agreement.** Updated proof routes and dependencies agree with the Lean proofs. New node metadata includes source, proof steps, searches, module/declaration records, and the target chapter/unit. No definition or statement change record is needed.

Changed during second reading: added this review section only; no Lean declarations or DAG statements were altered.
