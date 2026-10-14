## What changed

Reduced `baseChangeTargetSheafComparison_naturality` to target-transition normalization
and underived inverse-image coefficient coherence. The geometric square is proved by
pullback uniqueness. A generic higher-image coefficient square is proved from the
existing higher-image transition composition theorem. Abstract categorical pasting
combines these steps.

The comparison definition retains its signature and the same three isomorphisms.
A proved mapping and isomorphism API gives every map explicit higher-image endpoint
objects, avoiding repeated normalization of derived constructions. See the change record for details.
No target statement changes. All work is confined to this item's sandbox.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Etale.baseChangeTargetSheafComparison_naturality`
by decomposition, not an axiom-free completion: one upper hole is replaced by two
strictly smaller lower statements. This is a net increase of one explicit hole,
not net proof completion of the target closure.

New holes, each in its own module and with a node and complete proof in words:

- `AlgebraicGeometry.Etale.baseChangeTargetTransition_higherImage`: normalize a target
  transition with an arbitrary coefficient morphism. No geometric comparison occurs.
- `AlgebraicGeometry.Etale.upperStar_coefficient_square`: an underived inverse-image
  coherence identity. No derived category, homology, or higher image occurs.

Additional proved supporting declarations:

- `AlgebraicGeometry.Etale.higherDirectImage_coefficient_square`, from the existing
  `higher_direct_image_transition_composition` theorem.
- `AlgebraicGeometry.Etale.higherDirectImageTransition_isIso_of_lower`, by preservation
  of isomorphisms under composition and functors.
- `AlgebraicGeometry.Etale.targetPullbackComparison_snd`, by `pullback.lift_snd`.

All private mathematical helpers are proved. There is no hole in any definition,
no arbitrary witness chosen from an unproved existence assertion, and no new axiom.
The remaining statements apply to arbitrary commutative rings, identity arrows,
zero coefficient sheaves, and all integer degrees where applicable.

## No longer needed

Removed this module's direct proof imports
`Sheaf.AlgebraicGeometry.BaseChangePullbackComparisonComp` and
`Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp`.
The nodes `lem-sbc-pullback-comparison-comp` and
`lem-sbc-lower-star-plus-transition-comp` are not used by this item's rewritten route.
The generic higher-image composition API replaces direct mate-pasting here.
Also removed the redundant direct proof imports
`Sheaf.AlgebraicGeometry.HigherDirectImageTransitions` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: their declarations remain
available through the public higher-image API. Their definition nodes remain used.
Every other old proof dependency is retained: `def-pc-fibre-product`,
`def-weil-pbc-inverse-image`, `def-sbc-canonical-base-change-stalk-transitions`, and
`def-sbc-module-higher-image-transitions`. Other items may still need the two
coherence modules; this is local pruning, not a claim that they disappear from
every target's import closure.

## Where the brief, the DAG or earlier work was wrong

The previous attempt had a real reduction, but did not pass compilation: the final
pasting generated large transports between derived-functor objects and timed out in
the kernel. The repaired API constructs the same maps with explicit higher-image
endpoint objects. Coefficient coherence is converted by ordinary simplification.
The final categorical pasting application supplies its objects, arrows and universe
levels explicitly; all generated terms are checked by Lean's kernel.

The unit's statement and proof steps are preserved. The reduction only changes the
coherence calculation below the unit level. Searches of the existing library and
Mathlib found composition and associativity infrastructure, not this restriction
square. The source pages read were Stacks Tags 0F07 and 09Z1.

## New nodes

- `lem-sbc-target-transition-higher-image`:
  `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage` (sorry).
- `lem-sbc-upper-star-coefficient-square`:
  `Sheaf.AlgebraicGeometry.UpperStarCoefficientSquare` (sorry).
- `lem-sbc-higher-image-coefficient-square`:
  `Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientSquare` (proved).
- `lem-sbc-higher-image-transition-isIso-of-lower`:
  `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionIsIsoOfLower` (proved).

The original node's proof, proof dependencies and proof origin follow this reduction.

Change record: `coord/changes/baseChangeTargetSheafComparison-proof-api.md`.


## Second reading by B4

1. **Unchanged statements and data: pass.** Compared the only existing delivered
   module with the repository by `diff` and by the declaration-table parser.
   Every existing declaration's statement is byte-for-byte identical; none was
   removed. The two definition-body edits are recorded in
   `coord/changes/baseChangeTargetSheafComparison-proof-api.md`. The inverse's
   construction changes only its commuting-triangle proof. The target comparison
   still composes the same target-functor isomorphism, the same higher-image
   transition, and the same mapped coefficient isomorphism. The new APIs unfold
   to these existing maps; the IsIso proof is proof irrelevant. The sole external
   named user is `BaseChangeTargetStalkHigherImageComparison`, which continues to
   apply the identical comparison and naturality statement.

2. **Proof and axioms: pass.** Read all five delivered Lean modules, including the
   custom congruence and pasting elaborators. They construct applications of
   equality, heterogeneous equality, congruence, proof irrelevance, and the proved
   categorical pasting lemma; their generated terms undergo ordinary kernel
   checking. No kernel-check bypass, axiom, unsafe declaration, arbitrary witness,
   or hollow definition is present. The only textual holes are the two named
   public theorems listed above. Local compilation and the axiom checks are
   recorded below.

3. **Split statements and search: pass.** The normalization theorem concerns an
   arbitrary target triangle and coefficient map, with no pullback comparison;
   the coefficient square concerns only underived inverse images, with no higher
   image. Both are strictly smaller parts of the original argument. Matched
   their arrow equalities and coefficient-map directions against their nodes and
   docstring arguments. Identity arrows reduce by inverse-image unit coherence;
   zero sheaves give the unique zero maps; negative q has zero higher-image
   objects. No step assumes a restriction arrow invertible or schemes qcqs.
   Read Stacks [0F07](https://stacks.math.columbia.edu/tag/0F07), the canonical
   restriction square preceding condition (2), and
   [09Z1](https://stacks.math.columbia.edu/tag/09Z1), the higher-image restriction
   setting. These are the geometric source; the generalized coefficient identities
   follow from the explicitly described naturality and composition calculations.
   Independent `msearch.py` LeanFinder, Loogle, and grep searches used single-complex
   naturality and pseudofunctor coherence terminology. They found categorical
   infrastructure, not either exact split statement. Read the existing
   `EtalePullbackSingleComp`, `HigherDirectImageOverCoherence`,
   `BaseChangePullbackComparisonComp`, and the higher-image composition and
   naturality modules. None states the full normalization or this coefficient
   square. Neither split was closable by a direct existing theorem.

4. **Route and pruning: pass after repair.** The scheme square is proved by
   pullback uniqueness; the generic higher-image square uses the existing
   `higher_direct_image_transition_composition`; the final proof pastes these
   with normalization and the underived square. No unproved renamed copy of the
   original target occurs. Removed two redundant direct proof imports and made
   the pruning list account for every old proof dependency. The unit
   `dag/units/sk-lem-failure-field.json` has empty realization lists and remains
   untouched; its condition-(2) higher-image continuity route is retained.
   This delivery remains a decomposition: one original hole closed, two added,
   net minus one in explicit hole reduction before any import-closure pruning.

5. **DAG agreement: pass after repair.** Checked the new nodes' source, statement,
   creation, blueprint ancestry, chapter, unit, Lean module and declaration
   records. Each proof_deps list equals the union of its proof steps' uses. The
   existing node changes only proof, proof_deps, and proof_origin. Restored the
   inverse-image and canonical target-transition definition dependencies in its
   actual construction steps, and added the canonical target-transition dependency
   to the API node's target-comparison and OverMap computation step.

Second-reading changes: removed two redundant imports from the item; added a
proof-only import of `EtalePullbackSingleComp` to the normalization module and a
proof-only import of underived `UpperLowerStar.Coherence` to the coefficient-square
module, so their planned proofs have the named existing lemmas available; corrected
the two dependency records; completed the pruning report. No statement or proof
construction was weakened, and no additional hole was introduced.

Validation: all five repaired modules compile locally without warnings in import
order (52.5 s, 2.0 s, 3.8 s, 23.5 s, 44.4 s respectively).
The scratch `#print axioms` audit covers every public definition and theorem of
the five modules. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the
comparison construction, generic higher-image square, and all supporting APIs.
Only the original naturality theorem and the two documented split theorems also
use `sorryAx`; no other axiom occurs. The comparison data itself is sorry-free.
