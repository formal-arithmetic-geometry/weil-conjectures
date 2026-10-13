## What changed

Reworked `flatBaseChangeRestrictedLift_homology` to reduce the equality to two strictly
smaller intermediate results: a chain-level restricted-lift section comparison and the
general fixed augmented-lift formula for `moduleCohomologyFMap`. Added the proof-only imports
needed for these reductions. Removed the unchanged copied `FlatBaseChangeResolutionOpenMap` support file: its compiled
version is now published, so no dependency adaptation is required.

## Proved and sorry left

Assigned module: 1 of 1 original holes closed syntactically; one new lower hole added.
Net hole reduction from this delivery itself is zero, so this is a decomposition,
not an unconditional proof of the assigned result. The generic formula has no sorryAx in its axiom closure.

Closed by a compiled reduction:
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeRestrictedLift_homology` by applying
the two intermediate results and simplifying functoriality and inverse-isomorphism identities.
Also proved: `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_of_augmentedLift`, node
`lem-weil-pbc-module-cohomology-augmented-lift`, using injective replacement, sections
quasi-isomorphism, choice independence and cancellation.
Added and left sorry: `AlgebraicGeometry.Scheme.Modules.flatBaseChangeRestrictedLift_sections`,
node `lem-weil-pbc-flat-base-change-restricted-lift-sections`.
This is a decomposition of the assigned hole into one chain-level obligation; no arbitrary
witness enters a definition.

## No longer needed

Removed direct imports: `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`,
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`, and
`Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso` are no longer direct imports of the assigned module. The latter two remain proof dependencies
of the new generic formula module. `lem-weil-pbc-complex-injective-resolution-mono` and
`Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono` are not needed on this route:
Mathlib's injective replacement supplies the quasi-isomorphism directly; a degreewise mono
is unnecessary. The definition dependencies remain available through the public open-map import; the two new nodes replace the long direct route strictly below the unit level.

The old direct proof dependencies now used only inside the two smaller results are
`def-weil-pbc-flat-base-change-open-choices`,
`def-weil-pbc-flat-base-change-resolution-construction`,
`def-weil-pbc-module-cohomology-fmap`,
`lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`, and
`lem-weil-pbc-module-cohomology-fmap-functorial`. They remain needed transitively.
`def-weil-pbc-flat-base-change-resolution-open-map` remains a direct dependency.
Only `lem-weil-pbc-complex-injective-resolution-mono` is bypassed on this route;
no claim is made that its module is globally unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped at an `aesop` placeholder and reported the assigned theorem as
still sorry. The documented proof naturally factors into the two intermediate statements
added here; treating the whole section and homology argument as one opaque theorem obscured
that reduction. Compilation and the dry run were delayed by a saturated shared compilation
environment.

## New nodes

`lem-weil-pbc-flat-base-change-restricted-lift-sections` records the restriction/direct-image
square and its section-complex equality. `lem-weil-pbc-module-cohomology-augmented-lift`
records the generic fixed-lift cohomology computation. Both have complete source-based proof
docstrings, dedicated modules, and DAG records.

Edge cases checked for the new statements: neither requires flatness; an empty open gives
zero section groups, and degree zero still uses the augmentation equation. The generic
formula permits an arbitrary scheme map since pushed injectives are sections-acyclic,
without claiming that pushforward preserves injectives. The restriction statement is
before homology and therefore cannot restate the assigned cohomology equality.

## Second reading by E2

1. Compared every delivered module with the read-only repository. The only existing
   module is FlatBaseChangeRestrictedLiftHomology: its theorem signature is byte for
   byte unchanged, as is its docstring. Changes are proof bodies, proof-only imports
   and an elaboration budget. The other two modules and nodes are new. No definition
   or existing public interface is changed and no change record is needed. Verdict: pass.
2. Compiled all three modules locally in import order with lcompile.py. Read both
   private auxiliary proofs, the generic formula and the target cancellation proof.
   Exactly one syntactic sorry remains, in the named restricted-lift sections theorem;
   no definition is introduced, and no forbidden axiom or implementation escape is
   present. The existential replacement complex is used inside a theorem proof,
   never to define arbitrary mathematical data. Explicit axiom probes and the
   delivery tool's all-declaration probe are checked before delivery. Verdict: pass. Explicit #print axioms checks show propext, Classical.choice
   and Quot.sound for moduleCohomologyFMap_of_augmentedLift (no sorryAx); the
   assigned theorem and the remaining section-square theorem additionally use
   sorryAx. Thus the generic formula is fully proved, while the assigned theorem
   remains conditional on the new chain-level obligation.
3. Read the new chain-level statement against RestrictedResolutionSections,
   FlatBaseChangeOpenChoices.unit_square and flatBaseChangeResolutionQ. The restricted
   direct-image comparison conjugates t to k. Adjunction and the two augmentation
   equations give hk; the prescribed component equations give the section square
   degreewise. Empty opens and zero modules yield zero section maps; identity maps
   yield the usual restriction comparisons. The generic formula also covers p=0,
   zero coefficients and arbitrary h: it uses section acyclicity of pushed injectives,
   not preservation of injectives by pushforward. Both new docstrings give complete
   mathematical arguments and have nodes. Repeated leanfinder, loogle and Mathlib grep
   with different terms; also searched Sheaf, WeilConjectures and upstream modules.
   Existing open direct-image comparisons and the canonical section isomorphism are
   private ingredients, not duplicates of either new theorem. The remaining hole
   is a genuine chain-level part, not the assigned homology theorem renamed. Verdict: pass.
4. The proof follows the old plan: restriction, injective replacement, cohomology
   independence and cancellation. Mathlib replacement avoids the unnecessary mono
   requirement. No easier complete theorem was found. The section square is a
   substantial transport proof, not something closable by a short existing lemma.
   Read dag/units/sk-thm-p1.json: its realized statement and steps are unchanged,
   and the replaced mono node does not realize one of them. Completed the report's
   list of all old proof dependencies: only the mono result is bypassed; the others
   remain direct or transitive. Verdict: pass, decomposition with zero net holes.
5. Compared Lean with all three node records. Existing node changes are exactly
   proof, proof_deps and proof_origin. Each proof_deps equals the union of step uses;
   the two new records include source, creation, blueprint, searches, unit, chapter
   and Lean attachment. Corrected both new Lean statement strings to be exact source
   text rather than reformatted copies. Verdict: pass.

Second reading changes: tested the visibility of SchemeModulesEnoughInjectives;
a plain import fails to provide HasInjectiveResolutions in the public theorem
signature, so the original public import is necessary and retained. Made the new
section-square module import only
FlatBaseChangeMapSectionsDefs, which its statement uses, rather than the downstream
open cohomology map; corrected exact node signatures; recorded independent searches;
expanded the pruning inventory and made the decomposition/net-zero accounting explicit.
No mathematical statement or working proof was rewritten.

Sources checked against the Stacks originals: [01FB](https://stacks.math.columbia.edu/tag/01FB)
for the injective-replacement definition of the h-map,
[01EZ](https://stacks.math.columbia.edu/tag/01EZ) for section acyclicity of pushed injectives,
and [01E4](https://stacks.math.columbia.edu/tag/01E4) for the section-complex computation.
