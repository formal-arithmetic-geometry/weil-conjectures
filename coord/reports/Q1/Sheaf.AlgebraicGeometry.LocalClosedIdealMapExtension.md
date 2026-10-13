## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.LocalClosedIdealMapExtension` with a
complete Lean reduction. The original theorem's signature and public imports are unchanged.
Added proof-only imports of `ClosedStructureAmbientIdealExtension`,
`ClosedStructureIdealProductIso`, and the source library's ideal-sheaf `Basic` module.
The ideal is constructed as `(I ^ n).comap i`, where I is the actual vanishing ideal of the
closed complement of U. Support containment proves it is nonzero. The map is the comparison
isomorphism followed by the ambient extension, and functorial composition proves agreement
on all of U. Updated the item's DAG proof and added the two bridge modules and nodes.
The Picard coherence unit and its realized statements and steps are unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.local_closed_ideal_map_extension`
(node `lem-pc-local-closed-ideal-map-extension`), by a complete proof from two intermediate
statements. No sorry remains in the item's module.

Added two holes, each the sole named public theorem in a new module:

- `AlgebraicGeometry.Scheme.Modules.closed_structure_ambient_ideal_extension`
  (`lem-pc-closed-structure-ambient-ideal-extension`): extends from an ambient ideal power
  times a closed structure pushforward. It neither constructs an ideal on W nor proves
  nonzeroness; it requires no integral W or generic point.
- `AlgebraicGeometry.Scheme.Modules.closed_structure_ideal_product_iso`
  (`lem-pc-closed-structure-ideal-product-iso`): compares the pushforward of the extended
  ideal with the ambient ideal product, with its inclusion equation. It has no local map,
  target module, open, Noetherian hypothesis, or generic point.

This is a decomposition: one original hole closed, two holes added, net minus one before
any other pruning. It is not an axiom-free proof of the whole import closure. The ideal's
data comes from real constructions, not an arbitrary witness of a sorry existence theorem.

All three modules compile together in import order with no compiler warnings. The original
statement is kept verbatim. Edge cases checked against the sources and constructions:
zero local map, U = X, exponent zero, zero and unit ambient ideals, and empty W in the
comparison theorem. The extension helper allows empty W and empty U. The main theorem
retains integral W and its nonempty generic point.

## No longer needed

No original import was removed: the existing public imports supply the original statement's
notions. The node's seven old direct proof dependencies are replaced by the two bridges:

- `lem-weil-pbc-reduced-induced-closed-subscheme`
  (`Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`): the main proof uses Mathlib's
  actual vanishing-ideal construction and support formula, not the reduced subscheme theorem.
- `pqf-lem-pushforward-qcoh` (`Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`),
  `lem-weil-pbc-quasi-coherent-finite-type-affine`
  (`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`),
  `pqf-lem-coherent-ft-locnoeth`
  (`Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`), and
  `lem-weil-pbc-coherent-homs-over-open` (`Sheaf.AlgebraicGeometry.CoherentHomsOverOpen`):
  these move into the ambient helper's proof plan; they are not mathematically pruned.
- `lem-weil-pbc-closed-immersion-pushforward-ideal-powers`
  (`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers`): the main proof uses
  the normalized, single-ideal comparison instead. The comparison helper uses the affine
  quotient and product formulas directly and then elementary sheaf gluing; the older
  ideal-powers theorem is unnecessary throughout this proof route.
- `lem-weil-pbc-integral-scheme-ideal-generic-stalk`
  (`Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk`): completely unnecessary for this
  argument. Nonzeroness follows from support, without a field or generic-stalk calculation.

These are claims about this proof route, not claims that other target branches no longer
import these modules. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing proof dependencies are not already imported by the item's source. More
substantially, `tools/import_direction.py may` refuses the following imports because those
modules already reach this item transitively: `CoherentHomsOverOpen`,
`ClosedImmersionPushforwardIdealPowers`, `FinitePushforwardCoherent`,
`Modules.IdealTimesQuasiCoherentAffineSections`, `ClosedImmersionIdealPowerImage`,
`ClosedImmersionPowerQuotient`, and the source library's `Modules.ClosedImmersion`,
`Modules.FinitePushforward`, and `Cohomology.DirectImage.AffineMorphism`.
The bridges avoid these import cycles without modifying modules held by other workers.
Their DAG proof plans retain the applicable existing statements, whose DAG dependencies
were separately checked not to lead back to the original node. The independent reader
should distinguish these source-import cycles from mathematical dependency cycles.

The current CoherentHomsOverOpen interface chooses its open by a stalkwise condition and
uses overFunctor. The ambient bridge states the prescribed open and uses restrictFunctor;
its proof plan explains equality of the opens and transport through overFunctorEquiv.
The old ideal-powers theorem gives equality of image subobjects, only at positive powers;
the comparison bridge gives the precise inclusion-compatible isomorphism and includes
zero/unit ideals. This is the needed interface, not a change to either existing theorem.

The repository on this machine does not contain the downloaded Stacks source. Read the
actual sources online at https://stacks.math.columbia.edu/tag/01YB,
https://stacks.math.columbia.edu/tag/01YE, and https://stacks.math.columbia.edu/tag/01QY.
LeanSearch returned HTTP 500 for both new statements; those searches are recorded as
unavailable. LeanFinder, Loogle, and Mathlib/source-library grep found no matching
normalized theorem. The blueprint search found no matching blueprint statement.
`blueprint_refs.py ancestor` returns None because created.item here is a module name;
new nodes inherit the existing item's recorded blueprint ancestor `lem-pc-coherent-hi`
and extend its via chain instead.

## New nodes

`lem-pc-closed-structure-ambient-ideal-extension`, in
`lean/Sheaf/AlgebraicGeometry/ClosedStructureAmbientIdealExtension.lean`, carries the
ambient ideal-power extension, including the closed structure module coherence check,
normalization of ideal powers, and transport to the given open's restriction functor.
Its source is Tag 01YB with Tags 01XZ and 01QY. It is strictly the extension part of the
argument, before an ideal on W or its nonzeroness is considered.

`lem-pc-closed-structure-ideal-product-iso`, in
`lean/Sheaf/AlgebraicGeometry/ClosedStructureIdealProductIso.lean`, carries the affine
quotient comparison for any single ideal. Its source is Tag 01QY and the affine
ideal-product calculation used in Tag 088A. Its normalized inclusion equation is what
combines the extension with the constructed ideal. No statement or definition changes
and no forced adaptations or change records are needed.

## Second reading by Q1

1. Interface preservation: PASS. Compared the main module with the repository using
   diff and checked the existing theorem signature byte for byte through `:= by`.
   The signature and all existing public imports are unchanged; no definition is
   changed. The existing node changes only proof, proof_deps, and proof_origin.
   There are no forced adaptations or statement changes.

2. Proof and kernel trust: PASS as a decomposition. Independently compiled all three
   delivered modules in import order through lcompile.py, with no errors or warnings.
   Searched every delivered Lean file for forbidden declarations and attributes.
   The main theorem contains no sorry; the only two remaining sorry tokens are the
   two named public bridge theorems listed above, each with a source and proof docstring.
   Scratch copies with #print axioms for all three declarations report exactly
   propext, Classical.choice, Quot.sound, and sorryAx. The last is expected from the
   two explicitly open bridge statements; this is not an axiom-free closure proof.
   No data definition is introduced: J is explicitly constructed as (I^n).comap i.
   The existential comparison is determined by its inclusion equation, and its
   witness is used only inside a proof, not to define arbitrary data.

3. Split statements: PASS. Read the actual sources at
   https://stacks.math.columbia.edu/tag/01YB,
   https://stacks.math.columbia.edu/tag/01QY, and
   https://stacks.math.columbia.edu/tag/01YE. The ambient extension is the extension
   step with coherent source i_*O_W (cyclic on affines) and coherent target; it makes
   no claim about an upstairs nonzero ideal. The comparison is the affine quotient
   identity followed by unique gluing inside i_*O_W, with no local-map or generic-point
   hypothesis. Neither merely renames the item's conclusion. Checked zero local map,
   empty U, empty W, unit and zero ideals, and n = 0: empty U gives the unique local
   map and a zero global map; n = 0 is the unit ideal; the comparison of the zero
   ideal and the empty subscheme gives zero modules on both sides. Empty W is excluded
   from the main theorem by integrality, as required for its generic point.
   Independent LeanFinder queries used quotient multiplication and clearing
   denominators terminology; Loogle searched IdealSheafData.comap, and msearch grep
   plus rg inspected the actual source library. The closest existing results are
   closedImmersion_pushforward_idealPowers, coherent_homs_over_open, the base-change
   ideal-image statements, and ClearDenominators. They have different interfaces or
   hypotheses; the first two also have the source-import cycles recorded above.
   No directly usable normalized bridge was found. Proving either bridge requires
   further affine-section normalization and transport, beyond a few-minute repair.

4. Route, imports, and pruning: PASS after correction. The main proof takes the
   direct support argument for nonzeroness, rather than generic-stalk calculations,
   and composes the two inclusion equations. New imports in the main module are
   proof-only. Bridge public imports supply notions occurring in their signatures;
   no proof-only public import was added. Checked all seven old direct dependencies
   against the No longer needed list and inspected the unit's realized record;
   no unit realization or route is bypassed. Removed the old ideal-powers theorem
   from the comparison bridge's plan: its affine quotient and product steps already
   prove equality of the two ranges, and the final unique gluing is elementary.
   This is pruning of a proof dependency; no original source import was removed,
   and no claim about whole-library reachability is made.

5. DAG consistency: PASS after correction. Every recorded Lean signature matches
   its module. Every proof_deps list equals the union of its proof steps' uses;
   all referenced nodes exist, and recursive proof-dependency checking found no
   cycle. Both new nodes contain source, proof_origin, search records, created,
   blueprint ancestry, chapter, unit, and Lean records. The main node records
   exactly the explicit vanishing ideal, support contradiction, and two bridges.
   The comparison node now records its actual affine/gluing plan without the
   redundant ideal-powers dependency.

Second-reading changes: removed
lem-weil-pbc-closed-immersion-pushforward-ideal-powers from the new comparison
node's proof_deps and final step's uses; marked that gluing step elementary;
corrected the corresponding No longer needed entry; appended this review.
No Lean proof or signature needed repair. Holes closed remain one of one in the
item, with two holes added: a decomposition with net minus one before closure
pruning, not an additional proof during this reading.
