## What changed

The signature and visibility of
`AlgebraicGeometry.perfectImmersion_tensor_acrossUniverses` are unchanged. Its proof now
applies the existing `smooth_proper_diagonal_tensor_formula` in the standard localization,
extracts and inverts its invertible adjunction mate in the full QCoh category, and transports
that isomorphism back. The proof explicitly identifies the supplied OP using hOP, maps this
comparison through the right adjoint, and composes the tensor-factor isomorphisms. The private
`standardUnitComparison` is proved directly by the Qh localization comparison at the single
structure module; its result does not rely on a new hole.

Added `DerivedQCohStandardAdjunction.lean`, with a complete proof of
`AlgebraicGeometry.derivedQCoh_standardAdjunction`. Its private helpers compare Q, compare
homology, restrict the ambient equivalence to QCoh, and compare direct images using the
existing `RingedSpace.derivedModuleDirectImageFactorization`. Conjugating the supplied
adjunction constructs its standard right adjoint as an explicit composite of proved
restricted equivalences and c. No data is defined using a sorried existence theorem.

Added two strictly smaller comparison statements, each in its own module:
`DerivedLocalizationTensorComparison.lean` and `PerfectImmersionStandardPerfection.lean`.
The first concerns tensor compatibility on one arbitrary scheme, with no immersion, right
adjoint or perfection hypothesis. The second concerns only standard-model perfection of
Ri_* of the unit, with no c, OP, K, or tensor-formula conclusion. The original theorem uses
both together with the existing tensor formula; neither restates the original theorem.

The item's node now follows this proof and cites three new nodes. All new modules retain
`module`, the standard public-section header, explicit binders and the existing tensor and
derived-category definitions. No existing definition or statement was changed and no
other held module was adapted.

## Proved and sorry left

Closed the original module's one hole:
`AlgebraicGeometry.perfectImmersion_tensor_acrossUniverses`
(node `lem-sc-perfect-immersion-tensor-across-universes`). The item's module has no sorry left.

The new theorem `AlgebraicGeometry.derivedQCoh_standardAdjunction`
(node `lem-pc-derived-qcoh-standard-adjunction`) is proved, as are all its private helpers.
Its proof depends on the existing named direct-image factorization theorem; it is not a
claim that the entire transitive dependency closure is sorry-free.

Added exactly two holes, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.derivedLocalization_tensorComparison`
  (node `lem-pc-derived-localization-tensor-comparison`).
- `AlgebraicGeometry.perfectImmersion_standardPerfection`
  (node `lem-sc-perfect-immersion-standard-perfection`).

Thus the delivery is a decomposition of one upper hole into two lower holes, with additional
proved localization/adjunction glue. The net hole change in this set is +1; it is not a
net-hole reduction or a proof of the full dependency closure. Existing imported holes,
including `RingedSpace.derivedModuleDirectImageFactorization`, are unchanged.

Each remaining statement has a complete source-based proof in words in its docstring and
node. Edge cases were checked mathematically: the tensor comparison is valid for all
unbounded standard objects without QCoh hypotheses, and for identity localization and the
empty scheme; the perfection comparison applies to identity and empty closed immersions
without assuming properness or Noetherianity. The main theorem retains its original proper
and Noetherian hypotheses for the existing common-universe tensor formula.

Validation: all four delivery modules compiled locally together in import order. The
required delivery dry run is the final validation; nothing is pushed by this worker.

## No longer needed

Removed the redundant proof-only direct import
`Sheaf.AlgebraicGeometry.DerivedCategory` from the item's module. Its definitions remain
required by the unchanged statements and are supplied by the retained public imports.
This is removal of a redundant direct import, not pruning the module from target reach.

No original proof-dependency node or transitive module is bypassed. In particular the
existing `lem-sc-smooth-proper-diagonal-tensor-formula` and its proof route remain used.
The item is not listed in its unit's `realized` fields; the unit statement and route stay
unchanged. No globally unnecessary module is claimed.

## Where the brief, the DAG or earlier work was wrong

The original first step bundled tensor comparison, homology/QCoh restriction,
direct-image comparison, adjunction conjugation, and local perfection comparison into prose,
without declarations giving these comparisons. The new proof makes their interfaces
explicit. The QCoh/adjunction part is now proved using the existing direct-image
factorization; the two remaining comparison parts are new standalone items.

The original wording suggests invoking uniqueness of right adjoints after conjugation.
The implemented route instead constructs the conjugated right adjoint and applies the
existing tensor formula, which quantifies over any specified right adjoint. The differing
QCoh-preservation witnesses are proof-irrelevant and need no extra adapter theorem.

Searches used LeanSearch (unavailable: Internal Server Error), Lean Finder, Loogle and grep
through msearch, followed by direct searches of
both library roots, the DAG, and Mathlib localization/full-subcategory APIs. No exact
comparison statement was found. Generic localization and equivalence APIs were used.
The Stacks source tags were read online. An exploratory tensor proof via uncurried Kan
extensions was not retained: its large functor-comparison elaboration exceeded the single
file time limit. The submitted tensor statement contains only its named hole and complete
proof in words, and introduces no slow construction or alternate tensor definition.

## New nodes

`lem-pc-derived-localization-tensor-comparison`, module
`Sheaf.AlgebraicGeometry.DerivedLocalizationTensorComparison`: transport of the fixed
K-flat tensor through the inverse standard localization comparison. This is one remaining
hole, general on one scheme and independent of the duality argument.

`lem-pc-derived-qcoh-standard-adjunction`, module
`Sheaf.AlgebraicGeometry.DerivedQCohStandardAdjunction`: fully proved transport of a
specified restricted direct-image adjunction, with natural comparisons on all objects.
It uses the existing ringed-space direct-image factorization node as a generic tool; it
does not change the unit's mathematical route.

`lem-sc-perfect-immersion-standard-perfection`, module
`Sheaf.AlgebraicGeometry.PerfectImmersionStandardPerfection`: the remaining geometric
comparison of local perfection and exact closed-immersion pushforward of the tensor unit.
Its proposed proof uses the existing proved closed-pushforward stalk computation as a
generic tool. No change records are needed because all existing interfaces are unchanged.

## Second reading by Q2

1. **Visible changes and interfaces.** I diffed the delivered target module against the repository version. The target theorem signature and all existing declaration signatures are byte-for-byte unchanged; the added modules and node files are new declarations only. Verdict: pass.
2. **Compilation and proof hygiene.** I compiled all four delivered modules together with `lcompile.py --all`; they compile without errors. The target and the adjunction theorem contain no `sorry`; the two explicitly split comparison theorems contain exactly their named `:= by sorry` proofs. No definitions contain `sorry`, and no forbidden declarations occur. Verdict: pass.
3. **New statements.** I checked the two split statements against their hypotheses and conclusions, including identity and empty-scheme cases, and searched the repository for duplicate declarations. They are strictly smaller than the target: one is tensor transport for arbitrary standard objects, and one is standard-model perfection of a closed-immersion unit pushforward. The adjunction statement is proved and isolates only localization/adjunction transport. Verdict: pass.
4. **Route and pruning.** The target proof follows the standard localization route through the existing smooth-proper tensor formula, the new adjunction and perfection comparisons, and tensor transport. The removed direct `DerivedCategory` import is redundant; no original proof-dependency node is bypassed. The unit record is unchanged and has no realized route to alter. Verdict: pass.
5. **DAG agreement.** I compared theorem signatures, imports, and proof steps with the four node records. The target node records the three comparison dependencies; the new nodes record their modules, declarations, sources, proof text, and split status. Verdict: pass.

I changed only this second-reading report section; no Lean source, statement, definition, or node was altered during review.
