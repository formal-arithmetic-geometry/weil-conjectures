## What changed

Proved `AlgebraicGeometry.derivedTensor_openRestriction_natIso` in
`Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionNatural`, preserving its signature,
universes and public imports. Added proof-only imports of KFlatDerivedTensorComparison,
KFlatBifunctorIsoDescent, OpenRestrictionKFlatModel, the source pullback monoidal structure,
and the source natural total-complex comparison. Added private local sheaf tensor instances
and fully proved private helpers `tensorModelComposition`,
`bifunctorModelNaturality`, and `tensorRestrictionIso`. This helper performs
bifunctor composition and naturality with abstract functors, avoiding expensive unfolding of concrete
localization constructions. The final proof composes natural comparisons on K-flat families,
uses simultaneous naturality to descend them, and proves naturality on the product category.
The DAG proof and dependency list now follow this argument.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.derivedTensor_openRestriction_natIso`
(node `lem-pc-derived-tensor-open-restriction-natural`). No holes remain in the delivered
module, and no holes or modules were added. This is a proof from existing declarations,
not a decomposition. Private helpers contain no sorry. Single-file `lcompile.py` validation passes without warnings
(35.4 seconds for the final proof). The existing dependency declarations
are used as supplied by the library; this delivery does not claim to discharge their entire
transitive axiom closure.

## No longer needed

Imports removed: none; both original public imports are needed by the statement.
The following planned direct dependencies and their proof imports are unnecessary for this
item and are not imported:

- `lem-pc-kflat-resolution`: `Sheaf.Algebra.Homology.KFlatResolution`. Resolution/localization
  work is encapsulated in the existing KFlatBifunctorIsoDescent theorem; it is not repeated here.
- `lem-pc-open-restriction-total-tensor`: `Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor`.
  Its objectwise comparison is replaced by the proved natural total-complex comparison.
- `lem-pc-open-restriction-tensor-natural`:
  `Sheaf.AlgebraicGeometry.OpenRestrictionTensorNaturality`. The strong monoidal structure
  of adjoint pullback supplies the natural tensor comparison directly.

These are deletions from this node's direct proof dependency list; other users and indirect
requirements of imported modules remain. No unit-level step is bypassed: the unit's realized
statement and step lists do not include this node or any of these helpers.

## Where the brief, the DAG or earlier work was wrong

The original plan had all necessary mathematics but its total-tensor lemma was only
objectwise. The source library already provides the natural comparison
`HomologicalComplex.mapBifunctorComparisonNatTrans`, invertible for strong monoidal
restriction preserving the coproducts of totalization. The existing K-flat bifunctor descent
lemma accepts an arbitrary target category, so independent localization universes require
no additional transport theorem. All constructions also apply to the empty open.

## Second reading by R3

1. **Interface unchanged — pass.** Read the complete repository and sandbox modules and
   compared them with `diff -u` and `stage3_delivery.diff_module`. The existing theorem's
   signature is byte for byte unchanged, including independent universes `w` and `wO`,
   both `HasDerivedCategory` hypotheses, arbitrary scheme and open, the canonical
   `schemeOpenRestriction`, and the product-category natural-isomorphism conclusion.
   Existing docstrings and both public imports are unchanged. No change record or
   forced adaptation is needed; all added declarations are private.
2. **Proof and axioms — pass.** Independently compiled the delivered file with
   `lcompile.py`: clean, 35.9 seconds. Compiled a scratch copy with `#print axioms`
   for the public theorem and all three private helpers: each uses only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx` (42.0 seconds).
   Scanned the delivered Lean for forbidden declarations and holes: none. The two
   private instances use actual library constructions. `tensorModelComposition`
   constructs its isomorphism by composing five supplied natural isomorphisms;
   `tensorRestrictionIso` constructs components and proves product naturality.
   No definition chooses arbitrary data from an unproved existence theorem.
3. **Split statements — pass, none.** There are no new public statements, split-off
   holes, or new nodes. Read the actual interfaces and proofs of
   `kFlat_derivedTensor_comparison_natIso`, `openRestriction_isKFlat`, and
   `kFlat_bifunctor_iso_descent`. The first comparison needs only its first input
   K-flat; restriction supplies exactly that condition on U. Descent accepts an
   arbitrary target category, so it does not equate the two localization universes.
   The empty open, zero inputs, and unbounded complexes impose no extra condition.
4. **Route and pruning — pass.** Read the source total-complex comparison and its
   invertibility instances in `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor`
   (comparison/naturality and instance code, lines 234–341), and the recorded
   `pullbackMonoidal` construction. The proof transports strong monoidality along
   the restriction/pullback isomorphism and supplies small-coproduct preservation;
   these discharge the totalization comparison's hypotheses. Read the same-universe
   `derivedTensor_openRestriction_iso` in `AffineDerivedPullbackTensorTilde`:
   it is not a direct specialization for independent `w` and `wO`. Additional `rg`
   searches in the upstream scheme modules and Mathlib localization files found no
   direct replacement. The private naturality helper composes the two naturality
   squares; the last helper factors tensor morphisms into the two whiskerings.
   Added imports serve these proofs and are plain imports; original public imports
   serve the statement. Compared all five old dependencies with the new route:
   the report's three unused dependencies are complete. Read
   `dag/units/sk-thm-picard-duality.json`: its `realized` statement is empty and
   its step list contains an empty list, so no realized unit step is bypassed or
   changed. The monoidal-pullback and total-comparison nodes from another unit
   are already proved tools, not a replacement of this unit's route.
5. **DAG agreement — repaired, pass.** Only `proof`, `proof_deps`, and `proof_origin`
   differ from the repository node. Steps 2 and 3 name exactly the K-flat comparison,
   restriction preservation, and bifunctor descent used by Lean. Step 1 initially
   failed to cite the existing node `lem-pc-total-bifunctor-comparison-iso`, despite
   using its source-library invertibility instance. Read that node's hypotheses
   against the source and the supplied additive, strong monoidal, coproduct-preserving
   restriction; added it to step 1's `uses` and to `proof_deps`. The resulting
   dependency list is exactly the union of the steps' uses. No new node is needed.

Second-reading changes: repaired the existing total-bifunctor comparison citation
in the DAG and appended this review. The Lean proof was correct and was left intact.
Holes closed: `AlgebraicGeometry.derivedTensor_openRestriction_natIso` (one of one).
Holes added: none; split off: none. All checked declarations have a closed axiom closure.
