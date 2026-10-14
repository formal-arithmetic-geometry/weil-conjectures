## What changed

Replaced the sorry in `AlgebraicGeometry.schemeMV_composition_left_normalization`
with a categorical combination of two intermediate statements. Its signature,
universes, hypotheses, visibility and original docstring are unchanged. Added two
proof-only imports, each for one new public theorem in its own module.

The first intermediate is the open-composition unit equation before either exact
restriction factor. The second is naturality of the derived composition along the
inverse exact X-restriction factor, before precomposing the h-localization unit.
The main proof postcomposes the unit equation, rewrites the restriction-factor
calculation and combines maps by functoriality and associativity.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.schemeMV_composition_left_normalization`
(one of one original holes).

Added and proved: `AlgebraicGeometry.schemeMVOpenComposition_restricted_source_unit`
(`lem-pc-mayer-vietoris-open-composition-restricted-source-unit`). The second reader
closed this intermediate by an exact application of the existing
`schemeMVOpenComposition_complex_localization` theorem to the termwise restriction.
The two source-complex presentations are definitionally equal.

Added and left: `AlgebraicGeometry.schemeMVOpenComposition_restriction_factors`
(`lem-pc-mayer-vietoris-open-composition-restriction-factors`).

This is a decomposition: one original hole closed and one strictly smaller hole
added, hence net zero holes removed. The remaining equation is the naturality
square for the canonical derived-composition comparison, precomposed with the
open-localization unit and postcomposed with the inverse restriction comparison.
It has no h-localization unit or complex-composition map. No definitions, target
statements, axioms or existence-selected data were added or changed.

## No longer needed

Removed the item's public import of
`Sheaf.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain`; replaced it
with `public import Sheaf.AlgebraicGeometry.MayerVietorisImageChainData`, which
supplies the definitions in its signature. The sole direct consumer,
`MayerVietorisImageCompositionLocalization`, already imports
`MayerVietorisRestrictionLocalizationChain` itself. The chain module remains in the
target import closure through other consumers; this is an import-edge pruning,
not removal of a whole module from the target closure.

Of the original proof dependencies:

- `def-pc-mayer-vietoris-restriction-localization-chain` is no longer used.
- `lem-pc-mayer-vietoris-open-composition-complex-localization` is no longer a
  direct dependency of the item, but remains required by the proved restricted-source
  intermediate and is not pruned from its transitive proof dependencies.
- `def-pc-derived-mayer-vietoris-canonical-data` and
  `def-pc-mayer-vietoris-image-chain-data` remain used.

## Where the brief, the DAG or earlier work was wrong

The first worker split source-identification and restriction-factor calculations
because combining the complex-unit theorem with naturality caused prolonged
definitional comparisons inside the derived functors. The second reader found
that the source-complex identification is definitionally equal: Lean accepts an
exact application of the existing complex-localization theorem, so that
intermediate now has a complete proof. Attempts to close the remaining naturality
equation ran into expensive instance conversions; its valid formal naturality
argument remains in the docstring and node.

A sandbox experiment normalizing the definition of schemeOpenModuleImageComplex
was discarded; that module is not part of this delivery. The final delivery changes
no existing definitions. The unit's realization and route are unchanged.

## New nodes

`lem-pc-mayer-vietoris-open-composition-restricted-source-unit` records source
identification followed by the existing complex-localization theorem. Its module is
MayerVietorisOpenCompositionRestrictedSourceUnit.

`lem-pc-mayer-vietoris-open-composition-restriction-factors` records the naturality
square of the canonical composition comparison along the inverse exact restriction
factor. Its module is MayerVietorisOpenCompositionRestrictionFactors.

Change record: `coord/changes/MayerVietorisCompositionLeftNormalizationImports.md`
records the public import pruning, old/new imports and every transitive user.
No existing statement or definition was changed.

## Second reading by N1

1. Compared the delivered existing module against the repository with `diff` and
   compared all three theorem signatures byte for byte with their node records.
   PASS: the existing declaration's signature, universes, hypotheses, visibility
   and original docstring are unchanged. No definition or target was changed.
   The import pruning is intentional and recorded above and in
   coord/changes/MayerVietorisCompositionLeftNormalizationImports.md. The change
   record lists all transitive users and explains why no adaptation is needed.
2. Read the complete proofs, checked for forbidden declarations and hollow data,
   and compiled the delivery in import order with `lcompile.py`. The item combines
   the two intermediate equations by postcomposition, functoriality and
   associativity. The restricted-source intermediate is now proved. The only
   direct sorry is the named restriction-factor theorem listed above; it has a
   complete proof in words and a matching node. Axiom checks allow only the three
   standard axioms and sorryAx inherited from open lower statements. Explicit
   `#print axioms` in a scratch copy confirmed only propext, Classical.choice and
   Quot.sound for the restricted-source theorem; the main theorem and remaining
   obligation additionally use sorryAx. All three modules compile without warnings.
3. PASS: the remaining lower statement is precisely the naturality square of the
   canonical beta along the inverse exact restriction factor. Its source is QJ
   and its target is derived restriction of QI, so the direction is correct.
   For zero complexes, empty/full opens and identity h, the same naturality
   identity applies without an additional hypothesis. It omits the item's
   h-localization unit and complex-composition map and is strictly a part of the
   original argument. Repeated searches used Loogle naturality_assoc, LeanFinder
   for prolongation of composite functors, and grep for complex-comparison and
   naturality equations, alongside local source searches. No public theorem
   states the remaining exact interface. A similar comparison expansion is a
   private helper in DerivedMayerVietorisOpenComparisonUnit and cannot be imported.
4. PASS: the top proof follows the existing complex-unit route and transports
   the restriction factor by naturality. The unnecessary chain import was
   pruned, and every old proof dependency is accounted for above. Inspected
   dag/units/sk-thm-picard-semicon.json: its realized statement and step lists
   are empty and unchanged; this supporting calculation replaces no unit step.
5. PASS: existing node changes are only proof, proof_deps and proof_origin.
   The dependency lists equal the union of the proof-step uses. Both new nodes
   have their source, complete statements, search records, creation fields,
   blueprint provenance, chapter/unit and verbatim Lean signatures. Updated
   the restricted-source node to describe the actual exact application.

Changed in the second reading: closed
`AlgebraicGeometry.schemeMVOpenComposition_restricted_source_unit`; corrected its
proof description and node; pruned the unnecessary restriction-chain import;
completed the old-dependency accounting and corrected the hole counts; added
the public-import change record required by preflight. The
restriction-factor theorem and the existing main proof were otherwise retained.
