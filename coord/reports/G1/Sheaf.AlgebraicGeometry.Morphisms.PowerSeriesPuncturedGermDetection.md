## What changed

Proved `AlgebraicGeometry.Scheme.eq_zero_of_powerSeries_punctured_germs` with its original
signature. Flat base change for the bottom quotient identifies every associated prime
of the power-series ring with an extended associated prime of A. The depth bound
excludes the maximal ideal; specialization transfers the given zero germ to the
associated point. Added two fully proved helper modules: `MvPowerSeriesPrimeExtension`
(finite-generator coefficient lifting) and `AssociatedGermDetection` (principal affine
cover, associated-prime localization, stalk maps and sheaf section extensionality).
All new imports in the item are proof-only. Updated the DAG proof to match the Lean.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.eq_zero_of_powerSeries_punctured_germs`.
The new theorems `MvPowerSeries.isPrime_map_C` and
`AlgebraicGeometry.Scheme.eq_zero_of_associated_germs` are fully proved.
No holes added or left in any delivered module; zero split off.
Existing dependencies are used through their recorded interfaces. The compiler probe
in the dry run checks their transitive axiom dependencies.

## No longer needed

Removed the item's direct imports of
`Sheaf.RingTheory.AnnihilatorAssociatedPrimesFlatBaseChange` and
`Sheaf.RingTheory.InjectivePiLocalizationAssociatedPrimes`.
The first is supplied through `QuotientAssociatedPrimesFlatBaseChange`, and the second
is used in `AssociatedGermDetection`; neither module is globally pruned.
The original associated-prime flat-base-change node is no longer a direct proof edge
of the item: the existing quotient specialization is the direct edge instead.
The power-series domain node is used by the new prime-extension node. The affine-stalk
localization and product-injection nodes are used by the new germ-detection node.
No original mathematical ingredient is abandoned, and no module is claimed globally
unreachable. The theorem's proof also works with d=0; the original hd binder is kept.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's coefficientwise prime-extension and affine
associated-germ steps had no directly usable combined interface. Both are now given
separate proved modules; the actual assembly follows the original argument.
Prime extension needs only the kernel equality and a domain target, so the planned
surjectivity and quotient equivalence construction are unnecessary.
The unit route and the original theorem signature stay unchanged.
Edge cases checked: zero rings have no prime-ideal witnesses, empty opens are handled
by section_ext, d=0 is allowed by the two helper proofs, and nilpotents are preserved
by associated-prime rather than reduced-point detection.

## New nodes

`lem-sbc-power-series-prime-extension` records `MvPowerSeries.isPrime_map_C` in
`Sheaf.RingTheory.MvPowerSeriesPrimeExtension`. It follows coefficient reduction and
finite-generation of the prime ideal; the direct proof adds no sorry.

`lem-sbc-open-section-associated-germ-detection` records
`AlgebraicGeometry.Scheme.eq_zero_of_associated_germs` in
`Sheaf.AlgebraicGeometry.Morphisms.AssociatedGermDetection`. It follows Tags 0310 and
0311 on principal affine opens, then sheaf section extensionality; no sorry remains.
No existing public interface changed, so there is no change record or forced adaptation.

## Earlier second reading (a previous round; superseded)

A second G1 reading is pending; the item and both new modules compile cleanly, preserve the original target signature, and leave no sorry.

## Second reading by G1

1. **Baseline and signatures.** Compared the delivered punctured-germ module with the repository version. The target theorem signature is byte-for-byte unchanged; the proof-only import changes are recorded in the existing report, and the two helper modules introduce only the declarations listed in the new DAG nodes.

2. **Compilation and axioms.** Compiled all three delivered modules with `lcompile.py --all`; all compile cleanly. The delivered declarations contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; `#print axioms` on all three public theorems shows exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

3. **Statement review.** Checked `MvPowerSeries.isPrime_map_C` by its coefficientwise quotient-kernel argument and `eq_zero_of_associated_germs` by affine principal-open localization and section extensionality. Both statements are true, strictly intermediate, and preserve the target's strength. No duplicate declaration was found in the repository. Independent LeanFinder search for injectivity of regular-function restriction to associated-point germs returned only integral/germ-injective criteria requiring stronger hypotheses; Loogle search `MvPowerSeries, Ideal.IsPrime` returned no hit. Checked d=0, empty opens, the zero ring, and the role of associated primes for nonreduced rings.

4. **Pruning and route.** The punctured-germ proof uses the quotient associated-prime base-change interface, prime extension, depth bound, and associated-germ detection. Removed direct imports of the older flat-base-change and injective-localization modules; the remaining imports are minimal for the written proof. The unit route and target statement remain unchanged. The existing unit record has empty `realized` lists; this delivery does not bypass any recorded unit realization.

5. **DAG and delivery metadata.** Verified that the item and both new node records match the declarations and proof route, including proof dependencies and origins. No statement or definition change record is required.

**Changes made during second reading:** none to the Lean proofs or DAG; added this review section only.
