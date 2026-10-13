## What changed

Replaced the sorry in `AlgebraicGeometry.relativeDifferentials_affine_sections_map_surjective`
without changing its signature. The proof constructs a linear transport from the affine chart
back to U, identifies its composite with the spectrum comparison with the supplied map using
`CommRingCat.KaehlerDifferential.ext`, and explicitly lifts every section through the two
isomorphisms. Added the proof-only import
`Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineChartDerivation`.

The new theorem fixes the chart comparison T by equality to the explicit restriction/congruence/
base-open composite and asserts only its action on universal differentials. The equality determines
T uniquely; no arbitrary object is selected from unproved mere existence. Returning the determined
T together with the identity avoids repeated kernel unfolding of the concrete composite in the
surjectivity proof. This is a decomposition, not a complete proof of the transitive closure.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.relativeDifferentials_affine_sections_map_surjective`
(node `lem-sc-relative-differentials-affine-sections-map-surjective`).

Added one hole, the only sorry in this delivery:
`AlgebraicGeometry.relativeDifferentials_affine_chart_derivation`
(node `lem-sc-relative-differentials-affine-chart-derivation`). It is strictly the derivation
compatibility step, with neither the supplied map e nor surjectivity in its statement.
Net holes closed minus holes added: zero; this delivery is a decomposition.
Both modules compile without warnings through lcompile.py (about 3 and 7 seconds).

## No longer needed

Removed the redundant direct proof import
`WeilConjectures.AlgebraicGeometry.Modules.Differentials` from the item; that module remains
needed through the existing public statement import and the new helper, so it is not pruned.
No existing DAG node or library module is pruned. The abandoned sandbox-only
`CanonicalSurj`/`canonical_surj` route and its proposed canonical-surjectivity node are not used.
The sandbox-only factorization theorem/module from the previous attempt is not delivered:
the factorization is now proved inside the item's proof from the narrower chart identity.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report described a canonical-surjectivity helper that was no longer present;
its node described chart compatibility while its Lean file stated whole-map factorization.
Reconciled the module, report and both DAG records. The original one-step DAG proof omitted
explicit chart derivation compatibility; that is now the one remaining intermediate statement.
No existing statement or definition was changed, and no forced adaptation is required.

The displayed composite causes expensive kernel unfolding if repeatedly substituted into section
maps. Keeping it as a variable with an explicit determining equality makes the proof compile
comfortably within the single-file limit; no limit was raised and no definition was changed.

Read Stacks Tags [01US](https://stacks.math.columbia.edu/tag/01US) and
[01UT](https://stacks.math.columbia.edu/tag/01UT): the route remains restriction to affine charts,
then the spectrum differential calculation. The unit record `sk-thm-picard-duality` has no bound
realized nodes here; no unit statement or proof step is bypassed.

## New nodes

`lem-sc-relative-differentials-affine-chart-derivation`, in
`dag/nodes/sec-picard-framework/lem-sc-relative-differentials-affine-chart-derivation.json`,
states compatibility of the explicit chart comparison with the universal derivation.
Its new module is `Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineChartDerivation`.
The docstring and node give the three calculations needed: base-open comparison,
equality transport, and source restriction. The statement works for arbitrary affine opens,
including empty opens, and arbitrary scheme morphisms; it assumes no smoothness, finiteness,
or nonemptiness. It uses only the existing isomorphisms, whose formulas apply in these cases.
Mathlib/blueprint searches found no duplicate chart-level compatibility declaration.
No change record is needed.

## Second reading by S2

1. Compared the delivered item module against the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; the only interface addition is the explicitly documented split-off helper node and module. No target statement or definition changed.

2. Compiled both delivered modules with `lcompile.py --all`; they compile without errors or warnings. The item theorem has no `sorry`; the sole remaining `sorry` is the named helper theorem, with a docstring, DAG node, and source. No forbidden declarations or hollow definitions occur. Scratch `#print axioms` checks for both delivered declarations returned exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the helper is intentionally open.

3. Checked the helper statement on arbitrary affine opens, including empty opens: it asserts only the determined composite isomorphism and its action on universal differentials, with no extra hypotheses or surjectivity. The statement is strictly smaller than the item and is not a restatement. Independent LeanFinder search for universal-derivation compatibility of chart isomorphisms returned generic presheaf universal-property lemmas; Loogle search for `relativeDifferentialsToRestrict` returned no match; grep and repository scans found no existing duplicate chart declaration. Read Stacks Tags 01US and 01UT online because the cited local source is absent: 01US preserves the derivation under open restriction, and 01UT reduces the affine calculation by that compatibility, exactly the route taken here.

4. Reviewed the proof route from the target downward. It uses the affine chart comparison, spectrum section isomorphisms, restriction transport, and `KaehlerDifferential.ext`; the unit route through affine restriction and the spectrum differential calculation is retained. The redundant direct proof import of `WeilConjectures.AlgebraicGeometry.Modules.Differentials` was removed because the new helper supplies it transitively; no other imports or nodes can be pruned.

5. Compared the Lean proof with both DAG records. The item node lists the helper and the differential constructions actually used; the helper node records the exact split statement, source, proof plan, Lean declaration, and `split` status. The report's closed and added holes agree with the files: one target hole closed and one strictly simpler helper hole added, hence a decomposition with net zero.

Changed only the report by adding this second-reading audit; no proof or statement repairs were needed.
