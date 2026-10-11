Files written:

- lem-sp-ce-vertical-nullhomotopy.json: item, split with three proof steps.
- lem-sp-ce-row-comparison-nullhomotopy.json: merged Mathlib leaf, attached to `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`.
- lem-sp-ce-compatible-homotopy-assembly.json: corrected augmented assembly statement, Mathlib no-match.
- citations.json: verbatim quotes for every cited proof step.

Attachments:

- `CategoryTheory.InjectiveResolution.descHomotopyZero` belongs to `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` via the augmented-complex specialization.

WANTED:

- None. The cited Stacks source and Weibel reference are available in the imported literature metadata.

What was wrong or incomplete:

- The returned assembly statement was false: it lacked exact augmented source sequences and the condition that the middle map vanish on the augmentation. I repaired it by introducing the augmented short exact sequence, compatible augmentations, and `R_I epsilon_I = 0`; its horizontal clause now states the required restriction on the boundary inclusion.
- The returned item proof did not use the `B_I^p -> Z_I^p -> H_I^p` sequence or explain horizontal compatibility. I rewrote it as an induction: assemble `h_Z^p` from `h_B^p` and `h_H^p`, then assemble `s_2^p` and the next `h_B^{p+1}` from the `Z_I^p -> I^p -> B_I^{p+1}` sequence.
- The old row-comparison helper is a special case of `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` after adjoining degree `-1`; it is marked merged and removed from the item dependencies.

What I could not finish:

- No Lean implementation was attempted, as required for stage 1.

## Review by M1

I read the item source in `literature/stacks-project/derived.tex`, Tag 015I, and the cited Weibel 5.7.10 construction. I checked the parent Cartan-Eilenberg node for both exact sequences `B -> Z -> H` and `Z -> I -> B`. Step 1 uses that node for the induced maps and exactness. Step 2 cites the existing acyclic-to-injective statement verbatim and verifies the degree `-1` augmentation construction, so the row maps vanish on augmentations and the homotopies have zero degree-zero component. Step 3 cites the corrected assembly statement verbatim: its hypotheses include the augmented short exact sequence, compatible augmentations, and `R_I epsilon_I = 0`; its conclusion supplies both the middle homotopy and the next boundary homotopy. I checked the induction invariant `h_Z^{p+1}|_{B^{p+1}} = h_B^{p+1}`, which is exactly what makes `s_2 d_h = d_h s_2`. I also checked the zero and one-row cases. The row-comparison helper was compared against the existing Mathlib-backed node and marked merged. LeanFinder, Loogle, grep, and LeanSearch searches were rerun for the corrected assembly statement; LeanSearch was unavailable and is recorded as such.

## Not duplicates

lem-sp-ce-row-comparison-nullhomotopy vs lem-sp-ce-vertical-nullhomotopy: the helper treats one augmented exact row and one map; the item treats three rows of a double complex and assembles them.
lem-sp-ce-row-comparison-nullhomotopy vs lem-sp-cartan-eilenberg-properties: the helper proves null-homotopy of a zero-on-augmentation map; the existing node states Cartan-Eilenberg exactness and injectivity properties.
lem-sp-ce-row-comparison-nullhomotopy vs lem-sp-cartan-eilenberg-exists: the helper compares a given exact row map; the existing node constructs a Cartan-Eilenberg resolution.
lem-sp-ce-row-comparison-nullhomotopy vs lem-sp-cart-eilenberg-left-exact-cohomology: the helper gives a null-homotopy; the existing node compares horizontal cohomology under a left exact functor.
lem-sp-ce-row-comparison-nullhomotopy vs lem-sp-ce-horizontal-lift: the helper handles a vertical row map from an exact source; the existing node lifts horizontally across a double complex.
lem-sp-ce-row-comparison-nullhomotopy vs lem-sp-cartan-eilenberg-comparison-homotopy: the helper is only the vertical row comparison input; the existing node states the full filtered total-complex comparison homotopy.
lem-sp-ce-row-comparison-nullhomotopy vs lem-sp-cartan-eilenberg-double-complex-homotopy: the helper is a single-row ingredient; the existing node assembles horizontal and vertical components.
lem-sp-ce-row-comparison-nullhomotopy vs lem-weil-pbc-cartesian-eilenberg-functorial: the helper gives a null-homotopy; the existing node constructs a functorial double-complex morphism.
lem-sp-ce-row-comparison-nullhomotopy vs lem-weil-pbc-horseshoe-morphism-lift-exact-source: the helper gives homotopies of exact-to-injective row maps; the existing node lifts morphisms between short exact sequences.
lem-sp-ce-compatible-homotopy-assembly vs lem-sp-ce-vertical-nullhomotopy: the helper assembles across one short exact sequence; the item applies this to all boundary-cycle rows of a double complex.
lem-sp-ce-compatible-homotopy-assembly vs lem-sp-cartan-eilenberg-properties: the helper assembles prescribed homotopies; the existing node only states row exactness and injectivity.
lem-sp-ce-compatible-homotopy-assembly vs lem-sp-cart-eilenberg-left-exact-cohomology: the helper is a short-exact homotopy construction; the existing node is a cohomology comparison.
lem-sp-ce-compatible-homotopy-assembly vs lem-sp-cartan-eilenberg-exists: the helper assumes resolutions and assembles maps; the existing node constructs resolutions.
lem-sp-ce-compatible-homotopy-assembly vs lem-sp-ce-horizontal-lift: the helper assembles vertical homotopies; the existing node constructs horizontal comparison lifts.
lem-sp-ce-compatible-homotopy-assembly vs lem-sp-cartan-eilenberg-comparison-homotopy: the helper handles one exact sequence; the existing node includes the full double-complex and filtration conclusion.
lem-sp-ce-compatible-homotopy-assembly vs lem-sp-cartan-eilenberg-double-complex-homotopy: the helper is the assembly ingredient; the existing node states the completed total homotopy.
lem-sp-ce-compatible-homotopy-assembly vs lem-weil-pbc-cartesian-eilenberg-functorial: the helper assembles homotopies; the existing node constructs a functorial double-complex morphism.
lem-sp-ce-compatible-homotopy-assembly vs lem-weil-pbc-horseshoe-morphism-lift-exact-source: the helper assembles null-homotopies with a commuting differential; the existing node lifts a map of short exact sequences.

## Second reading by M1

I reread Tag 015I (definition-cartan-eilenberg and lemma-cartan-eilenberg) and the Weibel 5.7.10 reference named by the split. Step 1 was checked against the item hypotheses and is elementary: restriction to kernels, images, and quotients follows from commutation with the horizontal differential; its unsupported citation was removed. Step 2 was checked against the exact-source/injective-target statement of `lem-sp-ce-row-comparison-nullhomotopy`, including the zero augmentation and degree-zero homotopy. Step 3 was checked against the repaired assembly statement, including restriction, quotient, homotopy identity, and horizontal commutation. The item is strictly more general than either helper, so neither helper restates an item clause. Both new helpers remain statement-only and retain recorded searches.

## Second reading by M1

- Step 1 checked against Tag 015I's boundary/cycle/cohomology row construction and `lem-sp-cartan-eilenberg-exists`; verdict: induced row maps and exact sequences match the hypotheses.
- Step 2 checked against `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` and the exact-source specialization; verdict: the augmented row maps vanish and the homotopies are degree-zero zero.
- Step 3 checked against the assembly statement and the two displayed short exact sequences; verdict: induction and horizontal compatibility are stated explicitly.
- `lem-sp-ce-compatible-homotopy-assembly` checked for B1-B7 and small zero/one-row cases; verdict: self-contained unsplit statement, with exact augmented complexes and structure-map hypotheses.
- `lem-sp-ce-row-comparison-nullhomotopy` checked against Mathlib KInjective declarations; verdict: converted to a Mathlib leaf using `CochainComplex.isKInjective_of_injective` and `CochainComplex.IsKInjective.nonempty_homotopy_zero` at verified lines 133 and 43.

Changes: repaired the assembly statement's missing exactness and undefined indexed clause; made the item induction's augmentation and boundary compatibility explicit; converted the row-comparison helper to a Mathlib leaf and updated its status/search metadata.

Changes made: removed the step-1 citation to `lem-sp-cartan-eilenberg-exists` because that node does not state the short exact boundary/cycle sequences used there; marked the resulting diagram chase elementary; rewrote the assembly helper to introduce its injection, quotient, outer maps, homotopy equations, and horizontal-commutation hypotheses explicitly; updated `citations.json` to quote the repaired helper statement. The sandbox copy of the item also had an incorrect worker `created.item` value, but that maintainer-owned field is preserved from the repository during delivery.
