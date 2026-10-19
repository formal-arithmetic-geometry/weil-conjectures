# Stage-1 report: lem-trf-generic-cm-locus-field

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-cm-locus-field.json`: repaired split statement and proof.
- `dag/nodes/sec-trace-formula/lem-trf-minimal-primes-dense-spectrum.json`: retained prerequisite with repaired immediate-parent ancestry; statement-only, no Mathlib exact match.
- `citations.json`: verbatim citations for every proof-step use.

## Attachments

None.

## WANTED

None.

## What was wrong or corrected

The returned review correctly identified that the earlier Step 2 inferred a zero maximal ideal from dimension zero; the ring $k[\\varepsilon]/(\\varepsilon^2)$ is a counterexample. I replaced that inference with the valid argument using prime correspondence for localization, the existing theorem that minimal primes of a Noetherian ring are associated, and the existing depth upper bound for an associated prime. The empty regular sequence supplies the lower bound, so depth and dimension are both zero while nilpotents may remain.

The added `lem-trf-finite-type-cm-locus-open` node was removed because it duplicated the existing general theorem `lem-sbc-fibre-cohen-macaulay-locus-open`. The item now applies that general flat locally finitely presented fibre-locus theorem to $\\operatorname{Spec}A\\to\\operatorname{Spec}k$, and separately cites the existing finite-type and localization Noetherian leaves to identify its locus with the stated Cohen–Macaulay locus. Both created ancestry chains now begin with the immediate parent item, as required by B9.

## Review by Q90

I reread the item against Stacks Project `literature/stacks-project/algebra.tex`, Tags 00RF and 00RG, and reread the retained density prerequisite against the final minimal-prime sentence of Tag 00RG. I also opened the existing general openness node `lem-sbc-fibre-cohen-macaulay-locus-open`, the finite-type Noetherian and localization-Noetherian leaves, the prime-localization correspondence, the minimal-prime-associated theorem, the associated-prime depth bound, and the depth, finite-module and Krull-dimension definitions. Their statements provide exactly the clauses quoted in `citations.json`.

Step 1 checks the hypotheses of the general fibre-locus theorem: a finite type algebra over a field is flat as a vector-space module, and finite presentation is supplied by the existing Mathlib leaf `lem-weil-pbc-finite-type-noetherian-finite-presentation` (Stacks Tag 00FP), after verifying directly that the only ideals of the field are $(0)$ and $(1)$; finite-type Noetherianity and localization Noetherianity then verify that the depth-equals-dimension locus is exactly the Cohen–Macaulay locus. Step 2 uses the prime-localization bijection and minimality to get a unique prime and dimension zero, then applies the associated-minimal-prime statement to that unique prime and the depth upper bound to get depth at most zero; the depth definition gives the opposite inequality. I explicitly checked the nonreduced edge case $k[\\varepsilon]/(\\varepsilon^2)$ and the reduced field case, so the repaired argument does not silently assume reducedness or a zero maximal ideal. Step 3 applies the retained minimal-prime density statement and the openness from Step 1.

The retained density node is distinct from `lem-pc-dense-range-comap-minimal-primes`: the latter characterizes dense range of a spectrum contraction map, while the new node asserts density of minimal-prime points in one finite-type spectrum. It is also distinct from the parent `lem-trf-flat-lfp-cm-locus-fibre-dense`: the parent is a fibrewise geometric statement whose proof uses the present field-algebra result, whereas the retained node is the ring-theoretic minimal-prime density input. The removed openness node has no remaining citation or file.

## Not duplicates

`lem-trf-minimal-primes-dense-spectrum` vs `lem-trf-generic-cm-locus-field`: the retained node only states density of minimal-prime points; the item additionally proves openness and that those points have Cohen–Macaulay localizations.

`lem-trf-minimal-primes-dense-spectrum` vs `lem-trf-flat-lfp-cm-locus-fibre-dense`: the retained node is a ring-spectrum minimal-prime density statement; the existing parent is density of Cohen–Macaulay points in every fibre of a flat locally finitely presented morphism and uses the item.

`lem-trf-minimal-primes-dense-spectrum` vs `lem-pc-dense-range-comap-minimal-primes`: the retained node directly asserts density of minimal-prime points in one spectrum; the existing Mathlib leaf characterizes when the contraction map on spectra has dense range.


## Repair of the C4/C1 return at c3111f998c

The retained item was compared with the current shared node: the current node is still unsplit, and its statement, chapter, unit and ancestry agree with the retained split. The initial dry run of the retained split passed at `13e435a58e`; that mechanical success did not resolve the citation gap in the return. This repair changes Step 1, its uses and proof_deps, and citations.json, rather than resubmitting that unchanged proof.

I opened the statement of `lem-weil-pbc-finite-type-noetherian-finite-presentation` and read its source in `literature/stacks-project/algebra.tex`, Tag 00FP, label `lemma-Noetherian-finite-type-is-finite-presentation`. It states exactly that a finite type algebra over a Noetherian ring is finitely presented. I also read `Algebra.FinitePresentation.of_finiteType` at lines 69–74 of `Mathlib/RingTheory/FinitePresentation.lean`: its forward direction proves that same implication using the finite polynomial presentation and the Noetherian kernel. Step 1 now applies that cited statement with $R=k$ and $S=A$. The base hypothesis holds because a field has only the two finitely generated ideals $(0)$ and $(1)$; the finite-type hypothesis is the item's hypothesis. The cited node is already a Mathlib leaf and needs no new node or off-route tool declaration. Its full statement was copied verbatim into citations.json, and proof_deps is the union of the repaired steps' uses.

I reread every other step's cited statements and kept the accepted minimal-prime and depth argument. For the zero algebra the spectrum and the locus are both empty, so openness and density hold in the empty space and Step 2 has no prime to choose. For $A=k$ the sole localization is a dimension-zero field. For $A=k[\varepsilon]/(\varepsilon^2)$ the localization still has depth and dimension zero, with a nonzero maximal ideal allowed. These also test the field specialization of the newly cited finite-presentation theorem. No proof step exceeds 2000 characters. No new node or new Mathlib-search claim was introduced in this repair; the retained search records and density prerequisite are preserved.

## Unfinished

No stage-1 proof obligations remain. The retained minimal-prime density prerequisite is intentionally statement-only and joins the queue for a later split.
