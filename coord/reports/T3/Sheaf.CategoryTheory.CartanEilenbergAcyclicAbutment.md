## What changed

Replaced the sole hole in `Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment`
without changing its statement. Its proof combines the normalized augmentation
comparison, the canonical natural image filtration, and the second-image comparison.
Only proof imports were changed in the existing module.

Added four modules, each with its own node:

- `CartanEilenbergAcyclicAugmentation`: states the natural augmentation into degree-zero
  total summands and its quasi-isomorphism property.
- `CartanEilenbergAugmentationComparison`: proves the total-cohomology comparison from
  that quasi-isomorphism by explicitly inverting its homology map, then composing
  with extension homology and the canonical injective-resolution computation.
  Naturality is proved by cancelling the augmentation homology map and using the
  two existing naturality lemmas.
- `GrothendieckCanonicalImageFiltration`: fully proves an explicit construction of
  the canonical filtration, its antitonicity, its naturality, and the stable-page
  identification at every integer r satisfying the requested bound. The proof uses
  existing spectral-object page, outer-index replacement, and successive-image
  cokernel computations, rather than another convergence hypothesis.
- `CartanEilenbergSecondImageTruncation`: states precisely the filtered comparison
  needed to identify the mapped second-filtered-total images with canonical steps,
  for all integer filtration indices.

All five modules compile together in dependency order with no warnings. Multiple
single-file iterations checked the naturality square, integer indexing, dependent
subobject equalities, and quotient transport. Every private helper is proved.
No definition contains a hole. The original signature is unchanged.

The only existentially selected complex maps are the augmentation maps in
`exists_cartanEilenberg_acyclic_augmentation`. Their prescribed nonnegative
components determine them uniquely: their extended source is zero in negative
degrees. Thus the inverse-homology construction uses determined data, rather than
an arbitrary witness of existence. The canonical filtration itself is constructed
as a concrete `let`-bound structure using `Subobject.exists`.

## Proved and sorry left

Closed the original hole:

- `CategoryTheory.exists_cartanEilenberg_acyclic_abutment`
  (`lem-sp-ce-acyclic-abutment`). This is a decomposition, not a proof independent
  of new holes: one original hole is closed and two strictly smaller holes are added.

Fully proved the new intermediate results:

- `CategoryTheory.exists_cartanEilenberg_augmentation_comparison`
  (`lem-sp-ce-augmentation-comparison`).
- `CategoryTheory.exists_grothendieck_canonical_image_filtration`
  (`lem-sp-grothendieck-canonical-image-filtration`).

Exactly two sorries remain in the delivery, each the whole proof of a public theorem
in its own module, with a source and complete proof in words:

- `CategoryTheory.exists_cartanEilenberg_acyclic_augmentation`
  (`lem-sp-ce-acyclic-augmentation`): constructing the normalized natural complex
  augmentation and proving it is a quasi-isomorphism by acyclic columns.
- `CategoryTheory.cartanEilenberg_second_image_eq_truncation`
  (`lem-sp-ce-second-image-truncation`): the filtered Dec/truncation comparison.

No sorry remains in the original module. The net local hole change is -1 (one
closed minus two added); the delivery supplies a reduction and two actual proved
intermediate results, not a claim of net hole progress.

Edge cases checked in the statements and proof: zero objects; total degree zero;
negative filtration indices (whole complex and whole canonical image); p>n (zero
image); r=2 when allowed by the bound; and arbitrary objectwise comparisons c_X.
Naturality of c is never assumed or used.

## No longer needed

Removed the original module's direct proof imports:

- `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`: the row-collapse node
  `lem-weil-pbc-first-quadrant-row-collapse` is unnecessary on this proof route.
  The augmentation comparison follows directly from a quasi-isomorphism; the
  lower augmentation node uses the acyclic-cone column argument.
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`: its old direct proof
  import is unnecessary for the assembly and the proved canonical filtration.
  The double-complex spectral-sequence theorem remains part of the natural-language
  plan of the lower augmentation node; it is not claimed mathematically pruned.
- `Sheaf.CategoryTheory.DoubleComplexTotal` and `Sheaf.CategoryTheory.Filtration`:
  redundant direct proof imports removed. Their definitions are still needed by
  the unchanged statement and are available through public statement imports;
  their nodes and modules are not claimed pruned.

The remaining old direct proof dependencies, `lem-sp-derived-well-defined` and
`def-sp-composite-acyclicity`, moved below the comparison reductions rather than
being mathematically pruned. `def-sp-cartan-eilenberg-presentation`,
`def-sp-double-complex-total`, and `def-sp-filtration` remain required by the
statements and lower proofs. Thus every old proof dependency is accounted for.

No exact-couple convergence, filtered homotopy, or comparison-independence module
was added for stable-page computation. The unit record has no realized node for
this item, and its statement and steps are untouched.

## Where the brief, the DAG or earlier work was wrong

The planned row-collapse application is not supplied with the convergence data
its Lean statement requires. It therefore cannot by itself establish that the
augmentation is a quasi-isomorphism. The reduction makes that precise missing
step an independent item and proves the inverse-homology construction and its
naturality in Lean.

The DAG's stable-page step did not identify its exact interfaces. The existing
`spectralSequencePageXIso`, `isoMapFourδ₁Toδ₀'`, `isoMapFourδ₄Toδ₃'`, and
`nonempty_cokernel_ofLE_imageFiltration_iso` suffice; this portion is fully proved.
The original statement is not disputed and no statement or definition was changed.

The blueprint-ancestor script follows `created.item` as a node id, but the earlier
stage-3 node records a module name there, so it returned no ancestor. The delivered
new nodes instead follow the original node's explicit blueprint link to
`thm-sp-grothendieck`, with `lem-sp-ce-acyclic-abutment` in `via`. Blueprint searches
for Cartan--Eilenberg augmentation and canonical image filtration found no duplicate.
LeanSearch returned an HTTP service error; the actual unavailable result is recorded.

## New nodes

`lem-sp-ce-acyclic-augmentation`, in
`Sheaf.CategoryTheory.CartanEilenbergAcyclicAugmentation`, is the complex-level
acyclicity and naturality part of the original proof, with no spectral-sequence
or filtration data as inputs.

`lem-sp-ce-augmentation-comparison`, in
`Sheaf.CategoryTheory.CartanEilenbergAugmentationComparison`, is proved from the
complex-level augmentation and the standard injective-resolution computation.

`lem-sp-ce-second-image-truncation`, in
`Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation`, is only the equality
of filtered images, conditional on augmentation normalization. It does not
assert existence of the total comparison or stable-page identifications.

`lem-sp-grothendieck-canonical-image-filtration`, in
`Sheaf.CategoryTheory.GrothendieckCanonicalImageFiltration`, is fully proved and
uses no Cartan--Eilenberg presentation or second-filtered-complex comparison.
It constructs the canonical filtration and proves its naturality and stable pages.

The original node's proof, proof dependencies and proof origin now match the Lean
assembly. No change record is required: no existing interface was altered.

## Second reading by T3

1. **No accidental visible changes.** Compared the delivered abutment module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; the only existing-module changes are proof imports and the proof body. The four additional modules are new split-off declarations recorded by matching DAG nodes.

2. **Proof and trust basis.** Compiled all five modules with `lcompile.py --all`; they compile without errors or warnings. No `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definition occurs. The only remaining `sorry`s are the two named public split-off theorems `exists_cartanEilenberg_acyclic_augmentation` and `cartanEilenberg_second_image_eq_truncation`; both have source-backed proof docstrings and matching nodes. The two completed intermediate theorems contain no `sorry`. Explicit `#print axioms` checks show only `propext`, `Classical.choice`, and `Quot.sound` for the canonical filtration, and additionally `sorryAx` for the abutment, augmentation comparison, and second-image theorem, as expected from the two open lower statements.

3. **Statements and split nodes.** Checked the new declarations against the original proof route and their node records. The augmentation theorem isolates the acyclic-column quasi-isomorphism, the second-image theorem isolates the filtered comparison, and the two proved theorems are strictly stronger reductions used by the abutment assembly. Their edge cases and normalization hypotheses match the use sites. Independent LeanFinder search for “bicomplex resolution augmentation totalization is quasi-isomorphism when vertical cohomology vanishes”, Loogle search for homology maps, and `rg` inspection of the CE and total-complex modules found no applicable existing theorem closing these holes. The existing total-resolution theorem concerns a flipped unmapped total with injective terms, so does not supply the G-acyclic mapped-column statement. Checked Stacks [015N](https://stacks.math.columbia.edu/tag/015N) and [015X](https://stacks.math.columbia.edu/tag/015X): they support the CE computation and filtered comparison described here.

4. **Pruning and imports.** The abutment proof no longer uses the direct row-collapse, total-complex, double-complex-total, or filtration proof imports; those were removed as proof-only imports and are listed in `## No longer needed`. The replacement imports are exactly the three comparison/filtration modules used by the proof. The original node proof and proof dependencies were updated to follow the actual assembly. No unit statement or realized route is changed; this item has no realized unit node.

5. **DAG agreement and review verdict.** The Lean declarations, node statements, proof steps, proof dependencies, origins, and module paths agree. The abutment hole is closed by a valid decomposition into two lower holes plus two proved reductions; no target statement is weakened. Verdict: suitable for delivery.

Changed during this second reading: no Lean statements or proofs; the review section, axiom-check results, independent-search results, and the accounting of all old proof dependencies were added to the report.
