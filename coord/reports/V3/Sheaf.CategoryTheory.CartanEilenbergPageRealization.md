## What changed

Added a real assembly proof in `CartanEilenbergPageRealization`. Added two strictly smaller intermediate statements: functorial page-two realization of spectral objects and the filtered Cartan–Eilenberg/truncation comparison. The target proof constructs `k` and `e` by composition and proves naturality from the two component naturality lemmas.

## Proved and sorry left

`exists_cartanEilenberg_page_realization` is proved from the two new intermediate declarations. The new declarations `CategoryTheory.Abelian.SpectralObject.exists_pageTwo_functor` and
`CategoryTheory.exists_cartanEilenberg_filtered_truncation_comparison` remain `sorry` and are recorded by nodes `lem-sp-spectral-object-page-two-functor` and `lem-sp-ce-filtered-truncation-comparison`.

Net holes: one closed and two added; this is a decomposition, not a sorry-free proof.
The constructed `CategoryTheory.Abelian.SpectralObject.pageTwoComparison` contains no hole.

## No longer needed

The original direct imports of `CartanEilenbergExists`,
`CartanEilenbergFunctorial`, `DoubleComplexTotal`,
`CartanEilenbergComparisonIndependence`, and `CartanEilenbergLeftExactCohomology` are no longer needed by the target module itself; their results are used by the filtered comparison node. The direct `FilteredComplexZBDescription` import is also removed from the target module.

These are import transfers, not global pruning: their modules remain reachable through
the intermediate comparison module. No previously planned mathematical dependency is
claimed globally unnecessary.

Every old direct `proof_deps` entry is absent from the new assembly proof:
`def-sp-filtered-page-two-model`, `def-sp-double-complex-total`,
`lem-sp-filtered-complex-ZB-description`, `lem-sp-cartan-eilenberg-exists`,
`lem-weil-pbc-injective-resolution-lift-exists`,
`lem-weil-pbc-cartesian-eilenberg-functorial`,
`lem-sp-cartan-eilenberg-comparison-independence`,
`lem-sp-cart-eilenberg-left-exact-cohomology`, `lem-sp-derived-well-defined`,
and `def-sp-cartan-eilenberg-presentation`.
Definition dependencies remain in the unchanged signatures or in the lower comparison
statement; comparison and cohomology dependencies remain in its proof plan.
The upper proof uses the existing upstream `grothendieckSpectralObjectHIso` directly,
not the statement of `lem-sp-derived-well-defined`. Globally pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

Validation: all three delivered modules compile with `lcompile.py --all`; the required
`deliver3.py --no-push` dry run passes except for the second reading, which is reserved
for the next worker.

The original four-step proof plan requires a substantial filtered comparison and page functor construction that are not available as existing declarations. These are split into two strictly smaller intermediate statements so the target proof is a genuine Lean assembly.

## New nodes

`lem-sp-spectral-object-page-two-functor` records the finite kernel/image construction and naturality of page-two realizations. `lem-sp-ce-filtered-truncation-comparison` records the Dec-filtration comparison with the canonical truncation spectral object.

The new statements were checked on zero spectral objects, zero functors, and complexes
concentrated in degree zero. No acyclicity hypothesis is introduced. The integer-indexed
page functor requires no convergence or finite filtration; the CE filtered comparison
uses degreewise finite diagonals, rather than a uniform bound. The unit record has no
realized nodes or steps for this imported CE node, so no unit statement is bypassed.
Sources read: [Stacks 015K](https://stacks.math.columbia.edu/tag/015K),
[Stacks 015X](https://stacks.math.columbia.edu/tag/015X),
and [Stacks 012K](https://stacks.math.columbia.edu/tag/012K).

## Second reading by V3

1. Compared the existing target module against the read-only repository using `diff`.
   Its theorem signature, universes, hypotheses, conclusion, and public imports are
   byte-for-byte unchanged. Only private proof imports and the proof body differ.
   The two other modules are new. No change record is necessary: no existing statement
   or definition changed. Verdict: pass.

2. Compiled all three modules in import order with `lcompile.py --all` (2.2, 3.8,
   and 6.7 seconds). Inspected every delivered declaration: exactly two named theorem
   sorries, both listed above; no forbidden declarations or hollow definitions.
   Scratch-copy `#print axioms` checks give only `propext`, `Classical.choice`, and
   `Quot.sound` for `pageTwoComparison`; each new open theorem and the assembled
   target also has `sorryAx`, as expected. The latter is a conditional assembly proof,
   not a sorry-free result. `k` and `e` are explicit composites; no definition chooses
   an arbitrary witness from either existence theorem. Verdict: pass as decomposition.

3. Read both new statements and their complete proof docstrings against Mathlib's
   spectral-object construction, `SpectralSequence.Hom.comm`, Stacks 012K (filtered
   cycle/boundary construction and functoriality), 015K, and 015X (second sequence).
   The page functor lemma applies to arbitrary integer-indexed spectral objects and
   needs no convergence hypothesis: each page involves finite kernels and images.
   The comparison lemma fixes E and c and removes the derived-page computation from
   its conclusion; it is a filtered comparison problem, not the original existential
   statement under another name. Its all-integer naturality hypothesis suffices:
   after conjugating by c, agreement on page two forces agreement on later pages
   using `Hom.comm` and cancellation of the successor homology isomorphism.
   For zero objects or zero functors all relevant page maps vanish; for a complex
   concentrated in degree zero, the resolution filtration gives R^pG in q=0.
   Negative total degrees vanish for CE totals; each nonnegative diagonal is finite.
   The shifted filtration at a=-q contains the augmentation below degree q and
   imposes exactly its cycle condition at degree q. Additivity preserves the split
   horizontal cycle/boundary sequences and comparison homotopies, so no preservation
   of injectives by G or acyclicity of F(injectives) is assumed.
   Repeated searches with different words using launcher leanfinder, loogle and grep,
   plus rg of Sheaf and the upstream spectral-object/Grothendieck files, found only
   related APIs. Mathlib constructs spectral-sequence objects but does not expose the
   required functor on spectral-object morphisms. Neither remaining proof is a
   few-minute direct application. Verdict: sound strictly smaller open tasks.

4. Read the proof from its two `obtain` reductions through the naturality calculation.
   `hc` supplies naturality of k, the upstream natural isomorphism supplies naturality
   of e, and both requested component equations are `rfl`. There is no shorter
   existing CE/truncation comparison found. Signature imports remain public;
   imports used only by the proof are private. The transferred proof dependencies
   remain reachable below the new comparison module; no global pruning is claimed.
   Checked `dag/units/sk-prop-av-pqf-finite.json`: none of its realized statement or
   step arrays names this CE node. Its route has not been bypassed. Verdict: pass.

5. Read all three node files alongside the Lean. Both new nodes have the required
   source, proof, search, creation, blueprint, unit, chapter and Lean records, with
   their theorem signatures matching the files. The upper node's first two steps
   match the two actual reductions. Corrected its third step: the proof uses the
   upstream `grothendieckSpectralObjectHIso`, not the DAG statement of
   `lem-sp-derived-well-defined`; removed that unused direct proof dependency.
   Completed `No longer needed` with every old direct dependency. Verdict: pass
   after these metadata/report repairs. No Lean proof or statement was rewritten.
