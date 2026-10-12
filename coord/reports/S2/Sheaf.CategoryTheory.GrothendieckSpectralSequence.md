## What changed

Replaced the sole postponed proof of
`CategoryTheory.exists_grothendieck_spectralSequence_cartanEilenberg`
with a complete Lean reduction to two independent parts of the CE argument.
The declaration signature and its existing docstring are unchanged.

Added `Sheaf.CategoryTheory.CartanEilenbergPageRealization` and
`Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment`, one named statement
per module, and imported them privately in the item. The first constructs the
filtered page functor and its canonical E2 comparison without any acyclicity
hypothesis. The second uses acyclicity to identify total cohomology and its
image filtration; it does not construct the page functor or compute E2.
Neither lemma has the item's complete conclusion or merely repackages a
hypothesis of it.

The item's proof itself constructs a presentation for every X using the
existing CE existence theorem; transfers first-quadrant vanishing through
c using Mathlib page and evaluation functors; proves the two filtration
bounds using the existing truncation image-filtration lemmas; constructs
both transported edge maps; and proves all four edge equations and the
identification with the existing natural edge maps. In the left-edge
calculation an equality-elimination lemma handles the dependent cast from
cohomology degree n to 0+n. The existing node's proof and proof dependencies
now describe this argument.

The unit record has no realized statement or proof-step nodes for this
item, so this reduction does not bypass a realized unit step.

## Proved and sorry left

Proved by reduction:
`CategoryTheory.exists_grothendieck_spectralSequence_cartanEilenberg`
(node `thm-sp-grothendieck`). There is no direct sorry in its module.
It still depends on postponed theory, as intended in stage 3.

Exactly two new whole-proof sorries remain in the delivery:

- `CategoryTheory.exists_cartanEilenberg_page_realization`
  (`lem-sp-ce-page-realization`,
  `Sheaf.CategoryTheory.CartanEilenbergPageRealization`).
- `CategoryTheory.exists_cartanEilenberg_acyclic_abutment`
  (`lem-sp-ce-acyclic-abutment`,
  `Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment`).

The unchanged dependency `CategoryTheory.exists_cartanEilenberg_resolution`
also remains postponed outside the delivery. No definitions, target
signatures or existing intermediate signatures changed. No extra axioms.

All three delivered modules compile locally in import order.
The required deliver3.py --no-push dry run printed OK after local compilation,
axiom probes, server compilation and preflight (only the second reader
section remains for that reader). The revised DAG closure has 68 nodes
with no cycles or missing dependencies. Nothing was pushed. The main
assembly was compiled repeatedly while resolving casts and removing the
first-quadrant and filtration-bound clauses from the new postponed lemmas.

Edge cases checked against the statements: zero objects and zero functors;
degree n=0 (the bounds are step 0=top and step 1=bottom); negative p or q
(the vanishing is proved in the item); arbitrary presentations, including
nonminimal resolutions; and merely additive left exact F which does not
send injectives to G-acyclics (allowed by the page lemma but excluded by
the abutment lemma). All six category universes remain independent.
The second lemma needs only objectwise c for stable terms, so no unjustified
naturality of c is assumed.

## No longer needed

Removed these direct private imports from the item:

- `Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence`
- `Sheaf.CategoryTheory.CartanEilenbergExists`
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`
- `Sheaf.CategoryTheory.DoubleComplexTotal`
- `Sheaf.CategoryTheory.ExactCoupleConvergence`
- `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`
- `Sheaf.Paper.CartanEilenbergLeftExactCohomology`
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`

The CartanEilenbergExists and DoubleComplexTotal declarations needed by the
item's statements and presentation construction are already public imports
of CartanEilenbergPresentation, so their duplicate imports were removed.
The new helper signatures also do not need an import of the source
TotalComplex module. Removed the unused ExtendHomology import from the
page lemma. In the abutment lemma, replaced FilteredPageTwoModel with
the narrower FilteredComplexSubquotients import needed for complexStep.

At the DAG level `def-sp-convergence` is no longer a direct or new-helper
proof dependency: the actual convergence clauses use the finite image
filtration and the existing spectral-object comparisons, rather than the
abstract exact-couple convergence package. The other removed direct proof
imports correspond to ingredients retained in the two helper nodes' plans,
or to vocabulary already publicly available. Their removal is not a claim
that those ingredients are mathematically unnecessary or globally unreachable.

The complete difference of the old and new direct `proof_deps` is:

- `def-sp-convergence`: removed directly; still reached through existing plans.
- `def-sp-double-complex-total`: used by both helper plans and presentation vocabulary.
- `def-sp-left-exact-additive`: retained through statement dependencies.
- `thm-sp-double-complex-spectral-sequences`: used by the acyclic computation.
- `lem-weil-pbc-first-quadrant-row-collapse`: used by the acyclic computation.
- `lem-sp-cart-eilenberg-left-exact-cohomology`: used by the page computation.
- `lem-weil-pbc-injective-resolution-lift-exists`: used by page functoriality.
- `lem-weil-pbc-cartesian-eilenberg-functorial`: used by page functoriality.
- `lem-sp-cartan-eilenberg-comparison-independence`: used by page functoriality.

These nine nodes no longer need direct citations in the item's proof. None is
removed from its full DAG closure: the old closure has 66 nodes, and the new
closure has those 66 plus the two helper nodes (68). No globally unreachable
node or module is claimed as pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The DAG node lem-sp-grothendieck-edge-maps depends on this item. The Lean
assembly only unfolds the already implemented edge definitions and proves
the equations directly, so it does not cite that node or create a cycle.

The recorded double-complex spectral-sequence declaration is only the
natural-indexed first sequence; its signature does not supply the common
FilteredPageTwoModel, the resolution-degree second filtration, descent to
objects, or the comparison with the truncation spectral object. Likewise,
comparison independence requires a supplied model and gives data on
presentations, rather than directly the functor and canonical comparisons
required by this item. Therefore those declarations cannot directly close
the full item by specialization. The two new statements isolate this
missing assembly and the separate acyclic abutment computation.

The local checkout lacks literature/stacks-project/derived.tex. Read the
primary Stacks pages directly: Tags 015J, 015K, 015N, and especially 015X,
which supplies the filtered injective-resolution/truncation comparison.
The new docstrings expand the differential sign normalization and the
shifted cycle filtration used in that comparison; these expansions are
marked as agent work in proof_origin. The original theorem's docstring
was preserved. No statement was found false or weakened.

Mathlib searches were executed through msearch.py: LeanFinder found
injective-resolution infrastructure, Loogle's broad grothendieck query
found group constructions, and source grep found no CE declarations.
LeanSearch returned an Internal Server Error, recorded as unavailable.
Local source search found the existing truncation spectral object,
natural derived page isomorphisms and natural edge maps; these are reused.
Blueprint searches for CE truncation, acyclic total cohomology, decalage
and Tag 015X found no matching blueprint node.

## New nodes

`lem-sp-ce-page-realization` records the page construction and comparison
without acyclicity, serving the second-spectral-sequence and functoriality
parts of thm-sp-grothendieck. Its natural-language argument specifies the
sign correction and Dec filtration comparison of Tag 015X.

`lem-sp-ce-acyclic-abutment` records the acyclic total comparison and
presentation-independent image filtration, serving the first-sequence
collapse and common-abutment parts. It supplies the augmentation equation,
comparison square, filtration images, stable terms and step naturality;
the item itself proves the finite bounds and all edges. Both nodes inherit
the item's chapter and unit and carry exact Lean signatures and the actual
search records. No change record is needed: all existing signatures,
definitions and public imports are unchanged.

## Second reading by S2

1. **Existing interfaces: pass.** Read all three delivered modules and diffed the
   item against the repository version. Compared the bytes from the existing
   theorem's `theorem` keyword through its `:= by`: identical, including all six
   category universes, the Grothendieck and derived-category instances, left
   exactness and the acyclicity hypothesis. The original docstring and four public
   imports are unchanged. The only existing proof is replaced; the eight removed
   imports were private. The two additional declarations are new, each in its own
   module. There are no changed definitions or signatures and no change record
   is needed.

2. **Kernel checks: pass as a reduction, still conditional.** Independently ran
   `lcompile.py --all` in import order: each module compiles without warnings or
   errors, in under seven seconds per file. Scratch copies under `scratchpad/`
   append `#print axioms` for each of the three public theorems. Each reports
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Thus the
   original theorem has no direct sorry but is not yet an axiom-free completed
   target. Only the two named helper theorems have whole-proof sorries in this
   delivery. Checked the text for axiom, unsafe, opaque, implemented_by, extern,
   written sorryAx and overlong lines: none. There are no definitions in these
   files. The remaining CE existence sorry is outside the delivery.

3. **Split statements: pass after clarifying their proof sketches.** Read
   [015H](https://stacks.math.columbia.edu/tag/015H),
   [015J](https://stacks.math.columbia.edu/tag/015J),
   [015K](https://stacks.math.columbia.edu/tag/015K),
   [015M](https://stacks.math.columbia.edu/tag/015M),
   [015N](https://stacks.math.columbia.edu/tag/015N), and the filtered construction
   [015X](https://stacks.math.columbia.edu/tag/015X) with its preceding
   [015W](https://stacks.math.columbia.edu/tag/015W). Matched the presentation's
   five resolution fields and common augmentation with the CE definition. The
   page statement needs no acyclicity: split horizontal cycles and boundaries
   compute the second page. Resolution degree is the first spectral index,
   complex degree is the second, and multiplying term j by (-1)^(q*j) handles
   the vertical differential sign. Its conclusion has no total-derived-composite
   identification. The abutment statement separately requires hFG, which kills
   positive column cohomology. It constructs no page model, page functor or E2
   identification, and assumes only objectwise c. The two results are strictly
   different parts of the argument, not renamed copies of the item.

   Checked the zero functor and zero object, n=0, negative filtration steps,
   p=0 and p=n+1, arbitrary nonminimal presentations, and a left exact F whose
   injective images are not G-acyclic. In the last case the page assertion still
   holds, while the abutment assertion is not available. For stability, outgoing
   and incoming positions leave the quadrant when r>q+1 and r>p respectively.
   Left exactness is used to preserve the kernels defining Dec; finite sums and
   comparison homotopies use additivity. G is applied to a filtered injective
   computation, not presumed to preserve the augmentation quasi-isomorphism.
   The truncation index n+1-p corresponds to tau_{<=n-p}, with no off-by-one
   shift. Each lemma has a source, a full proof sketch and a matching node.

   Repeated discovery with different vocabulary: LeanFinder query
   "spectral sequence of a filtered injective resolution canonical truncation
   filtration decalage hypercohomology"; Loogle query "SpectralSequence";
   Mathlib grep for "decalage|hypercohomology|filtered.*resolution|resolution.*filtered".
   LeanFinder returned injective-resolution infrastructure; Loogle returned
   general spectral-object and shape declarations; grep returned no match.
   These searches are recorded in searches.jsonl. Source and Sheaf searches
   located the existing truncation sequence and the separate first-page CE
   theorem, not the missing filtered CE-to-truncation comparison. No helper is
   a few-minute specialization of an existing theorem, so their sorries remain.

4. **Route and pruning: pass after completing the report.** Read the existing
   source Grothendieck module, presentation, page model, comparison-independence
   statement, double-complex filtration definitions and the spectral-object
   image-filtration implementation. The proved source Grothendieck sequence
   does not assert its CE realization; applying it alone would drop part of the
   existing conclusion. The actual proof uses existing CE existence to build
   presents, existing page/evaluation functors and first-quadrant lemmas for
   vanishing, and imageFiltration_eq_top/bot for the two finite bounds. It defines
   bottom and left using the existing natural transformations, cancels k via the
   e equation, and handles the dependent 0+n cast by equality elimination.
   There is no circular application of the edge-maps theorem. Every public
   import is needed in a signature; the two proof helper imports are private.
   Completed the list of all nine removed direct proof dependencies above and
   distinguished them from global pruning. The unit
   sk-prop-av-pqf-finite has realized.statement=[] and realized.steps=[[]], and
   its proper/quasi-finite geometric proof is unaffected. No realized unit step
   or chapter route is bypassed.

5. **DAG and Lean: pass.** Checked each node's recorded Lean signature against
   its module after whitespace normalization: all agree. The existing node
   changes only proof, proof_deps and proof_origin. Its four steps match the
   actual presentation construction, helper assembly, vanishing/bounds and
   edge calculations; each helper's proof dependencies are the union of its
   step uses. Both new nodes have source, statement dependencies, searches,
   creation provenance, blueprint ancestor/place, chapter/unit and complete
   Lean records. Independently traversed the combined statement/proof closure:
   68 nodes, no missing dependency and no cycle. The proof_origin records the
   expanded comparison as agent work.

Changes made by this second reading: completed the pruning report; clarified
in the page helper's proof sketch that the Dec filtration is a filtered
injective resolution and comparisons are made before applying G; explained
kernel preservation in the abutment helper; replaced its ambiguous transport
of a CE stable term along c with the truncation spectral-object quotient-image
computation followed by c; updated both helper nodes' matching proof steps;
and restored the blank line after the item's imports. All declaration
signatures and executable proof terms are unchanged. No new sorry was added.
