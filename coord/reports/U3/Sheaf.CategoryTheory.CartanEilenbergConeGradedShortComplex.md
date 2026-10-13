## What changed

Replaced the earlier sandbox reduction by a compiling proof of
`CategoryTheory.Functor.cartanEilenberg_cone_graded_shortComplex_iso`, preserving the
repository signature and docstring. Its proof obtains normalized degreewise comparisons
at `n-1`, `n`, and `n+1`, applies two adjacent differential equalities, constructs the
inverse short-complex isomorphism with `ShortComplex.isoMk`, and composes with
`HomologicalComplex.isoSc'` to handle the integer index identifications.

Added two modules, each with one public postponed theorem:
`Sheaf.CategoryTheory.CartanEilenbergConeGradedNormalizedIso` and
`Sheaf.CategoryTheory.CartanEilenbergConeGradedNormalizedDifferential`.
The former also defines the real predicate `CartanEilenbergConeGradedNormalized`:
it specifies the comparison on the retained I-column and K-cone inclusions, using
lifts through the filtration inclusion and the actual graded quotient projection.
There is no choice-based definition and no postponed data. The degreewise comparison
does not assume `haug`; only the differential calculation needs it. Its remaining
hole is restricted to `p-1 ≤ m`. The private proved helper
`normalized_iso_all_degrees` treats `m<p-1` directly: the image-supremum filtration
step is zero, its monic inclusion has zero source, and its evaluated graded
quotient projection is epic, hence has zero target. The two column-cone terms
are zero by extension by zero. Their zero-object isomorphism is normalized
because neither normalization condition can have a nonzero source in this range.

The main module adds one proof-only import of the differential module. That module
publicly imports the normalized object comparison because its statement uses the
normalization predicate. Original public imports remain because the original statement
uses their definitions. Updated the parent node's proof route and added the two nodes.

All three modules compile locally without warnings. The decomposition preserves the
original column quotient argument rather than asserting compatibility of arbitrary
object isomorphisms. The source calculations were checked against Stacks Tags 012X
(second-filtration graded differential) and 0133 (canonical augmentation).

## Proved and sorry left

Closed the original hole:
`CategoryTheory.Functor.cartanEilenberg_cone_graded_shortComplex_iso`.
There is no `sorry` in the item's module.

Added two holes, exactly `:= by sorry`, in separate modules:

- `CategoryTheory.Functor.cartanEilenberg_cone_graded_normalized_iso`
  (`lem-sp-cartan-eilenberg-cone-graded-normalized-iso`): the degreewise quotient
  comparison with explicit retained-summand normalization for `p-1 ≤ m`.
  No differential square; the complementary degree range is proved locally.
- `CategoryTheory.Functor.cartanEilenberg_cone_graded_normalized_differential`
  (`lem-sp-cartan-eilenberg-cone-graded-normalized-differential`): one adjacent
  differential square for two already normalized comparisons. No existence or
  invertibility assertion.

This is a decomposition of one hole into two, not a completed foundational proof or
a net reduction of holes. Each lower result is a strict part of the argument. Their
combination, the three-term assembly, and all integer reindexing, and all degrees `m<p-1` are proved in Lean.

Boundary checks before stating the new lemmas: if `p<b`, both column-cone summands
vanish; if `m<p-1`, both vanish by extension by zero; at `m=p-1` only `K^p` can remain;
at `m>=p` only `I^{p,m-p}` can remain. The normalization tests exactly those two
possible nonzero summands. Lifts are uniquely determined by the monic filtration
inclusion; their equations determine the inverse comparison on the cone's generating
summands. The differential has the retained resolution coefficient one because the
bicomplex is flipped, and the augmentation block is fixed by `haug`.

## No longer needed

No original public import or existing DAG dependency module can be removed: they
supply definitions used in the unchanged signature and lower statements. The old direct
proof dependency `def-sp-double-complex-total` is replaced by the two normalized
comparison nodes, both of which still use it; its module remains transitively imported.
No module is globally pruned, and no claim of global pruning is made. The optional direct proof import of the normalized object
comparison was removed because the differential module publicly exposes it.

Discarded the two unlanded helper nodes of the rejected earlier sandbox attempt:
`lem-sp-cartan-eilenberg-cone-graded-piece-iso` and
`lem-sp-cartan-eilenberg-cone-graded-piece-iso-comm-sc`, and their same-module theorem
bodies. The latter's arbitrary-isomorphism compatibility assertion is not used.
These were never existing library nodes and are not counted as global pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier worker's compatibility theorem was false: arbitrary independently chosen
isomorphisms need not commute with differentials. It also placed the new holes in the
item's own module, used incomplete docstrings, and gave their node Lean records the
parent statement rather than their own signatures. This replacement uses new modules,
complete proof descriptions, correct blueprint identifiers and verbatim Lean records.
It replaces arbitrary isomorphisms by maps specified on actual column inclusions.
The earlier second-reading section is not carried into this new worker report.

The existing planned dependency nodes supply definitions, not the augmented-cone
quotient comparison or its differential compatibility. The two new nodes isolate
those calculations. The unit record `sk-prop-av-pqf-finite` has empty `realized`
statement and step lists; no unit realization is bypassed or removed.

## New nodes

`lem-sp-cartan-eilenberg-cone-graded-normalized-iso` gives the degreewise quotient
calculation and explicitly records its normalization on both possible cone summands.
It follows parent steps 1-2, Stacks Tags 012X and 0133, with the already proved
negative-resolution range excluded by the explicit `p-1 ≤ m` hypothesis. The normalization is real data
specified by equations, not a renamed short-complex isomorphism theorem.

`lem-sp-cartan-eilenberg-cone-graded-normalized-differential` gives parent step 3
for one pair of adjacent degrees, assuming the two normalized degreewise comparisons.
It follows the resolution, horizontal, and augmentation block calculations of the
same sources. It does not assert compatibility of arbitrary comparisons.

Both nodes record semantic search, Loogle and local source search. Searches find
Mathlib's cone/functor comparisons and `ShortComplex.isoMk`, but no theorem covering
the augmented column-tail quotient. No existing interface changed and no change
record or forced adaptation is needed.

## Second reading by U3

1. **Visible interface: pass.** Compared the complete delivered main module with
   the repository using `diff -u`, then extracted the existing theorem signature
   and checked byte-for-byte equality. Its docstring and original public imports
   are unchanged. The only original body replaced is
   `cartanEilenberg_cone_graded_shortComplex_iso`; the other main-module additions
   are a private proved helper and a proof-only import. The two new modules add
   their stated interfaces and do not adapt another existing module. There is no
   statement/definition change requiring a change record.
2. **Kernel checks: pass as a decomposition.** Compiled all three modules in import
   order with `lcompile.py --all`: no errors or warnings (about 2--3 seconds each).
   Searched all delivered Lean for forbidden declarations and holes: exactly the
   two named public `:= by sorry` theorems listed above remain, with none in a
   definition or in the main module. A scratch module printed axioms of the
   normalization predicate, both lower theorems and the original theorem. The
   predicate uses only `propext`, `Classical.choice`, `Quot.sound`; the three
   theorems additionally use `sorryAx`, as expected from the two lower holes.
   The predicate defines equations, with no witness chosen from an unproved
   existence assertion. The main proof eliminates existential isomorphisms only
   to prove a proposition; it defines no public data from them.
3. **Lower statements: pass.** Read each Lean signature, normalization equation,
   docstring argument and node. The degreewise lemma omits `haug` because the
   object quotient only depends on the steps. The differential lemma requires
   `haug` and already normalized comparisons, and asserts one square, without
   asserting any existence. Thus neither restates the short-complex theorem.
   In degree `m=p-1` the column cone has only `K^p`; its next differential is the
   augmentation into `I^{p,0}` with coefficient +1. At `m>=p` only the retained
   I resolution term can be nonzero. At `m<p-1` both terms vanish, as the private
   helper proves. For `p<b`, the retained column and K term vanish by the two
   bound hypotheses; the quotient is zero, including empty intervals. For
   `p=b` the retained summand is included rather than accidentally discarded.
   Monicity makes each lift unique, and the two normalization equations specify
   the inverse on all potentially nonzero cone summands.

   Independently searched with `msearch.py` using a finite independent-subobject
   tail quotient query (LeanFinder), a quotient differential checked on generating
   inclusions query (LeanFinder), `"mappingCone", "inr"` (Loogle), and
   `cokernel.*(biproduct|coprod)|graded.*(cone|column)|secondFiltration` (grep).
   The first semantic search returned module/direct-sum equivalences, not an
   abelian-category filtration theorem; the second returned cofiber extensionality
   and index transport. Loogle found `mappingCone.inr_f_d`; grep found biproduct
   cokernel facts. These are ingredients, not either lower statement. Local `rg`
   in both Lean roots and the upstream WeilConjectures checkout found no duplicate.
   Read `ConeHorizontalGradedIso` and `DoubleComplexTotal.secondFiltration_graded`:
   the former concerns a natural-indexed total-map cone with a shift/sign twist,
   the latter an unaugmented first-quadrant total. Neither directly proves the
   present integer-indexed augmented comparison. Closing either lower statement
   still requires its stated quotient or generator calculation.
4. **Route and pruning: pass.** Read Stacks [012X](https://stacks.math.columbia.edu/tag/012X)
   (second-filtration graded differential) and
   [0133](https://stacks.math.columbia.edu/tag/0133) (canonical augmentation), and
   compared the arguments with Mathlib `total_d`, `d₁_eq'`, `d₂_eq'` and
   `mappingCone.inl_v_d`/`inr_f_d`. Flipping makes the retained resolution block
   the first differential, of coefficient one. The signed horizontal block and
   `-d_K` raise complex index and factor through the next step. The remaining
   off-diagonal block is identified by `haug`. No exactness or quasi-isomorphism
   assumption is silently used. The main proof really assembles three object
   comparisons and two squares, then transports prev/next indices. All original
   imports supply signature definitions; the only new main import is private to
   the proof. Checked `sk-prop-av-pqf-finite.realized`: its statement and sole step
   lists are empty, and no realization is bypassed. No module is pruned.
5. **DAG agreement: pass after metadata repair.** The parent records the proved
   negative-support case, the three normalized comparisons, two differential
   squares and `isoMk`/`isoSc'` assembly. Each lower node has its own self-contained
   statement, source, complete prose proof, dependency union, search records,
   creation and blueprint provenance, chapter/unit and Lean record. Verified both
   new `lean.statement` fields verbatim against their declarations and checked
   that `proof_deps` equals the union of proof-step uses. The old total-complex
   dependency remains through the lower nodes; no old dependency module became
   unused. Corrected the parent's previously single-line `lean.statement` record
   to the actual unchanged multiline signature.

Changes in this reading: corrected that parent Lean record, clarified the replaced
old direct proof-dependency edge under `No longer needed`, and added this independent
review with compilation, axiom, source, boundary-case and duplicate-search evidence.
No Lean proof or statement needed repair. One original hole is closed syntactically
and two strictly smaller holes are added: this remains a decomposition (net -1 holes),
not a claim of a completed foundational proof.
