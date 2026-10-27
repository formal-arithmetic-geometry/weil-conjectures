## Worker report

Stage 2, Q104. The previous worker's stale-assignment rejection was for stage 1.
The current queue has this item at stage 2, the current node has no Lean record,
and coord/brief-stage2.md section 0 explicitly authorizes this stage handoff.
The accepted Q121 split and every proof step are preserved.

The module Sheaf.Combinatorics.OrderedCompositionComplexHomology constructs the
ordered vector-composition complex and its rational dual, and states all the
comparison, finiteness and homology conclusions. No definitions contain sorry.
Every theorem is postponed, with the proof in its source/blueprint docstring.
The ordered-composition helpers belong to this node. The existing proper-interval
construction is now owned by the new definition node described below; no
replacement module or second complex is introduced.

Clause-by-clause correspondence:

- r >= 0 and m in N^r: `{r : ℕ} (m : Fin r → ℕ)` in every declaration.
  There is no positivity assumption on r and no nonzero assumption on m except
  in the two comparisons where the node explicitly requires m nonzero.
- Ordered tuples of n nonzero vectors summing to m: `Basis m n`, a subtype of
  `Fin n → (Fin r → ℕ)` with both conditions. `Terms m n` is its rational free
  module. For n=0 the sum condition is exactly m=0, so the empty tuple occurs
  in exactly the stated case.
- Negative terms zero: `complex m` is `complexNat m` extended along the natural
  inclusion into integer chain degrees, using Mathlib's extension-by-zero.
- Adjacent merges and coefficients (-1)^a for one-based a: `mergeRaw` retains
  blocks before the chosen pair, adds the pair, and shifts later blocks left.
  `merge_valid` supplies only the proof that this is again a basis tuple.
  `boundary m (n+1)` sums `Fin (n+1)` positions with exponent `a.val+1`.
  `boundary m 0` is zero (degree one to degree zero); the degree-zero outgoing
  map is zero by chain-complex shape and extension. `boundary_squared` states
  precisely that consecutive merge differentials compose to zero.
- Rational dual and its unsigned transpose differential: `dualBoundary` is
  `(boundary m n).dualMap`, and `dualComplex` has terms `Module.Dual ℚ` of the
  exact same `Terms`. `dualBoundary_squared` states the required identity.
- Kernel modulo image: Mathlib `HomologicalComplex.homology`, specialized to
  ModuleCat, is used for homology and dual cohomology, as recorded by the
  dependency. `ShortComplex.moduleCatHomologyIso` identifies this with the
  literal kernel/image quotient. Natural grading computes the same degrees
  n>=0 as integer extension, including zero incoming or outgoing maps.
- Proper coordinatewise interval, strict-chain basis, empty chain and deletion
  boundary: the published `ProductChainProperInterval.ChainBasis`, `Chains`,
  `boundary` are used directly. No second proper interval or deletion complex
  is defined. The new definition node def-sfb-product-chain-proper-interval-complex is
  added to stmt_deps; its homology theorem stays in proof_deps.
- Cumulative sums: `partialSums` sums exactly the blocks of index <= a, and
  `cumulative` gives the strict chain on these vertices. `partialSums_valid`
  supplies the proof of membership and strict increase; it determines no data.
  `cumulativeLinear` extends this specific map linearly.
- Identification and minus sign: `cumulative_comparison` asserts bijectivity in
  every degree n+1 and the equation `F_n ∘ partial = -(boundary ∘ F_(n+1))`.
  Its n=0 case compares the two-block merge with the augmentation. The single
  block maps to the empty chain; degrees <=0 on either comparison side vanish
  for nonzero m, as forced by the explicitly constructed terms.
- Shift n-2 with the original boundary: `IntervalBasis m 0 = Fin 0`; in degree
  n+1 it is the published n-vertex chain basis, i.e. interval degree n-1.
  `intervalBoundary` is the published boundary with no sign change, zero at
  the bottom. This is a regrading of the existing construction, not a second
  definition of its underlying interval or boundary.
- Sign-corrected chain isomorphism: `comparison` supplies `e`, with its positive
  degree components required to equal `(-1)^(n+1) • cumulativeLinear m n`.
  At degree zero source and target are zero, hence the component is unique.
- Derived isomorphism: the same theorem supplies `d` and requires it to be
  `DerivedCategory.Q.mapIso` of the extension of this very `e` along
  `ComplexShape.embeddingDownNat` (n maps to -n). Thus it is the canonical
  localization image, with no arbitrary comparison map or per-degree proxy.
  The explicit `[HasDerivedCategory.{w} (ModuleCat.{0} ℚ)]` only selects the
  localization universe required by the recorded derived-category dependency.
- All terms finite dimensional: the first conjunct of `homology`.
- Vanishing for nonzero m and n>sum m: its second conjunct uses `IsZero` on
  the actual chain term, with exactly these hypotheses.
- Equality of homology/cohomology dimensions for every m and n>=0: the first
  equality in its third conjunct. The second equality is the exact if-formula
  for squarefree coordinates and n=sum m. No dimension zero alone is used as
  a proxy for infinite-dimensional vanishing: finite terms are also asserted.
- Any coordinate >=2 gives both complexes acyclic: the last conjunct gives
  `IsZero` of every natural-degree homology/cohomology object. Negative degrees
  are zero by construction. The m=0 clause follows from the basis description
  and formula: one rational generator at zero and none elsewhere, also r=0.

Dependency declarations read and used:

- Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex:
  `HomologicalComplex.homology`, recorded by
  def-weil-pbc-module-chain-complex-homology. Its actual signature/docstring
  were read, along with the ModuleCat kernel/image realization.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; their full signatures and universe
  binders were read for def-weil-abstract-derived-category.
- Sheaf.Combinatorics.ProductChainProperIntervalHomology: `ProperInterval`,
  `ChainBasis`, `Chains`, `boundary`, `boundary_squared`, `complex`, `homology`.
  The entire published module was read. Its existing statement is only the
  interval homology result, so it does not already state this item's comparison.
- Proof imports: Mathlib.LinearAlgebra.FiniteDimensional.Lemmas contains
  `LinearMap.finrank_range_add_finrank_ker`; Dimension.RankNullity contains
  `Submodule.finrank_quotient_add_finrank`; Dual.Lemmas contains
  `Subspace.instModuleDualFiniteDimensional`, `Subspace.dual_finrank_eq`,
  `LinearMap.finrank_range_dualMap_eq_finrank_range`. These are the exact
  recorded mathlib_match declarations for the three dimension proof leaves.

Edge checks before/during writing: r=0 forces m=0; m=0 has the unique empty
basis only at degree zero; for m a unit vector the interval is empty and the
single-block tuple gives degree-one homology; for two blocks the merge sign is
-1 and agrees with minus augmentation; for n>sum m no tuple can exist; for a
coordinate >=2 the displayed formula and the explicit acyclicity clause agree.
Zero coordinates do not create nonzero blocks or remove admissible m.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches (2026-10-23, exact wrapper logs in searches.jsonl):

- msearch.py leanfinder: "Ordered vector compositions with adjacent merging
  differential identify with shifted augmented proper product interval chains
  and have squarefree homology" returned eight hits, including scalar
  Composition.boundary and Composition.orderEmbOfFin_boundaries and Dold-Kan
  c_mk. These have neither vector blocks nor this homology comparison.
- msearch.py loogle: `"Composition", "homology"` returned zero hits.
- msearch.py grep: `composition.*homolog|CompositionComplex|merge.*boundary`
  returned three unrelated ShortComplex homology-map composition comments.
- rg on lean/Sheaf and lean/WeilConjectures for orderedComposition,
  OrderedComposition, properInterval, ProperInterval, productChain,
  ProductChain, ordered.composition found the published proper-interval module
  and unrelated simplex shuffle/ordered integration definitions. None defines
  this vector-composition basis or its comparison. Searching the exact node id
  in WeilConjectures and dag/lean_names_upstream.json returned no match.

Validation: prescribed scompile.py passed both sandbox and library module
compilation with no errors or warnings (5.5s and 4.8s). Every variable and universe
is explicitly bound; autoImplicit and relaxedAutoImplicit are disabled.
Independent maintainer review is supplied by the dispatch workflow; no second
agent was started, in accordance with this worker's explicit brief.

## Repair of return L (immutable head 0a1917a9af6a)

The initial saved-packet dry run passed as edfaf4f1398, but the independent
maintainer return identified a semantic dependency-ownership issue beyond that
mechanical check. Replaced the added statement dependency
lem-sfb-product-chain-proper-interval-homology by the new definition node
below. The theorem remains in proof_deps, unchanged. The item's statement,
proof, proof_deps, Lean signatures and Lean module are unchanged. The new node
records all eight construction declarations requested in the return, including
boundary_squared. No published file or theorem-node record is edited.

## New nodes

`def-sfb-product-chain-proper-interval-complex` records, with existing:true,
`ProductChainProperInterval.complex` in the unchanged published module
`Sheaf.Combinatorics.ProductChainProperIntervalHomology`. It owns ProperInterval,
ChainBasis, Chains, boundary, boundary_squared, complexNat,
augmentedDegreeEmbedding and complex. The definition is the coordinatewise
proper interval, its rational strict-chain modules, alternating deletion with
augmentation, and the extension by zero below degree -1. Its source is the
agent-formulated A(m) construction below latest direct-images paragraph (3),
explicitly distinguished from the blueprint's motivation. For every r and m,
including zero, the existing construction has these terms; only its homology
theorem requires r>=1 and m nonzero. The empty interval has Q in degree -1 and
zero in nonnegative degrees; a two-vertex chain has boundary [v1]-[v0].

Searches for the new node: msearch.py LeanSearch query "Augmented rational chain
complex of strict chains in the proper interval of a product of finite chains"
returned eight generic augmentation/construction hits; LeanFinder query
"Augmented chain complex with empty chain and alternating vertex deletion on a
proper product interval" returned eight generic alternating/simplicial hits;
msearch.py grep "ProductChainProperInterval|proper.interval|augmented.*[Cc]hain"
returned four generic augmentation hits. Their exact JSON results are recorded
in mathlib_searches. rg in WeilConjectures and Sheaf found the exact specialized
construction in ProductChainProperIntervalHomology. DAG search found its theorem
node and the general augmented-poset chain nodes, but no definition node owning
these specialized declarations. blueprint_refs.py search product-chain-proper
returned zero matches; ancestor returned None, recorded as null. The general
poset complex has list bases and is not a replacement for the already used
specialized order-embedding declarations. This adds a record for the existing
construction, with no duplicate Lean declaration.

## Second reading by Q104

Repair self-check, with both node files, the saved item module and the published
interval module open: the new definition matches ProperInterval's three
conditions, ChainBasis's n vertices, Chains's rational finite support,
boundary's zero-based alternating sign, boundary_squared's sole proof
obligation, and complex's n-1 integer grading with extension by zero. No
positivity or nonzero hypothesis is imposed on the construction. The item uses
ChainBasis, Chains and boundary in its cumulative and interval comparison;
it does not use ProductChainProperInterval.homology to construct any data.
The new definition is consequently the statement dependency, and that theorem
is exclusively a proof dependency. The full previously accepted clause mapping
and the r=0, m=0, one-block and two-block edge checks above still apply. No Lean
change or mathematical statement correction was needed. The dispatch workflow
supplies the independent maintainer review; this is the required worker
self-check, not a claim of review by another agent.

Repair validation: standalone scompile.py passed the unchanged item in sandbox
and library modes (5.5s and 4.8s). The first repaired-packet dry run required
the current server schema field import_flags on the new definition node; it
is now the empty list (no import flags). No source definition was changed.


## Repair of return L (immutable head 2c690ef71e93)

The required first dry run of the retained packet passed, producing dry-run
commit 4b97ea2cf70. The saved module and current published interval module were
then compared at their definitions of Basis/ChainBasis, Terms/Chains, boundary,
and boundary_squared. Current main has no OrderedCompositionComplexHomology
module and the item has no Lean record. The retained packet differs from the
current item only in lean and the previously requested definition dependency.

The return's qualification exception applies: the two printed signatures have
different meanings because `boundary` resolves in different namespaces. In
OrderedCompositionComplex.boundary_squared, it is the adjacent-merge map on
ordered nonzero vector tuples. In ProductChainProperInterval.boundary_squared,
it is alternating vertex deletion on strict chains. The former composite has
type Terms m (n+2) -> Terms m n; the latter has type Chains m (n+2) -> Chains m n.
These are different basis types and different linear maps. Their identification
requires the cumulative-sum comparison and a grading shift; they are not
definitional equalities. For example, for r=1, m=(2), the merge boundary at n=0
is zero from the single-block space to the zero empty-tuple space; the interval
boundary at n=0 sends the unique vertex (1) to the nonzero empty-chain generator.
Consequently importing the deletion theorem cannot directly replace the merge
square-zero obligation.

Repaired the flagged signature by fully qualifying both merge boundary maps,
binding r explicitly in each application, and explicitly typing zero as a map
between the fully qualified OrderedCompositionComplex.Terms modules. The theorem
name and mathematical statement stay unchanged. No second deletion theorem is
introduced; the existing ProductChainProperInterval.boundary_squared remains
imported through the owning definition dependency. All proofs remain sorry, as
required for stage 2. No source or unit statement correction is needed.

Second reading by Q104 for this repair: with both modules and the item open,
the flagged theorem is precisely the item's clause "These maps square to zero"
for its displayed merge differential, with every r, m and n permitted. The
fully qualified source and target show which complex is being constructed.
At n=0 the zero merge map still makes the composite zero; at m=0 and r=0 the
same basis and grading conventions remain. The chain constructor still consumes
this exact obligation. The comparison, dimension formula, finite terms and
acyclicity statements, and the new interval definition node are unchanged.
The previously recorded clause-by-clause correspondence continues to apply.

Repair validation (2026-10-23): prescribed scompile.py compiled the repaired
module cleanly in sandbox mode (2.0 s) and library mode (1.9 s). The node's main
lean.statement was checked byte-for-byte against the unchanged homology signature;
all Lean lines meet the 100-character limit. The repair changes the merge
square-zero signature's qualification and type annotations, plus the item's
lean.note and this report; all other declarations and node fields are retained.
