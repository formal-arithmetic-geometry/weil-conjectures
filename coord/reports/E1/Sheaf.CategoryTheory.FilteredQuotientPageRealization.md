## What changed

Replaced the earlier rejected decomposition with two new modules, each containing one
public intermediate theorem: `Sheaf.CategoryTheory.FilteredQuotientCanonicalFunctor`
and `Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure`.

The item's original declaration signature, public imports and docstring are unchanged.
Its complete Lean proof chooses the uniquely specified representative differentials
from `filteredComplex_page_differential_exists_unique`, applies the canonical-functor
lemma, and applies the pointwise structural lemma to the same witnesses. The structural
lemma explicitly requires every page comparison to commute with the representative
differential. This supplies the missing hypothesis responsible for the previous
sign-change counterexample. Its conclusions involve only page complexes, so it need
not constrain the successor homology isomorphisms of the supplied spectral sequence.

Both new modules compile, and the combining proof compiles. A declaration-local unused
variable linter setting suppresses warnings on unused proposition binders in the
unchanged original signature. No definition, existing statement, visibility, target,
or other held module was changed. The parent node's proof route now agrees with the
Lean proof; new nodes have their own creation records, not copied review records.

## Proved and sorry left

Hole closed in the item: `CategoryTheory.filteredQuotient_page_realization`
(node `lem-sp-filtered-quotient-page-realization`). There are no local sorries in that
module. The combining proof is complete, conditional on the two new intermediate
theorems; this is a decomposition, not a sorry-free proof of the realization.

Holes added and left:

- `CategoryTheory.filteredQuotient_canonical_functor`
  (node `lem-sp-filtered-quotient-canonical-functor`): construction of the natural
  spectral-sequence functor with all representative differentials fixed; no first
  connecting map or exact-couple realization is asserted.
- `CategoryTheory.filteredQuotient_canonical_structure`
  (node `lem-sp-filtered-quotient-canonical-structure`): pointwise first differential
  and exact-couple comparison under explicit differential compatibility; no functor
  or naturality is asserted.

Both proofs are exactly `:= by sorry`, in separate new modules with full proof
explanations and matching nodes. One original hole closed, two holes added: net -1
before any closure pruning. No claim of net hole reduction is made.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.CategoryTheory.ExactCoupleMorphism` and node `lem-sp-couple-morphism`:
  the new functor construction uses quotient maps and canonical successor homology,
  and does not require half-plane convergence or abutment morphisms.
- `Sheaf.CategoryTheory.FilteredComplexPositivePages` and node
  `lem-sp-filtered-complex-positive-pages`: existential page isomorphisms alone
  do not pin their differential or successor homology normalization. The construction
  instead starts with the existing unique representative differential and successor
  cycle/boundary descriptions.
- `Sheaf.CategoryTheory.ExactCouple` and `Sheaf.CategoryTheory.Filtration`:
  these were redundant direct imports; the original public statement imports still
  expose both. Their definition nodes remain needed for statements and the new
  structural argument.

The original nodes `def-sp-filtered-complex-subquotients`, `def-sp-filtration`,
`def-sp-exact-couple` and `def-sp-spectral-sequence` are no longer direct proof
steps of the parent. They remain statement dependencies and dependencies of the new
lemmas; their modules are not claimed to be globally pruned. The two proof-only
modules above may remain reachable elsewhere; project-wide pruning is the
maintainer's queue computation.

Removed the earlier attempt's uncommitted naturality and structure helper node files
and its obsolete change record. They are not nodes on the repository base and are not
included in this delivery. There are no changed unit or chapter records.

## Where the brief, the DAG or earlier work was wrong

The earlier helper asserted structure for arbitrary page isomorphisms. Negating a
comparison at one end of a nonzero rational first differential violates its claimed
conclusion. The replacement's hypothesis hd excludes exactly this case: it forces
the transported differential to equal the uniquely specified representative map.
Even a natural sign change must satisfy hd on every page and bidegree. If it does,
the new structural conclusions transport correctly too.

Edge cases checked mathematically: the zero complex and zero graded pieces have zero
quotients and differentials; a filtration concentrated in one degree has no nonzero
inter-filtration differential; the rational two-term identity complex with two-step
filtration from the previous counterexample has d1 equal to the representative map,
and a sign change at only its source fails hd. All r in the new statements satisfy
r >= 1. Arbitrary changes to E.iso cannot affect the structural lemma, whose
conclusion contains only its pages and differentials.

Read Stacks Tag 012K online, including Lemmas 12.24.2, 12.24.3(1), and 12.24.4:
https://stacks.math.columbia.edu/tag/012K . The referenced local source files are
absent on this machine. Lemma 12.24.2 explicitly gives the componentwise construction
without countable sums; Lemma 12.24.3 states a countable-sum hypothesis, but its proof
uses only the componentwise representative formula. The new nodes explicitly record
an agent-written componentwise expansion of this argument, rather than pretending a
stronger theorem is printed verbatim in the source. No new source checkout was written.

Mathlib searches found homology and connecting-map naturality and the spectral-sequence
morphism structure, but no filtered quotient functor or this exact-couple comparison.
LeanSearch returned an internal server error; its unavailability is recorded along
with successful LeanFinder, Loogle and source searches. The unit's realized statement
and steps are untouched; this is a refinement below the unit level.

## New nodes

`lem-sp-filtered-quotient-canonical-functor`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-quotient-canonical-functor.json`,
records the functor construction from the actual representative differentials. Its
proof explains normalization of the successor homology comparison, filtered-map
restrictions and quotient descents, differential and homology commutation, and
identity/composition. It lives in `FilteredQuotientCanonicalFunctor.lean`.

`lem-sp-filtered-quotient-canonical-structure`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-quotient-canonical-structure.json`,
records the pointwise structural argument, with the explicit compatibility missing
from the rejected helper. Its proof constructs the homology exact couple, identifies
its derived differentials on representatives, fixes eH using the epic representative
equation, and transports to the supplied pages. It lives in
`FilteredQuotientCanonicalStructure.lean`.

The structural module retains ExactCoupleConvergence because it defines initialG;
no abutment or stabilization declaration is used.

Neither new theorem changes what existing importers see, because both are imported
only for the proof. No change record or forced adaptation is needed.

## Second reading by E1

1. Interface preservation: compared the delivered realization module against the
   repository with diff and compared the original theorem signature byte for byte.
   The signature, public imports, visibility and existing docstring are unchanged.
   The only original-node fields changed are proof, proof_deps and proof_origin.
   There are no changed definitions, targets or forced adaptations. Verdict: pass.

2. Proof and trust: compiled all three delivered modules in import order using
   lcompile.py; no errors or warnings. A scratch copy with #print axioms for
   filteredQuotient_page_realization, filteredQuotient_canonical_functor and
   filteredQuotient_canonical_structure reports exactly propext, Classical.choice,
   Quot.sound and sorryAx. The last is expected: the two named helper theorems are
   still open. There are precisely two literal sorry bodies, both public theorems,
   and no definitions or forbidden declarations in the delivery. The chosen D
   comes from unique existence of the full differential structure; this is not
   an arbitrary witness from mere existence. The parent combines hd, hnat and the
   pointwise comparison with the same S and eZ. Verdict: valid decomposition,
   one hole closed and two added, not a net proof gain.

3. New statements: read both helper signatures, their docstring arguments, their
   nodes, FilteredComplexPageDifferential, the successor cycle-cover and boundary
   image statements, and the exact-couple indexing. Read Stacks Tag 012K online,
   specifically 12.24.2, 12.24.3(1) and 12.24.4. The functor lemma asserts quotient
   pages and naturality, but no first connecting map or exact-couple comparison.
   Its fixed D has the defining representative equation, so hd fixes all page
   differentials; canonical successor-cycle comparisons are needed to make its
   quotient maps spectral-sequence morphisms. The structural lemma fixes one U
   and asserts only pagewise comparisons, not a natural functor. Its hd hypothesis
   is essential; E.iso does not appear in the conclusion, so no compatibility
   with that independently supplied data is required. At s=0 the reindexing
   (P,Q)=(2p+q,-p) sends (2,-1) to (1,0); at general s it sends (s+2,-s-1)
   to (s+1,-s), exactly the displayed page differential. hH and epic z fix eH.
   Checked zero complexes, a single nonzero graded step, and the rational
   two-term identity complex with F^0=K, F^1 its degree-one term and F^2=0.
   In the last example d1 is the identity; negating just the source eZ violates
   hd, whereas simultaneous compatible sign changes transport both equations.
   Lemma 12.24.3's printed countable-sum hypothesis is not silently cited away:
   the helpers use the componentwise representative argument recorded in their
   docstrings and proof_origin. Searches with the different query 'spectral
   object of a filtered cochain complex and induced spectral sequence' found
   Mathlib's mapping-cone spectral object, not either quotient comparison.
   Loogle's quoted δ_naturality search found homology-sequence naturality,
   not the needed construction; two attempted fully qualified δ queries were
   unknown identifiers. Source searches in Sheaf, upstream CategoryTheory and
   Mathlib's spectral-sequence directory found the existing positive-page and
   page-homology results. Their existential isomorphisms do not expose the
   normalization required for functoriality, so neither supplies a one-line
   replacement. Both remaining statements are true, needed, and strictly part
   of the original argument. Neither is a same-statement relabelling. Verdict:
   pass; neither remaining construction is a few-minute closure.

4. Route and pruning: checked the parent reduction from the top down. It first
   uses the existing unique representative differential, then the two genuinely
   different intermediate constructions. New functor step 1 uses the successor
   cycle cover and successor boundary image exactly for the normalized homology
   quotient; restrictions and quotient descents then give maps, and cancellation
   gives naturality and the functor laws. Structural step 1 is the homology exact
   couple, step 2 is its representative induction, and step 3 pins eH and the
   connecting map. The No longer needed section covers all six old proof_deps,
   distinguishing removed direct proof steps from still-needed definitions.
   Original public statement imports remain. ExactCoupleConvergence is needed
   for initialG and pageCouple in signatures; HomologySequence for hS.δ.
   No unit or chapter record changes. The inherited unit sk-prop-av-pqf-finite
   is about proper quasi-finite morphisms and has empty realized lists; it does
   not describe this spectral-sequence item. This pre-existing metadata mismatch
   is reported here, not repaired by changing an unowned unit field. The
   blueprint ancestor thm-sp-spectral-object-yields and its construction route
   are retained. Verdict: pass for this delivery, with inherited metadata issue.

5. Node agreement: compared every recorded Lean signature with its module after
   whitespace normalization; all match. For each node, proof_deps equals the
   union of the proof steps' uses. The parent steps match choose D, obtain the
   canonical functor, and apply the structural comparison. New nodes have source,
   full proof plans, actual search records, creation records, chapter/unit,
   blueprint ancestry and Lean records. The original statement is unchanged.
   Found missing plan imports in the new functor module: its node named the
   successor cover and boundary image but the module did not import them.
   Added both as plain proof-only imports. Verdict: pass after repair.

Changed in this second reading: added the two missing proof-dependency imports
to FilteredQuotientCanonicalFunctor; added blueprint identifiers to both new
module docstrings; replaced the obsolete scratch axiom test with a test of the
current three declarations; documented the inherited unit mismatch. No theorem
statement or proof body changed. The report remains explicit about the net -1
decomposition and makes no claim that an entire module was globally pruned.
