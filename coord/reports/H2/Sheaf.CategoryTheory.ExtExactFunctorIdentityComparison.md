## What changed

This is the listed upstream-review #1424 repair, rather than a new proof item.
The checked-out module already proves `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison`
and its private helper `CategoryTheory.Abelian.Ext.commShift_of_localization` without holes.
Retained the direct proof using Mathlib's `LocalizerMorphism.equiv_smallShiftedHomMap`.
Added proof comments explaining the pinned API mismatch and the private helper's downstream use.
All signatures, visibility, imports and proof terms remain unchanged.

The requested derivation from `mapExactFunctor_eq_of_iso` and `mapExactFunctor_id` cannot be
written against the pinned library: neither declaration occurs in Mathlib's Ext/Map.lean,
lean/Sheaf, or lean/WeilConjectures. `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map`
contains degree-one vanishing criteria, not these comparison lemmas. The existing proof uses the
underlying Mathlib localization API directly, in arbitrary degree and without EnoughInjectives.
Loogle returned unknown identifier for the proposed iso lemma; LeanFinder returned
`mapExactFunctor_hom`, the map definition and additive/linear wrappers; msearch grep found no
proposed iso or identity API. Actual searches are recorded in searches.jsonl.

The private localization helper is retained because
`Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity` imports it with `import all` and
calls it at line 56. The importer was copied unchanged under scratchpad/second-reading/ solely for a compile
against the sandbox module, and is not an adapted module or part of this delivery.

## Proved and sorry left

Already proved on the supplied baseline:
- `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison`.
- `CategoryTheory.Abelian.Ext.commShift_of_localization` (private).

Holes closed in this delivery: none (the baseline has zero holes).
Holes added: none. Holes remaining: none. Split-off statements: none.
No net proof progress is claimed for this repair.

The main theorem works at n = 0 by the same shifted-morphism argument, with no positive-degree
assumption. Zero classes and zero objects introduce no exception. The termwise component check
covers degree zero by simplification and every other degree by the zero object's uniqueness.
The natural isomorphism is arbitrary; it is not replaced by an equality or a chosen witness.

## No longer needed

No imports, nodes or modules are newly pruned. The sole import is
`Mathlib.Algebra.Homology.DerivedCategory.Ext.Map`, needed by the statement and proof.
The proof continues not to need `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`
or an injective-resolution route. These were already absent from the baseline.
Do not prune `commShift_of_localization`: the raw pullback identity module calls it.
The node's current two-step route remains accurate; no node fields change.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief says the module contains sorry, but the supplied source contains none and
compiles cleanly. coord/repairs.txt instead lists upstream review #1424, whose suggested API is
absent in the pinned version. This is a version/interface mismatch, not a false statement.
The baseline already carries the direct localization repair recorded in the node's proof_origin.
The current downstream source directly calls the private helper; retain it.

## Second reading by H2

1. Interfaces: PASS. Read the full module and its diff against the repository version.
   Only comments differ; both existing declaration signatures are byte-for-byte unchanged,
   as are visibility, imports and proof terms. The declaration-table check confirms no
   statement or interface changes. No change record is required.
2. Proof and trust: PASS. The delivered module compiles locally without warnings (2.2 s).
   A scratch copy with `#print axioms` for `exactFunctorIdentityComparison` and the private
   `commShift_of_localization` reports exactly propext, Classical.choice and Quot.sound.
   There are no sorrys, forbidden declarations or data constructions from open existence
   theorems. Compiled the unchanged HigherDirectImageRawPullbackIdentity importer against
   the scratch-built delivered module in import order; it passes (40.0 s), including its
   `import all` use of the private helper.
3. Split statements: PASS, vacuous. No declarations or nodes are added, and no statements
   are split off. At n = 0 the identity is ordinary naturality for a morphism; for zero
   classes or zero objects it is the zero equality. Arbitrary e is retained. The degreewise
   single-complex check handles i = 0 directly and every i != 0 by the zero object.
4. Route and pruning: PASS. Read Ext.Map and the localization comparison lemma. Fresh
   LeanFinder search for conjugating the Ext action by an identity comparison returns
   mapExactFunctor_hom and map/identity-composition wrappers, not the requested comparison.
   Restricted msearch grep finds only equiv_smallShiftedHomMap; direct searches in
   lean/Sheaf and lean/WeilConjectures confirm the proposed iso/identity API is absent.
   Loogle's Ext/NatIso query reports an unknown NatIso identifier, so it supplies no evidence.
   The current direct localization proof is justified against the pinned API. The only
   public import supplies Ext and mapExactFunctor used in the statement and is necessary.
   No old proof dependency is newly unused: both are Mathlib leaves reached by that import.
   No newly pruned node or module is omitted from No longer needed. Read sk-thm-p1.json:
   its realized statement and steps are unchanged, and this auxiliary proof bypasses none.
5. DAG consistency: PASS. The existing node's two steps match construction of the
   shift-compatible termwise comparison, equiv_smallShiftedHomMap, the single-component
   identities hx/hy and cancellation in shifted morphisms. Its proof_deps are the exact
   functor localization and Ext Mathlib leaves; its proof_origin describes this same route.
   No node fields need changing and no new-node checks apply.

Second reading changed only this report: added these independent checks, located the
unchanged importer test explicitly in scratchpad, and replaced the unverified historical
B4-return reference with the directly checked downstream call (the current B4 returns file
contains no identity-comparison entry). The Lean proof was already correct and is retained.
Holes closed: none; holes added: none; holes left: none. This is a reviewed repair with
zero net proof progress, not a new proof or decomposition.
