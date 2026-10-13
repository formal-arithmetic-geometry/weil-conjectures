## What changed

Proved `WeilConjectures.DerivedTotalResolution.total_resolution_element_finite_support`
in `Sheaf.Paper.TotalResolutionCycleFiniteSupport` without changing its signature.
Added proof-only imports `Mathlib.LinearAlgebra.DFinsupp` and
`Mathlib.Algebra.Category.ModuleCat.EpiMono`. The linear sum from the dependent
finite-support vectors of nonpositive columns is epi by the total coproduct's
universal property: its cancellation equation tests on singleton vectors, and
positive-column terms are zero. Epimorphisms of modules are surjective. Bounding
the support by its finite supremum yields the required range sum. Updated the
node's proof and proof_origin to describe this argument. Added the missing
copyright and module docstring. The second reading aligned the theorem
docstring with the direct cancellation proof.

Searches used LeanFinder for coproduct finite sums, Loogle for `DFinsupp.lsum`,
and grep for epimorphism surjectivity and support-sum lemmas. No library duplicate
was found. The proof uses Mathlib directly and introduces no helper theorem.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.DerivedTotalResolution.total_resolution_element_finite_support`
(node `aux-total-resolution-cycle-finite-support`). No holes remain in the item;
no holes were added or split off. Local compilation completed without warnings.
The bound works for empty support (`r = 0`), and the argument also includes the
zero ring, the zero bicomplex, and every integer total degree. No cycle condition,
vertical boundedness, or horizontal exactness is used.

## No longer needed

None. No imports, nodes, or modules were removed. The original node had no proof
dependencies; the proof still requires no Sheaf or WeilConjectures dependency.
No blueprint unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's coproduct/direct-sum identification can
be implemented with only surjectivity, proved directly by cancellation. There is
no need to construct a categorical isomorphism or reindex an integer-supported
vector. The original module lacked a module docstring; this is now supplied.

## Second reading by D2

1. PASS: diffed the only delivered module and node against the repository.
   The existing theorem signature, variables, namespace, visibility, and all
   definitions are unchanged byte for byte. No change record is needed.
2. PASS: local compilation is clean. A scratch copy with `#print axioms` reports
   only `propext`, `Classical.choice`, and `Quot.sound`. No sorry or prohibited
   declaration occurs. The finite-support witness comes from a proved
   surjectivity theorem, not an unproved existence assertion.
3. PASS: no statement was added or split off. Reviewed empty support (r=0),
   zero modules and the zero ring, arbitrary total degree, and the boundary
   column p=0. The argument needs no additional assumptions.
4. PASS: read top down and checked Mathlib's ModuleCat coproduct construction,
   dependent-sum lemmas via Loogle, and independent coproduct-generation searches
   via LeanFinder and source grep. No shorter matching library declaration was
   found: the available constant-family coproduct theorem has stronger
   assumptions, while range/iSup lemmas still need the generation argument.
   Both new imports are proof-only and needed. Compiled without the explicit
   Finset import, but retained its original public visibility: the dry-run
   preflight requires an interface change record for its removal. The old
   proof_deps was empty, so no DAG
   dependency is retired. The unit's realized fields name no affected node;
   its statement and route are kept.
5. PASS: the node's proof and proof_origin accurately describe singleton
   cancellation, positive-column vanishing, epi-to-surjective conversion, and
   extension of the support sum to the bounded range. Its empty proof_deps agrees
   with the absence of project proof dependencies. No new node is needed.

Changed only the theorem's natural-language proof,
which now follows the actual epi argument without claiming a constructed
coproduct isomorphism. The Lean proof itself needed no repair. Closed one hole,
added zero holes, and split off zero statements.
