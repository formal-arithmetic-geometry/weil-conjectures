## What changed

Proved `AlgebraicGeometry.Scheme.Modules.homotopyEquiv_single_cohomology_of_field`
without changing its signature. The private helpers `projective_of_field` and
`injective_of_field` reflect vector-space splitting along the proved global-sections
equivalence. Projective and injective lifts construct maps to and from the actual
single homology complex. Their reverse composite is exactly identity; their other
composite induces identity on homology.

Added the fully proved module `Sheaf.CategoryTheory.SplitCategoryNullHomotopy` and
its theorem `CochainComplex.nonempty_nullHomotopy_of_homologyMap_zero`, implementing
the boundary/complement contraction in any split abelian category. Its proof uses
Mathlib's exact-sequence lifting and null-homotopy constructors. All five new
imports of the item are proof imports. The existing public imports are retained.
Updated the item's proof, proof_deps and proof_origin to match the implementation.

Both modules compile without warnings through lcompile.py. Independent #print
axioms probes of both public theorems report exactly propext, Classical.choice,
and Quot.sound. The proofs handle arbitrary integer j, unbounded complexes,
acyclic complexes and zero homology; no finite-rank, boundedness or nonzero-object
hypothesis was added. All witnesses are chosen using proved lifting properties.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.homotopyEquiv_single_cohomology_of_field`
(node `new-field-complex-single-cohomology`).

Also fully proved the new theorem
`CochainComplex.nonempty_nullHomotopy_of_homologyMap_zero`
(node `lem-pc-split-category-null-homotopy`).

No sorry remains in either delivered module, and no new hole was added. This is
a complete proof, not a decomposition into new unproved intermediate statements.

## No longer needed

No original import, node or module was pruned: the item's original proof_deps were
empty and its three public imports support its existing statements. The new proof
does not construct a whole termwise-homology complex or transport complexes back
from vector spaces: it reflects projectivity and injectivity and works directly
with module sheaves. These were unnamed steps, so there is no named node to prune.
Redundant direct imports of ShortComplex.Exact, Projective.Basic and Injective.Basic
were removed from the new module; Homotopy already supplies them transitively.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. The old DAG described a
vector-space direct-sum construction but supplied no proof dependencies. Mathlib's
exact lifting API gives a shorter categorical implementation of that same
boundary/complement argument, keeping the unit route. The unit's realized statement
and step lists are empty, and no unit node is bypassed.

LeanFinder and grep found only the converse null-homotopy-to-homology statements,
and the source library's private semisimple-ring construction supplies only a
quasi-isomorphism, so neither closed this unbounded homotopy-equivalence goal.
LeanSearch returned Internal Server Error. The blueprint markdown is not present
in this machine's literature checkout; source provenance was read from the
existing node and its complete expanded proof. The new categorical proof is
explicitly marked as written by an agent.

## New nodes

`lem-pc-split-category-null-homotopy`, in
`dag/nodes/sec-picard-framework/lem-pc-split-category-null-homotopy.json`, states the
fully proved general null-homotopy lemma. It is strictly a part of the argument:
it assumes a given chain map with zero homology, has no field, degree or
concentration hypothesis, and constructs neither maps to a single complex nor
a homotopy equivalence. The item constructs and checks those maps itself.
Its proof is recorded in three explicit steps, uses only Mathlib, and its module
contains no sorry. No change record or forced adaptation is needed.

## Second reading by B2

1. Compared the delivered item module with the repository version. The target
   declaration signature is byte-for-byte unchanged; only its proof and
   proof-only imports changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; there are no
   errors, warnings, sorries, axioms, unsafe declarations, or hollow
   definitions. Verdict: pass.
3. Checked the split-off theorem against the category-theoretic construction:
   it is true, strictly weaker than the item, and needed to contract a map
   with zero homology. Searches found no existing duplicate. Verdict: pass.
4. Read the proof from the target downward. It uses the shortest available
   projective/injective lifting route and retains the unit route; no unused
   proof dependency was identified. Verdict: pass.
5. Compared both DAG nodes with the Lean declarations and proof steps. The
   new node records its source, proof, dependencies, and Lean declaration;
   the item node records the new dependency and revised proof origin. Verdict:
   pass.

Changed only the item proof/imports, added the proved helper module and node,
and documented the second reading. No statement or definition was changed.
