## What changed

Proved `CategoryTheory.finiteCDDerivedUpperBound` with its signature unchanged.
Three proved private helpers establish right-acyclic replacements from the existing
07K6 declaration, the upper bound on mapped acyclic complexes by finite dimension
shifting, and the Kan universal property of a factorization through fully faithful
precomposition. The main proof uses the existing 06XN declaration and explicitly
composes Kan extensions to obtain the cochain-localization universal property.
Only the assigned Lean module and its proof node change. All new imports are proof-only.
The final module compiles cleanly through lcompile.py in 3.2 seconds; its signature
was compared with the original and is identical.

The proof follows Stacks `derived.tex`, Tag 07K7 (1) and (4)(c), read at lines
9977–10109, using the existing 07K6 and 06XN declarations. No Grothendieck or
K-injective-resolution assumption is introduced. The induction includes N=0 and
uses only cycles sequences at indices at least t.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.finiteCDDerivedUpperBound`
(node `lem-sf-finite-cd-derived-upper-bound`). Holes closed: 1; holes added: 0.
No `sorry` remains in the delivered module. No split-offs or new nodes.
The two existing imported declarations
`CochainComplex.exists_quasiIso_degree_zero_of_bounded_degree` and
`CategoryTheory.Functor.exists_rightDerivedFunctor_of_adapted_complexes`
remain the stated dependencies for subsequent workers; their modules are not edited.

## No longer needed

Removed these redundant proof imports:

- `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`

The full long-exact-sequence re-export is unnecessary: the source library's proved
`exists_rightDerived_δ_exact` suffices. The other imports are available transitively
through the retained imports. No planned mathematical dependency is removed: the
existing finite-CD source API already implements the cone and identity-family
arguments, and its acyclic short-exact-sequence API uses R^0F ≅ F. Thus no entire
DAG node is claimed pruned; no assertion of transitive module pruning is made.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned cone work is already proved in the source
library, so it is reused. For the upper bound, monomorphisms from the long exact
sequence suffice: an induction makes the cycles right-acyclic and kernel preservation
then proves exactness. This avoids constructing the cohomology isomorphisms proposed
in Step 6. The node's proof is updated to this implementation, retaining its dependencies.
The shared FullLongExactSequence module is a retired re-export after upstream sync;
its direct import is removed. No interface or definition changes, hence no consumer
adaptations or change records are needed.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
