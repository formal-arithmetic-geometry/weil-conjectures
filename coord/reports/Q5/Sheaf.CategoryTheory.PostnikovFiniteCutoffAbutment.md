## What changed

Proved `DerivedCategory.postnikov_finite_cutoff_abutment` in
`Sheaf.CategoryTheory.PostnikovFiniteCutoffAbutment`, with its original signature and
all existing data definitions unchanged. The proof establishes cutoff invertibility
from the canonical tail triangle, shifted support and convergence, the actual image
filtration and its endpoints, canonical graded and arbitrary late-page comparisons,
and all naturality equations.

The additional helpers are private and completely proved. Proof imports use the
existing half-plane convergence and derived-couple functoriality results.
The private quotient helpers adapt the proved argument in
`WeilConjectures.CategoryTheory.AbutmentFinitePageComparison`;
the cycle and boundary recurrences give stabilization directly. The stronger public
finite-page comparison theorem and its module are not imported.
The node's proof, proof dependencies and proof origin now describe these arguments.
No source-library module, public signature, target statement or unit route changes.

## Proved and sorry left

Closed one hole: `DerivedCategory.postnikov_finite_cutoff_abutment`
(node `lem-per-postnikov-finite-cutoff-abutment`).
Added zero holes. Zero holes remain in the item, and none are split off.
All private helpers are proved.

Validation: `lcompile.py` compiled the complete module in 14.2 seconds with exit
code 0 and no warnings. The theorem signature and all original data definitions
were checked byte-for-byte against the library; zero `sorry` tokens remain.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.ExactCoupleMorphism`.
The node `lem-sp-couple-morphism` is no longer needed by this proof: its generic
infinite-page map comes directly from `lem-sp-derived-couple-functoriality`, while
image restrictions, the abutment equation and graded compatibility are proved here.
Removed the obsolete top-level `tool_uses` entry `lem-sp-couple-morphism`.
This does not withdraw that module or claim it is unused by other parents.
No other original declared dependency is pruned, and no Lean module is deleted.

## Where the brief, the DAG or earlier work was wrong

The planned `coupleMorphism` declaration in `Sheaf.CategoryTheory.ExactCoupleMorphism`
is inside the upstream-sync `TAKEN OUT` comment, so it cannot be applied. Its
underlying proved `derivedCoupleFunctoriality` declaration suffices and works for
the particular limiting subobjects already chosen by half-plane convergence.
The remaining map equations are proved directly, rather than selecting new
abutment or graded-comparison witnesses from a separate naturality theorem.
No mathematical statement repair was necessary.

Delivery preflight identified added file-wide commands. The elaboration option
is now scoped to individual proof declarations, and `omit` prefixes on private
helpers were replaced by explicit category parameters; no file-wide command or public interface change is delivered.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
