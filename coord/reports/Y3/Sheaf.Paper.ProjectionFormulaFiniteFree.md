## What changed

Replaced the sorry in SheafOfModules.ringedProjectionFormula_finiteFree by a complete
Lean proof from the existing total-mate API and a new representative comparison.
The existing theorem signature, all its hypotheses, and its visibility are unchanged.
The proof constructs the exact representative isomorphisms used by
ringedProjectionFormulaArrows. It obtains the ordinary total mate isomorphism and
K-injectivity of its target from the arrow API, rewrites the derived mate by the new
comparison, and proves both original composite identities by inverse cancellation.
No target, definition, or existing intermediate statement has been changed.

Added Sheaf.Paper.ProjectionFormulaMateRepresentative with one public theorem and
updated the parent node to describe the actual reduction. Only the original public
imports remain public; the new comparison is a private proof import.

## Proved and sorry left

Closed the original hole in
SheafOfModules.ringedProjectionFormula_finiteFree, node
lemma-weil-pbc-projection-formula-finite-free, by a compiling proof from the named
comparison and the existing arrow declarations.

Added one hole:
SheafOfModules.ringedProjectionFormulaMate_representative, node
lem-weil-pbc-projection-formula-mate-representative, in
lean/Sheaf/Paper/ProjectionFormulaMateRepresentative.lean.
Its proof is exactly `by sorry`; its docstring gives the complete representative
argument, including the functorial resolution and counit calculation.
There are zero holes in the item module and one hole in the new module.
This is one decomposition, not a net proof: one original hole closed, one added,
net zero. No untracked local holes or data definitions have been added.

The new comparison does not assume finite freeness, boundedness, a strict-perfect
package or invertibility of the ordinary mate. It computes the specified derived
map with a K-flat flat-term coefficient and an explicitly K-injective tensor target.
The separate main proof supplies these hypotheses and the invertibility statement;
thus the new theorem is strictly a part of the argument, not the original theorem
under another name. Zero rank and zero complexes are covered by the same inverse
identities, without a positivity assumption.

## No longer needed

Removed private imports from the item module:

- Mathlib.Algebra.Homology.BifunctorShift
- Mathlib.CategoryTheory.Adjunction.Limits
- Sheaf.CategoryTheory.ModulePullbackTensorIso
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
- Sheaf.Algebra.Homology.KFlat
- Sheaf.Algebra.Homology.KFlatResolutionGeneral (moved to the comparison module)
- Sheaf.Paper.RingedTopoiCanonicalTensorPullback
- Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients

The parent proof no longer directly needs the planned coordinate, shift and
finite-product calculation or these proof dependencies:
def-pc-tensor-complex-sheaves,
lem-weil-pbc-ringed-topoi-module-pullback-tensor,
lem-weil-pbc-termwise-adjunction-homotopy,
lem-weil-pbc-right-adjoint-preserves-limits,
def-pc-kflat-complex, and
lem-pc-pre-derived-adjoint-functors-general.
The last node was also removed from the parent's tool_uses list, preserving the
order of the remaining approval. These nodes may remain needed by other library
proofs; no global unreachability is claimed.

The K-flat resolution dependency lem-pc-kflat-resolution is needed inside the new
comparison, not directly in the final inverse calculation. The new module privately
imports Sheaf.Algebra.Homology.KFlatResolutionGeneral for that proof. The canonical
derived tensor comparison and the arrow API remain needed. Their public availability
through the existing imports makes the separate private canonical-tensor import
redundant, but its node is not pruned.
No node realizing a blueprint unit statement or proof step has been bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing arrow API already states total-mate invertibility and target
K-injectivity for the bounded split-free coefficient package. Repeating the planned
finite-coordinate proof here would duplicate that available interface. The missing
glue is the representative identification in steps 4--6 of the expanded parent
proof; the short blueprint proof describes it as the counit becoming the identity
under the two identifications. Neither the imported declarations nor the repository
search supplied that identity as a theorem.

Four Mathlib searches (leansearch, leanfinder, loogle, grep) and source/blueprint searches are
recorded in the new node. LeanSearch found derived_counit and related comparison
lemmas; these supply the counit equations already assumed as canonicalAdj, rather
than the missing mixed tensor square. No existing mixed representative comparison
was found.
No statement is disputed. No consumer adaptation or change record is necessary:
all existing signatures and definitions are unchanged.

## New nodes

lem-weil-pbc-projection-formula-mate-representative isolates the computation of the
specified derived mate, with its complete source proof in the module docstring and
three matching DAG steps. To close it, formalize naturality of the mixed tensor
representatives using a functorial K-flat flat-term resolution, extend the canonical
pullback tensor square to an arbitrary first complex, and apply the derived
adjunction hom equivalence and the two assumed canonical counit equations. Work in
this session compiled the generic adjunction diagram chase, construction of the
functorial flat resolution, mixed representative naturality and normalization on
flat pairs in scratch files. Completing the canonical tensor square and specializing
the generic chase remains; those scratch files are not delivery dependencies.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
