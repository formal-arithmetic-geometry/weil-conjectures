## What changed

Replaced the body of `AlgebraicGeometry.Scheme.adicResidue_isIso_of_residue` without
changing its statement. Added three proved private helpers: exactness of the actual
universally specified scalar extension; closure of local completeness under cones,
proved directly from its internal-Hom definition; and zero detection from the existing
normalized quotient homotopy-limit cone. The final proof completes the morphism to a
triangle, kills its residue cone, inducts on quotient exponents, reconstructs the zero
cone, and applies the distinguished-triangle isomorphism criterion.

Added the proof import `Sheaf.Paper.AdicCompleteReductionCone` and imports for the
cochain-model and internal-Hom exactness APIs. Added a new module
`Sheaf.Paper.AdicResidueVanishingSuccessor` for the coefficient-triangle induction step.
This is a decomposition, not a net hole reduction. The new statement is independent of
completeness, is about one object and two consecutive reductions, and has neither a
morphism nor an invertibility conclusion. Its induction and all completion/triangle
assembly are actual Lean proofs in the assigned module.

The declaration-scoped instance-search attribute matches the existing complete-cone and Hom-section
modules to avoid the expensive generic essentially-small sheafification search. It has no
exported effect on consumers.
No definitions, target signatures, source-library files or public imports were changed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.adicResidue_isIso_of_residue`
(node `lem-sfb-adic-complete-residue-conservative`). The item has zero textual holes.

Added one hole:
`AlgebraicGeometry.Scheme.adicResidue_vanishing_successor`
(node `lem-sfb-adic-residue-vanishing-successor`), with its complete coefficient-triangle
proof and Stacks Tag 0G1T source in the docstring and node. No other holes are added.
The imported, previously existing `adicResidue_complete_reduction_cone` remains unproved.
Its reconstruction interface is used directly rather than duplicated.

Validation: `lcompile.py --all` completed with exit code 0 and no warnings:
`AdicResidueVanishingSuccessor` in 15.9 s and `AdicCompleteResidueConservative` in 12.8 s.
Static declaration comparison reports no changed signatures, no removed declarations,
no changed public imports, and no exported instance/attribute risks.

Net holes closed minus added: zero. This delivery proves the assembly and leaves the
finite coefficient calculation as the strictly smaller next item.

## No longer needed

No baseline import was removed. No source declaration or module is withdrawn.
The assigned node no longer directly invokes
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`: its use is encapsulated by the existing
`lem-sfb-adic-complete-reduction-cone`, so it remains needed transitively.
The assigned node no longer directly invokes
`lem-weil-pbc-constant-module-section-properties`,
`lem-sf-derived-homology-long-exact`, or
`lem-weil-pbc-constant-completion-equivalence`: their coefficient-induction uses are
recorded on the successor node. Constant completion definitions are still re-exported
by the unchanged public statement import, and the complete-cone node still depends on
the completion equivalence. None of these dependencies is claimed globally pruned.
`RingedCompleteTriangulated` and the finite generating-list reflector are unnecessary
for cone closure here: simultaneous vanishing of exact internal-Hom tests proves it
directly, with no generator construction.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. The old plan contains the correct coefficient induction, but its
existing declarations do not state that induction at the arbitrary-Noetherian-ideal,
localized completed-coefficient endpoints. The DVR first-reduction theorem and the
one-point nilpotent upper-bound theorem cannot specialize to those endpoints.
The successor module isolates exactly this missing calculation. The unit route and
all public statements are preserved. Edge cases checked in the mathematical argument:
J=0, J=top, Q=0, n=0, and unbounded Q. The induction requires derived reassociation;
ordinary tensor of an arbitrary acyclic quotient complex would not suffice.

The original source prose groups Tag 099M under Algebraization; the local Stacks tag
index places 099M at proetale-lemma-naive-completion. The actual finite-vanishing source
is More on Algebra Tag 0G1T. Existing docstrings are preserved, and the new node records
the precise source labels.

## New nodes

`lem-sfb-adic-residue-vanishing-successor` states just the consecutive quotient
vanishing step. Its proof tensors the exact sequence of consecutive ideal powers
with a flat-term K-flat representative; derived reassociation kills the left term,
the inductive hypothesis kills the right, and exact cohomology kills the middle.
The node records LeanSearch, Loogle, and source grep searches, and the comparison with
DVR-only and point-site alternatives. It inherits the item's chapter and unit.
The conservative command-interface checker sees the proof context changes; these are
recorded in `coord/changes/Y2-adic-residue-conservative-proof-context.md`. The public
interface of every existing module is unchanged. The new statement has its own node
and module.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
