## What changed

Proved IsLocalRing.depth_eq_projectiveDimension_add_depth in
Sheaf.RingTheory.AuslanderBuchsbaum with four proved private helpers and no new
modules. The returned delivery duplicated three already existing private helpers.
This repair removes all three duplicate declarations and exposes their originals
in the unclaimed module Sheaf.RingTheory.CohenMacaulayDepthFirstTerm, then adds a
proof-only import of that module. The originals keep identical signatures and
proofs; only their visibility and explanatory docstrings change. A finite free
resolution and the depth lemma give depth R <= pd M + depth M.
For the reverse inequality, choose a maximal module-regular sequence rs and use
Mathlib ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular over
R itself. The resulting finite quotient has projective dimension pd M + depth M;
the minimal-resolution last-minors argument bounds that dimension by depth R.
This avoids reducing the coefficient ring and avoids Tor comparison.

The Lean module universe is repaired from Type v to Type (max u v), matching the
ordinary projectivity and bounded-resolution interfaces the declaration uses.
All mathematical assumptions and the conclusion stay the same. The downstream
importer Sheaf.RingTheory.UniformPerfectQuotientBound now has a completed proof
with one application of this theorem; its ring and module use the same universe,
so that application needs no adaptation. The sole existing direct consumer of
CohenMacaulayDepthFirstTerm is CohenMacaulayFreeResolutionMCM, which compiled
unchanged in 2.3 seconds against the exposed helpers. A separate check reproduces
the exact universe and application in UniformPerfectQuotientBound. Its full
current source could not be checked yet because the published build lacks the
unrelated BoundedFiniteProjectiveResolution.olean imported by that consumer. No target signature or definition changes.
The change records are coord/changes/auslander-buchsbaum-module-universe.md
and coord/changes/auslander-buchsbaum-depth-helper-reuse.md.
The existing DAG node and theorem docstring now describe the proof actually checked.

LeanFinder, Loogle and grep searches found no Auslander–Buchsbaum depth formula.
The pinned Mathlib source supplied its quotient-by-regular-sequence projective
dimension formula. Stacks algebra.tex Tag 090V was read at lines 27229 onward;
its minors bound and syzygy inequalities remain in the proof. The unit record
sk-thm-properbasechange realizes no step by this node, so this shorter node route
preserves every unit statement and realized step.

## Proved and sorry left

Closed the original hole in IsLocalRing.depth_eq_projectiveDimension_add_depth
(node lem-weil-pbc-auslander-buchsbaum). Added zero holes; split off zero theorems.
There are zero sorry occurrences in both changed Lean files. All private helpers
are proved. The visibility repair itself closes zero additional holes and adds
zero holes; the retained formula proof closes the original one hole. This is a
proof of the formula with a universe-interface repair,
not a decomposition. The four remaining private helpers are depth_cokernel_ge,
projectiveDimension_eq_nat, depth_le_resolution_length_add_depth, and
projectiveDimension_le_depth_ring. The three existing imported helpers are
IsLocalRing.depth_equiv_local, IsLocalRing.depth_subsingleton, and
IsLocalRing.depth_free_ge in CohenMacaulayDepthFirstTerm. Their proofs are unchanged.

## No longer needed

Removed proof imports from the original library module:

- Sheaf.RingTheory.DepthQuotSMulTop
- Mathlib.Algebra.Module.Projective
- Sheaf.Algebra.ProjectiveDimensionWellDefined
- Mathlib.Algebra.Homology.ExactSequence
- Mathlib.Algebra.Module.FinitePresentation
- Mathlib.RingTheory.Flat.Basic
- Sheaf.Algebra.Homology.FlatResolutionTorComparison
- Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
- Sheaf.RingTheory.DepthOverQuotientRing

Also removed Mathlib.RingTheory.Regular.Flat from the returned delivery, since
the reused finite-free depth lemma supplies everything that import was used for.
The three duplicate private helper declarations are pruned from AuslanderBuchsbaum;
all applications now resolve to the existing public helpers in
CohenMacaulayDepthFirstTerm. No module is withdrawn.

The quotient-ring induction is replaced by Mathlib's projective dimension formula
for a quotient by a module-regular sequence over the original ring. Thus its depth
drop, change-of-rings depth, reduction exactness and Tor-comparison obligations
are not used by this proof. Explicit projective-dimension well-definedness is
replaced by Nat.find and the resolution/Ext comparison. Images of the resolution
terms are finite by surjectivity, without the separate submodule-finiteness lemma.
Freeness and exactness
remain mathematical ingredients through the retained resolution APIs. The old
Tor-comparison tool_uses approval is withdrawn. Removed declared proof dependencies:

- lem-weil-pbc-depth-drops-by-one
- def-weil-pbc-projective-module
- lem-weil-pbc-projective-dimension-well-defined
- def-weil-pbc-noetherian-ring
- lem-sc-affine-standard-cover-finite-free-local-fp-flat
- lem-pc-flat-resolution-tor-comparison
- def-weil-pbc-module-chain-complex-homology
- lem-weil-pbc-depth-over-quotient-ring
- lem-weil-pbc-noetherian-submodule-finite

These modules/nodes may still be needed by other parents; this report claims their
removal from this proof only, not global unreachability. Mathlib's finite-free
flatness facts remain available through Regular.Flat rather than the removed
standalone imports. Added proof dependencies are DepthExt and the existing
BoundedProjectiveResolutionDimension comparison. No new node is required for
proved private glue or exposing existing proved helpers; the Mathlib quotient
dimension theorem is cited directly
in the proof step where it is applied.

## Where the brief, the DAG or earlier work was wrong

The returned delivery at bd48fd255 duplicated three private helpers from
CohenMacaulayDepthFirstTerm. The landing check correctly rejected that duplication.
Importing the module alone would not make private declarations accessible; this
repair exposes the originals and imports them, without reproving the statements.
Earlier reporting also said UniformPerfectQuotientBound was still sorry; current
main has its completed proof and an actual application. The application is
checked separately; the full consumer check awaits its unrelated missing
BoundedFiniteProjectiveResolution compiled artifact.

The original unrestricted Type v interface did not fit the declared minimal finite
free resolution theorem or the bounded-resolution/projective-dimension comparison,
both of which require ModuleCat.{max u v} R. The change record documents the repair
and all consumers. This is a size-interface issue, not a counterexample to the
mathematical Auslander–Buchsbaum theorem.

The plan required substantially more change-of-rings and Tor machinery than the
shorter route needs. The Mathlib regular-sequence quotient formula makes that
part of the plan unnecessary. The proof handles e=0, empty maximal regular sequences,
zero free terms and zero intermediate syzygies: subsingleton modules have infinite
depth, and zero-left-term short exact sequences are treated by a linear equivalence.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
