## What changed

Retired the duplicate Sheaf.AlgebraicGeometry.RefinementPreservesFiniteLisse module in
favor of the existing proved source declaration with the same name and elaborated type.
Changed the sole direct consumer, Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement,
to import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse. Its statement,
proof body, public imports, and visibility are unchanged. No source-library file is edited.

Reattached lem-weil-pbc-refinement-preserves-finite-lisse to the source declaration,
recording its actual current signature. Updated the parent node
lem-weil-pbc-irreducible-refinement to document its upstream application while retaining
the same mathematical dependency. The local IsLisseEtaleSheafOfSets predicate is an
abbrev of IsFiniteLocallyConstantSheafOfTypes, so this requires no added hypothesis or
comparison theorem. The current kept-twins inventory had conservatively retained this
pair because the source restated the result; the compilation probe resolves that concern.

Change record: coord/changes/refinement-preserves-finite-lisse-upstream.md.

## Proved and sorry left

The assigned module already had zero sorries and compiled unchanged. Holes closed: 0.
Holes added: 0. Holes remaining in delivered Lean modules: 0. Split off: 0.
This delivery claims duplicate-module pruning, not a new proof of an old hole.

AlgebraicGeometry.Scheme.refinement_preserves_finite_lisse, node
lem-weil-pbc-refinement-preserves-finite-lisse, remains fully proved in the adopted
source module. A Lean probe applies it directly to the exact local signature, and
#print axioms reports precisely propext, Classical.choice, Quot.sound.
The adapted direct consumer and the unchanged transitive consumer both compile with
the replacement proof import. Axiom probes for exists_irreducible_refinement and
exists_irreducible_lisse_stratification likewise report exactly the three allowed axioms.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/RefinementPreservesFiniteLisse.lean through
deleted.txt. Replace its only direct import in IrreducibleLisseRefinement by the
upstream module. The six duplicate private helper proofs disappear with that module;
the existing upstream private helpers provide the same argument.

The retired file's two public imports (WeilConjectures.AlgebraicGeometry.EtaleSheaves
and WeilConjectures.ConstructibleSheaf.Refinement) and four private imports
(WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction,
WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm,
WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits, and
WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison) are retained
by the unchanged source proof. None of those modules or dependency nodes is claimed
unused. The preservation node and every one of its five proof dependencies stay.

The sole DAG parent still uses the preservation node, now attached to the upstream
proof. The unit route and realized steps stay. The transitive consumer
Sheaf.AlgebraicGeometry.IrreducibleLisseStrata needs no edit. No adopted-source
declaration is removed, replaced by sorry, or otherwise changed.

## Where the brief, the DAG or earlier work was wrong

The dispatcher assigned an item whose current proof has no holes; there is no current
return or rework row requesting a definition repair. Rather than submit a no-op, this
delivery removes its unnecessary duplicate implementation using the shortest existing
proof. The node's lean.statement also still spelled the obsolete predicate
IsFiniteLocallyConstantEtaleSheafOfSets, whereas the current local signature uses the
abbrev IsLisseEtaleSheafOfSets. Its attachment now records the retained source signature
verbatim. The mathematical statement and all target statements remain the same.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
