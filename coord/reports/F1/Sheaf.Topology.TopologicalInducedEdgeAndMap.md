## What changed

Proved `CategoryTheory.exists_topological_induced_edge_and_map` in
`Sheaf.Topology.TopologicalInducedEdgeAndMap`, preserving every existing binder,
universe, visibility and conclusion. Added a private, fully constructed terminal-section
representing equivalence. Constructed the induced cohomology transformation by applying the
exact inverse-image functor to Ext, then precomposing with the canonical map from KZ to
L(KX) and postcomposing with the counit. Constructed the terminal map by lifting the
free-generator presheaf transformation through sheafification, and proved its generator rule.
No arbitrary existence witness and no zero-map shortcut is used.

Added the proof-only import `Mathlib.Algebra.Homology.DerivedCategory.Ext.Map`.
Removed the redundant imports listed below. Updated the node's proof route and dependencies.
The public import removal is recorded in
`coord/changes/topological-induced-edge-imports.md`; no downstream adaptation is necessary.
The original named existential binder `edge` does not occur in the remaining conclusion;
its existing signature is preserved, with unused-variable lint disabled locally on the theorem.

Validation: launcher single-file compilation is clean. The delivery dry run also checks axioms
and unchanged signatures. The constructions do not impose nonemptiness of X or Z, exclude
degree zero, or require exactness of pushforward: only exactness of inverse image is used.
For the identity map the construction uses the unit/counit maps; for empty spaces the same
terminal-open equality and adjunctions apply. No new statement needs edge-case testing.

Searches run: msearch leanfinder for induced pushforward cohomology returned continuous
pushforward APIs; loogle for sheafifyLift returned its lifting and uniqueness theorems;
msearch grep found sheafifyLift and exact-functor Ext composition lemmas. Local rg searches
of both library roots and Mathlib located these implementations and the terminal-section
representation already used privately in TopologicalResolutionCocycleLift.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.exists_topological_induced_edge_and_map`
(node `lem-sc-topological-induced-edge-and-map`).

No sorry remains in the delivered module. No holes were added, and no theorem was split off.
This is a proof, not a decomposition into new holed statements.

## No longer needed

Removed direct imports `Mathlib.CategoryTheory.Abelian.RightDerived` and
`Mathlib.CategoryTheory.Abelian.Injective.Ext`; the proof uses the derived-category Ext API,
not injective-resolution or right-derived-functor computations. Its statement dependencies
remain available through `WeilConjectures.Topology.Sheaves.PushforwardCohomology`.

Removed proof dependency `lem-sc-topological-pushforward-injective`. Its declaration
`TopCat.Sheaf.injective_pushforwardAb_obj` is not used. Its containing module
`WeilConjectures.Topology.Sheaves.PushforwardCohomology` must still be imported because it
defines `pushforwardAb`; this delivery makes no claim that the whole module is unreachable.
No Sheaf proof-dependency module is imported. Both retained definition nodes are used.
No unit statement or realized unit step is bypassed (the unit realizes only
`thm-sc-proper-cohomology`, not this intermediate node).

## Where the brief, the DAG or earlier work was wrong

The natural-language node additionally asserts compatibility with arbitrary injective
resolution cocycles. The existing Lean signature asserts only existence of a natural edge
transformation and of a terminal map with its generator formula; it contains no relation
between these witnesses and no cocycle clause. This delivery preserves that signature and
constructs the canonical exact-inverse-image map, but does not claim to have formally proved
the extra prose clause. The node's statement and source fields have not been altered.
The second reader should carry this existing statement-versus-Lean discrepancy upward.

The source file `literature/stacks-project/cohomology.tex` is absent on this machine.
Read the official [Section 01DZ](https://stacks.math.columbia.edu/tag/01DZ) and
[Tag 01F2](https://stacks.math.columbia.edu/tag/01F2) online. Section 01DZ defines
cohomology via resolutions; 01F2 is the Leray spectral sequence for ringed spaces,
whose proof invokes the composition comparison. Neither page literally states this
free-terminal-generator formula; that is the adjunction specialization in the original
node's plan and is proved directly using Mathlib.

## Second reading by F1

1. **Visible declarations: PASS.** Independently diffed the only delivered module against
   the repository. Extracted the existing theorem text from `theorem` through `:= by` and
   compared it byte for byte: identical, including all universes, hypotheses and both
   existential conclusions. There is no changed definition used by a target. The added
   `sectionEquiv` is private and concretely composes three existing adjunction equivalences.
   The public-import removals have the supplied change record; the added Ext import is
   proof-only. No other module is delivered or adapted.

2. **Proof and axioms: PASS.** Independently compiled the module with `lcompile.py`, then
   compiled a scratch copy with `#print axioms` for
   `CategoryTheory.exists_topological_induced_edge_and_map` and the private `sectionEquiv`.
   Both show exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   The module has no `sorry`, forbidden declaration, or hollow definition. Read the actual
   constructions of `b`, `edge`, and `a`: Ext functoriality and counit naturality prove the
   natural transformation equation; the sheafification lift equation gives the generator
   formula. No arbitrary data is selected from an unproved existence statement.

3. **Split statements: PASS (none).** No theorem is split off and no holes are added.
   The private equivalence is fully constructed, rather than a new unproved statement.
   Reviewed degree zero, empty spaces, the identity map, and the zero sheaf: none is excluded
   by the constructions or hypotheses. Independently searched the library and Mathlib
   cohomology/pullback APIs and ran leanfinder with “exact inverse image functor induced Ext
   homomorphism sheaves global sections”. The results include `Ext.mapExactFunctor` and
   `cohomologyPresheafFunctor`, which the proof already uses, rather than a missing theorem
   that would close a split statement or replace the whole construction.

4. **Route, imports and pruning: PASS.** The proof uses existing Mathlib exact-functor Ext,
   adjunction, free abelian group and sheafification APIs. No resolution-comparison hole is
   introduced. The two remaining imports supply respectively the unchanged public statement
   and the proof's exact-functor Ext operation. The old dependency omitted from the new
   `proof_deps` is precisely `lem-sc-topological-pushforward-injective`, already listed in
   `## No longer needed`; its containing module remains a statement dependency. No whole
   module is claimed pruned. Checked `dag/units/sk-thm-curveestimate.json`: its `realized`
   statement is only `thm-sc-proper-cohomology`, its realized steps are empty, and this item
   is not a realized unit step. The unit route remains unchanged. The sole direct importer,
   `Sheaf.Topology.TopologicalInducedCohomologyCocycle`, explicitly publicly imports both
   removed Mathlib modules. Compiled an unchanged scratch copy of that importer against
   the sandbox's freshly compiled delivered module: clean, confirming no forced adaptation.

5. **Node correspondence: PASS for the Lean proof; existing statement discrepancy flagged.**
   Compared the old and delivered JSON: only `proof`, `proof_deps`, and `proof_origin` change.
   Read each new proof step against the Lean code and checked that `proof_deps` is the union
   of its `uses`. The two retained nodes describe the cohomology and inverse-image objects
   actually used. The node's additional resolution-cocycle clause is not in the unchanged
   Lean signature; the proof does not establish that clause, and neither the node statement
   nor the Lean statement has been silently changed. **Maintainer follow-up:** review this
   existing stage-2 statement correspondence before counting the natural-language node as
   fully formalized. The downstream module separately states cocycle compatibility and
   uses `topological_induced_cocycle_formula` for it, discarding this item's `edge` witness.

Second reading changed only this report, adding the independent review, axiom and downstream
compilation evidence, and the explicit maintainer follow-up. No proof repair was necessary.
Closed holes: `CategoryTheory.exists_topological_induced_edge_and_map` (one of one).
Added holes: none. Split-off statements: none.
