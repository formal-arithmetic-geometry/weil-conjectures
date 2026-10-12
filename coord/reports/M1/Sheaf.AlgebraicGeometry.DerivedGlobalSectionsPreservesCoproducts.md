## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.DerivedGlobalSectionsPreservesCoproducts`
with a complete colimit argument, keeping its signature and public imports unchanged.
Use X.toSpecΓ to map to Spec Γ(X,O_X), so the affine equivalence has exactly the
coefficient ring required by the conclusion. Derived direct image preserves the ambient
cofan; quasi-coherent coproduct closure and preservation put its apex and summands in
the full quasi-coherent subcategory. The inclusion reflects the colimit, the inverse
affine equivalence preserves it, and natural isomorphisms transport it back to the
specified RΓ cofan, with its actual mapped legs. The direct-sum and affine-equivalence
steps of the original plan are retained.

Added the strictly separate comparison module
`Sheaf.AlgebraicGeometry.DerivedGlobalSectionsAffinizationComparison` and its node.
It states a natural isomorphism of functors for arbitrary schemes, without any
coproduct, quasi-coherence or qcqs assumption; it contains only the unfinished
geometric/derived-composition comparison, not the original universal property.
Added proof imports for this comparison and `DerivedQCohDirectSumsAux`.
Updated the item's proof, proof_deps and proof_origin to match the Lean argument.

Both modules compile together through lcompile.py, including the unchanged target
signature and arbitrary universe w. The main module has no sorry. The compiler
checks the reflection and transport of the cofan's universal property.

## Proved and sorry left

Closed: `AlgebraicGeometry.derivedGlobalSections_preserves_coproducts`
(node `lem-pc-derived-global-sections-preserves-coproducts`), 1 of 1 original holes.

Added and left: `AlgebraicGeometry.derivedGlobalSections_affinization_comparison`
(node `lem-pc-derived-global-sections-affinization-comparison`), with proof exactly
`:= by sorry`. Its docstring and node give the full natural-language proof via the
one-point ringed space, the derived pushforward composition theorem, and exact
evaluation on the point. The Lean signature includes the necessary explicit
transport of the derived-category instance between Γ(X,O_X)'s two presentations.

This is a decomposition: one upper hole closed, one strictly different lower hole
added, net zero holes. Existing imported declarations may still depend on sorry;
they have not been re-proved or counted as newly closed holes here.

Edge cases checked mathematically: an empty scheme has A = 0 and its affinization
is empty; the comparison still comes from composition on the point. For affine X,
a is an isomorphism and the comparison is the usual ΓSpec scalar transport. Zero
objects, unbounded complexes, and empty indexing families require no extra assumption.
No arbitrary data is chosen from a mere existence theorem: the affine equivalence
is used only inside a theorem proof, and no definition is added.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.GlobalDerivedHom` from the
item. The item no longer directly needs `def-pc-global-derived-rhom` or
`def-pc-ringed-spaces-derived-direct-image` as proof dependency edges: the new
comparison isolates their use. They remain statement dependencies or dependencies
of the comparison and are not claimed pruned from the entire target closure.

The route through Spec(ULift ℤ), derived restriction to integers, and reflection of
coproducts by derived scalar restriction is no longer needed. No separate node or
module for this scalar-reflection step exists in the old plan. No original
pushforward-preservation or affine-equivalence module is pruned; each is used.
Public imports are unchanged because they support the existing statement interface.

## Where the brief, the DAG or earlier work was wrong

The old plan required unnecessary scalar restriction to integers. Affinization
keeps the coefficient ring Γ(X,O_X) and removes the need for scalar-reflection theory.
The old plan also did not explicitly state that the ambient coproduct apex S is
quasi-coherent, which is needed to form its full-subcategory cofan. The existing
`schemeDerivedQCohClosedUnderCoproducts` closes that step.

The new comparison is not asserted to follow from the generic composition theorem
alone: constructing the map from Spec A to the point and identifying the exact
point evaluation with scalar-restricted global sections are its remaining glue.
For a general scheme morphism, module pushforward need not preserve K-injective
complexes; the proof in words uses the ringed-space derived composition theorem
instead. Read source: https://stacks.math.columbia.edu/tag/0D5T and
https://stacks.math.columbia.edu/tag/079V; Tag 09M1 explains the surrounding
coproduct application. Literature files are not populated in this local clone.

The unit's realized statement and step lists are empty, and its curve-duality route
is unchanged. The proof retains the original planned affine-equivalence and
pushforward steps. Search of the whole blueprint for global sections and of the
DAG for the comparison found no existing statement with this signature.

## New nodes

`lem-pc-derived-global-sections-affinization-comparison`, in the item's chapter and
unit, is a natural functor-comparison theorem justified by Stacks Tags 0D5T and
079V. Its statement imposes no coproduct hypothesis and supplies no colimit
conclusion; the main module supplies the real universal-property argument.
Three actual msearch kinds are recorded: LeanSearch returned Internal Server Error
(marked unavailable), Lean Finder returned eight ordinary Γ-Spec/pushforward hits
without the derived comparison, and grep found no affinization comparison.
No change record is necessary: no existing statement, definition, or visibility changed.

## Second reading by M1

1. PASS: diffed the existing module and node against the repository. Independently
   compared the theorem signature byte for byte; it is identical. There is no existing
   definition change, extra hypothesis, weakened conclusion, or declaration removal.
   Existing-node changes are exactly proof, proof_deps and proof_origin. The revised
   proof docstring describes the new route. The comparison is a new theorem only.
2. PASS: compiled both modules together with lcompile.py. Independently compiled
   scratch copies with #print axioms for both declarations: only propext,
   Classical.choice, Quot.sound and sorryAx occur. The original module has no sorry;
   the new comparison has the sole direct sorry, as its entire named public proof.
   There are no definitions or forbidden trust mechanisms in the delivery. The affine
   equivalence witness is eliminated inside a proof, not used to define arbitrary data.
3. PASS: read the comparison's whole signature and proof docstring against Stacks
   Tags 0D5T and 079V. The point has ring A on the whole space and zero on the empty
   open; evaluation is an exact equivalence. The counit identity for Γ-Spec identifies
   the composite morphism with the global-sections morphism. Derived composition and
   exact postcomposition then yield the stated comparison, including its scalar action.
   Empty X (A = 0), affine X, the zero complex, arbitrary shifts and unbounded objects
   impose no omitted hypotheses. The comparison has neither an indexing family nor a
   colimit conclusion; the original proof supplies the coproduct argument, so this is
   a genuine decomposition, not a renamed hole. Independent msearch with the query
   "total right derived sections functor commutes with direct image along a morphism
   of ringed spaces" returned only underived sheaf/pushforward results; grep with
   "globalSections.*[Dd]irectImage|[Dd]irectImage.*globalSections" returned no hits.
   Loogle did not recognize the upstream composition identifier; direct rg and reading
   of RightDerivedFunctor/Comp.lean confirmed its additional K-injective-preservation
   hypothesis, which is unavailable for a general scheme morphism. The existing
   ringed-space composition theorem and point comparison supply parts, not the entire
   new statement. Closing its point morphism and evaluation glue is not a short proof.
4. PASS after import repair: checked the colimit proof from its conclusion backward.
   The cofan legs are the actual G.map (ι i), transported through natural isomorphisms.
   The ambient apex is proved quasi-coherent before being placed in the subcategory;
   its fully faithful inclusion reflects the colimit, and the affine inverse preserves
   it. The proof uses every old proof dependency except def-pc-global-derived-rhom and
   def-pc-ringed-spaces-derived-direct-image as direct edges; both were already listed
   under No longer needed. Their role now belongs to the comparison. The unit's
   realized.statement is [] and realized.steps is [[]]; no unit route is changed.
   Existing public imports supply the signature's derived-category, derived-functor
   and global-sections interfaces. Added imports are plain proof imports. No whole
   module is claimed pruned from the target closure.
5. PASS after import repair: checked that each proof_deps is the union of its steps'
   uses, both recorded lean.statement strings occur verbatim in the corresponding
   module, and the new node has the required source, searches, origin, blueprint,
   chapter, unit, created and lean fields. The original node follows the actual
   quasi-coherent-apex, pushforward, affine-equivalence and cofan-transport proof.

Changed: added plain imports of Sheaf.AlgebraicGeometry.GlobalDerivedHom and
Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition to the new comparison
module. These are the two dependencies explicitly cited by its unfinished proof plan;
the first reader had omitted their imports. This keeps the target import closure
consistent with the comparison's remaining obligations and prevents accidental
pruning of their modules. Added this independent review. No proof or signature was
changed during the second reading. Counts remain one original hole closed, one new
hole added, a decomposition with net zero; no complete target proof is claimed.
