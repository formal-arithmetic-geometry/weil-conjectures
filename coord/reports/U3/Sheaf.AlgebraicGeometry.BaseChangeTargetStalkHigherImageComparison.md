## What changed

The target theorem `AlgebraicGeometry.Etale.baseChange_target_stalk_higher_image_comparison`
now constructs its family by applying the geometric stalk functor to an explicit sheaf
isomorphism and maps a sheaf coherence equality to the required commuting square.
New module `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` constructs
pullback associativity and its inverse, verifies both inverse equations, constructs the
coefficient comparison, proves the derived transport is an isomorphism, and composes these
with `baseChangeTargetFunctorIso`. All these constructions and their proof obligations are
proved. The sole missing part is the sheaf transition-coherence equality.
No existing statement or definition changed. The unit route and all integer degrees remain.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Etale.baseChange_target_stalk_higher_image_comparison`.
Added one hole:
`AlgebraicGeometry.Etale.baseChangeTargetSheafComparison_naturality`
(node `lem-sbc-target-sheaf-comparison-naturality`).
This is a decomposition, not a net decrease in holes: the comparison objects and their
invertibility are completely constructed; only a specific equality of sheaf transitions
remains. The new statement has no stalk, no existential family, and no arbitrary choice
of isomorphisms. The item's proof genuinely maps and combines this equality with the
proved construction. No sorry occurs in any definition.

## No longer needed

Removed the item's direct import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; its inverse-image constructions
remain used through the helper. No DAG nodes or modules are pruned from the closure.
All four original proof dependencies remain needed. No net module pruning claimed.
The helper's redundant direct public `HigherDirectImageTransitions` import was removed;
`BaseChangeStalkTransition` already exports it through its upstream transition module.

## Where the brief, the DAG or earlier work was wrong

The existing definitions and `baseChangeTargetFunctorIso` do not themselves state the
transition-coherence equality. The DAG's second step hides that glue; it is now a named
sheaf-level node with the specific, constructed comparison. An arbitrary family of
objectwise isomorphisms need not be natural, so no such lemma is asserted.
Edge cases checked: identities and compositions use canonical pullback lifts;
empty schemes impose no extra condition; negative degrees are included because all
comparisons are derived isomorphisms before homology. No compactness or affineness used.
The attempted direct proof encountered expensive elaboration; explicit projection
rewrites fixed the geometry and the final two-module compile passes without warnings.

## New nodes

`lem-sbc-target-sheaf-comparison-naturality` states only the restriction equality for the
explicit `baseChangeTargetSheafComparison`. It records the restriction square in Stacks
Tag 0F07 and canonical maps in 09Z1, and a proof using unit/counit naturality, transition
composition and coefficient-comparison composition. Source text read in the available
Stacks `etale-cohomology.tex`: the restriction square and fixed-coefficient limit paragraph.
No change records: only an existing proof and private proof imports changed; the other
module is new.

## Second reading by U3

1. I compared both delivered modules with their repository counterparts. The target theorem's
   signature is byte-for-byte unchanged; its only change is the proof and its proof-only import.
   The new helper module adds the explicitly constructed comparison and its named coherence
   statement. No existing definition or target statement was altered.

2. I compiled the helper and target together with `lcompile.py --all`; both compile cleanly. The
   only remaining `sorry` is
   `AlgebraicGeometry.Etale.baseChangeTargetSheafComparison_naturality`, exactly the named split
   theorem and node. There are no axioms, unsafe declarations, opaque declarations, or hollow
   definitions. The target proof uses only the permitted standard axioms apart from the imported
   open split theorem.

3. I checked the split statement against the displayed Lean type and node
   `lem-sbc-target-sheaf-comparison-naturality`. It is a sheaf morphism equality for arbitrary
   `p`, `g`, integer `q`, coefficient sheaf `F`, objects `U,V`, and morphism `φ`; it adds no stalk,
   existential, compactness, affineness, or degree hypotheses. The explicit pullback comparison
   and its inverse are genuine pullback lifts, and both inverse identities are proved by
   pullback extensionality. The split is therefore strictly below the target and is needed for
   the final naturality step. Searches recorded in the node found no existing declaration with
   this statement.

4. I reviewed the route from the target downward. The helper constructs the pullback comparison,
   coefficient comparison, lower-star transition isomorphism, and the target sheaf comparison;
   the target then applies the geometric stalk functor and maps the coherence equality. The unit
   route through the canonical target transitions and higher-image transitions remains intact.
   The direct `UpperLowerStar.Defs` import is removed; the helper supplies the needed declarations.

5. I checked edge cases stated in the report: identity and composition maps use canonical
   pullback lifts, empty schemes introduce no extra assumptions, and negative integer degrees
   are covered because all comparisons are formed before homology. I changed only the helper's
   redundant direct `HigherDirectImageTransitions` import (already exported by the stalk
   transition import), checked that `Coefficients` must remain public for the exposed definition,
   fixed a
   spacing-only formatting mismatch in the target proof, and added this second-reading record.
