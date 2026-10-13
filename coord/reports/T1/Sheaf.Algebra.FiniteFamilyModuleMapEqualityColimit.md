## What changed
Replaced the sole sorry in `ModuleCat.exists_stage_finite_family_map_eq` by applying
`ModuleCat.eventually_equal_maps_of_directed_preorder_colimit` to each map pair,
then the proved `ModuleCat.exists_common_stage_of_stage_equalities` in the new
module `Sheaf.Algebra.FiniteFamilyCommonStage`. Existing signatures, public
imports and docstrings are unchanged. The DAG now records these two proof steps.

## Proved and sorry left
Closed one original hole: `ModuleCat.exists_stage_finite_family_map_eq`.
The new `ModuleCat.exists_common_stage_of_stage_equalities` is proved by finite
induction and naturality of `extendScalarsComp`; it has no sorry.
Holes added: zero. No sorry remains in either delivered module.
Both modules compile cleanly in dependency order with `lcompile.py --all`.
The existing imported finite-presentation descent theory remains a dependency;
this delivery does not claim to close its holes.

## No longer needed
Removed the direct proof import `Sheaf.Algebra.FinitePresentationColimit` and
replaced the direct DAG dependency `lem-pc-fp-module-map-descent-affine` with
`lem-pc-preorder-module-map-equality-descent`. Finite-presentation descent remains
transitively used; no existing library module is claimed pruned.
Removed the earlier attempt's redundant proposed module
`Sheaf.Algebra.FiniteMapEqualityColimit` and proposed node
`lem-pc-finite-family-map-equality-preorder` before delivery.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt missed the existing preorder descent theorem and left finite
amalgamation open. The preserved revised proof fixes both issues without changing
any existing statement. Its previous infrastructure blocker is now resolved:
the published `Sheaf.Algebra.Homology.PreorderModuleMapEqualityDescent.olean` is
present, and the target compiles against it without a local dependency copy.
The unit's realized route is unchanged. The second-reading section below is
retained verbatim from the earlier attempt; its remarks about awaiting the
published artifact describe the prior state, now superseded by this compilation.
No source dependency or published artifact was changed, and nothing was pushed.

## New nodes
`lem-pc-finite-family-common-stage` records proved finite directed amalgamation of
stage map equalities, sourced to Stacks Tag 0BC7, proof of (1). It has no finite
presentation or colimit-equality hypotheses and is strictly the amalgamation
step. Empty families use i; induction transports equalities to a common upper
bound using the canonical scalar-extension composition isomorphism. Its full
Lean signature, searches and proof in words are recorded in its node.
No change record is needed: existing public interfaces are unchanged.

## Second reading by T1

1. Compared the delivered target module with the repository version. The theorem
   declaration, hypotheses, conclusion, namespace, and public imports are unchanged
   in all statement-relevant declarations; only proof imports and proof text changed.

2. Compiled both delivered modules with `lcompile.py --all`; both compile without
   errors or warnings. The axiom probe for `ModuleCat.exists_common_stage_of_stage_equalities`
   reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`s,
   axioms, unsafe declarations, or hollow definitions.

3. Checked the new common-stage statement on the empty, singleton, and finite-family
   cases. It is strictly the amalgamation step: it has no finite-presentation or
   colimit-equality hypotheses, and its conclusion is exactly one common later stage.
   The proof transports equalities using directedness, functoriality, and
   `extendScalarsComp`; the node records its source and proof.

4. The target proof follows the unit route: existing preorder module-map equality
   descent supplies one stage per map, and the new finite common-stage theorem
   combines them. The unit's realized route is unchanged. The removed direct
   finite-presentation import is proof-only and the remaining descent dependency is
   still used transitively.

5. Compared the target node and the new node with their Lean declarations. Their
   statements, proof dependencies, proof origins, sources, and module/declaration
   records agree with the delivered proofs. No existing target statement or
   definition was changed.

Changed in this second reading: corrected the report heading and replaced the
obsolete prior-round discussion with these checks; no Lean proof or statement
changes were needed.
