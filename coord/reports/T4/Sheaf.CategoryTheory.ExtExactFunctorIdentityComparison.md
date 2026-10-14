## What changed

Repair of return X-2affc (2026-10-14): retain the private theorem
`CategoryTheory.Abelian.Ext.commShift_of_localization` immediately before
`exactFunctorIdentityComparison`. The earlier delivery removed it, although
`Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity` imports this module
with `import all` and calls the helper in `identity_comparison_commShift`.
The helper matches the current repository verbatim. The main proof gains one
comment explaining why shift compatibility is checked before localization.
No statements, definitions, visibility, or imports change.

## Proved and sorry left

`CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` is fully proved.
`CategoryTheory.Abelian.Ext.commShift_of_localization` is also fully proved.
No sorry remains, no lower statements were split off, and no holes were added.
Relative to the current repository baseline, zero additional holes close: the
main theorem was already proved there. This delivery repairs the earlier deletion
and records an independent second reading; it is not additional ledger progress.

## No longer needed

None. No old proof dependency or import was removed. In particular, the private
localization helper is needed by a downstream `import all` user and stays.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery incorrectly treated the private helper as unused based only
on this module. Its downstream caller makes deletion an interface break.
The requested newer Mathlib shortcuts `mapExactFunctor_eq_of_iso` and
`mapExactFunctor_id` do not occur in the pinned Mathlib sources; the existing direct
localization proof is retained. The only import, Ext.Map, supplies the public
statement's `mapExactFunctor`, so its public visibility is appropriate.

## Second reading by T4

1. Compared the entire module and node against the repository with diff. Restored
   the helper's existing signature formatting and docstring verbatim. The final
   diff contains only a proof comment; every existing declaration signature,
   hypothesis, conclusion, universe, and visibility is preserved. No change record
   is necessary. Read return X-2affc and confirmed the downstream call in
   HigherDirectImageRawPullbackIdentity at `identity_comparison_commShift`.
2. Compiled the module locally through lcompile.py without errors or warnings.
   Compiled a scratch copy with #print axioms for both declarations: only
   propext, Classical.choice, and Quot.sound occur. There are no sorry, axiom,
   unsafe, opaque, implemented_by, extern, or hollow definitions. The standard
   derived-category construction comes from Mathlib, not an unproved witness.
3. No split-off statements or new nodes exist. Read the complete public signature
   against the node: arbitrary abelian C with small Ext, additive F preserving
   finite limits and colimits, natural isomorphism e to identity, arbitrary X, Y,
   and n. Both sides have the node's indicated composition order. Degree zero,
   F = identity, and zero source/target introduce no exclusions. The helper uses
   localization extensionality followed by cancellation of an isomorphism, valid
   without extra conditions on objects or morphisms.
4. Read pinned Mathlib Ext.Map (mapExactFunctor and mapExactFunctor_hom) and
   Localization.SmallShiftedHom (equiv_smallShiftedHomMap). Searched pinned Mathlib
   and both library roots for the proposed iso/identity shortcuts; none exists.
   The proof constructs the termwise comparison eta, checks its shift square
   componentwise, whiskers by Q to form delta, and applies
   equiv_smallShiftedHomMap with the identity derived functor. The hx equality is
   checked at degree zero and by the zero source in every other degree; hy cancels
   the inverse components. Ext.ext and ShiftedHom.id_map then give the conclusion.
   Ext.Map is the only import and is needed in the public signature. Read
   dag/units/sk-thm-p1.json: this auxiliary node is not itself a realized unit step;
   its proof keeps the localization route and changes no realized statement or step.
5. Compared the node files: identical. The proof and proof_origin describe the
   same direct localization argument; proof_deps remains the exact-functor
   derived-factorization Mathlib leaf and def-pc-ext. No old dependency is pruned,
   and no new-node metadata is required. The restored helper does not change the
   main theorem's proof dependencies.

Changed during second reading: restored the helper's repository signature layout
and docstring, corrected the obsolete review/report claims about pruning and the
unit realization, and recorded that the current baseline already proves the item.
Added a proof comment explaining the shift check before localization; preflight
requires a changed item module even for this returned-delivery repair.
No mathematical changes were needed.
