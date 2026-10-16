## What changed

Added the completely proved module
`Sheaf.CategoryTheory.CoefficientPushCopowerCriterion`, with the theorem
`CategoryTheory.Adjunction.isIso_iff_unitCoproductComparison`.
It generalizes the existing finite-basis unit-mate calculation to an arbitrary indexing type.
It proves an equivalence: after the two basis decompositions and the right mate are invertible,
the coefficient push component is invertible exactly when the corresponding copower comparison
is invertible. The proof checks the conjugacy equation on each coprojection and cancels
isomorphisms. It uses only Mathlib's adjunction mates and coproduct APIs.

The item's private `CategoryTheory.Adjunction.isIso_of_unitDesc` now uses that theorem.
The conversion from finite biproducts to coproducts is explicit, and additivity supplies the
finite copower comparison. This helper is used by `derivedPushHom_of_finiteFree` and hence by
the already proved finite-extension instance. A proof-only import makes the new theorem
available without changing any public signature or public import of the item.

Marked the remaining proper finite-to-Qbar instance `STATEMENT-DISPUTED` at its declaration.
Its statement and existing `sorry` are retained. The marker concerns its all-unbounded scope
and the missing ambient adjoint, not its bounded constructible specialization.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. Split-offs with `sorry`: **0**.
This delivery does not claim that refactoring an already proved finite-extension argument
closes the original proper-pushforward hole.

New theorem completely proved:
`CategoryTheory.Adjunction.isIso_iff_unitCoproductComparison`, node
`lem-weil-pbc-coefficient-push-copower-criterion`.
The private finite helper `CategoryTheory.Adjunction.isIso_of_unitDesc` also compiles using it.

The one existing `sorry` left is
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`.
It is the open upstream input explicitly cited in step 1 of
`prop-weil-pbc-qbar-condensed-basechange-compatibility`; that node is attached to
`Sheaf.Paper.CondensedQbarBaseChangeCompatibility`, not to this instance.
The item-module match in `prop-weil-pbc-qbar-condensed-two-colimit` is only a stale audit
record of earlier flatness holes. I found no dedicated Lean attachment for this remaining
instance. No new statement merely renames it.

The new criterion was tested by compilation and by its use in the finite argument.
Its empty-index case is covered without a nonempty assumption: the two assumed invertible
basis morphisms still give precisely the same conjugacy equation. No positivity, characteristic,
cohomological bound, properness or constructibility is hidden in its statement.

## No longer needed

No existing imports, DAG nodes or source-library modules are pruned by this delivery.
The finite argument continues to use its existing dependencies.
The new generic module imports only `Mathlib.CategoryTheory.Adjunction.Mates` and
`Mathlib.CategoryTheory.Limits.Shapes.Products`.
In particular it needs no module-object coefficient-change import.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the item's remaining instance quantifies over all complexes in the
unbounded ambient internal-module derived category, for every proper morphism of schemes.
Its docstring claims that properness supplies an ambient right adjoint to `Rf_*`.
The existing `ModuleObject.Derived.UpperShriek` constructs its exceptional right adjoint only
on bounded constructible categories, for schemes separated and of finite type over a field
of positive characteristic different from the coefficient prime. Those instance types cannot
supply a right adjoint to the ambient functor in the remaining instance.

`Sheaf.Paper.CondensedQcqsPushforwardContinuity.condensed_qcqs_pushforward_continuity`
requires a common lower cohomological bound `a` for every complex in its diagram.
It cannot be applied to an arbitrary unbounded object by omitting that hypothesis.
`Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts` likewise concerns bounded-below
continuity, and its coefficient category is ordinary module-valued sheaves.
The new criterion shows explicitly where the missing infinite-copower comparison enters;
finite additivity only supplies it for finite index types.

There is substantial reason to question the stronger ambient assertion:
`WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts` proves that the proper
structure map of a positive-dimensional abelian variety does not preserve countable
coproducts on the unbounded pro-etale derived category of ordinary sheaves of modules over
any field. The construction uses a subgroup `H = direct_sum_N Z` of the geometric generic
Galois group, an exact equivariant evaluation adjunction, and a sheaf with nonzero cohomology
in every positive degree. Its shifted copies obstruct coproduct preservation.

**This is not yet a Lean-certified counterexample for the precise internal condensed E-module
category of this item.** An explicit lift of the equivariant evaluation/coevaluation
adjunction to modules over `condensedRingObj (continuousMapRingObj E) X`, with the required
exactness and coefficient-ring identifications, remains to be supplied. I have not imported
ordinary-module counterexample declarations as though they had the internal-module type.
The report records the distinction instead of treating the failure of one proposed proof
as a formal refutation of the statement.

The target-facing node only requires invertibility on bounded constructible objects.
A repair should establish that narrower coefficient-continuity theorem and adapt consumers
of the blanket instance, or prove an appropriate additional ambient theorem for these exact
coefficients. The existing target statements must remain unchanged. Neither repair is
silently assumed in this delivery.

During exploration I tried two proposed intermediate statements asserting blanket ambient
coproduct preservation and an overly general flat-coefficient comparison. They were not
justified, so both proposed modules and nodes were removed from this sandbox. They are not
part of this delivery and contribute no new holes.

## New nodes

`lem-weil-pbc-coefficient-push-copower-criterion` records the proved categorical equivalence,
its unit-mate conjugacy proof, its exact Lean signature, and the three kinds of Mathlib
search. It is used by the item's finite-basis helper. No new node contains a `sorry`.
No existing node statement or blueprint unit route is changed, and there is no interface
change requiring a change record.

## Second reading by G1

1. Compared the complete item diff and all 70 parsed existing declarations with the shared
   source. Every existing signature, visibility, definition body and public import is unchanged.
   Only the private `CategoryTheory.Adjunction.isIso_of_unitDesc` proof, one proof import and
   the disputed-statement comment change. No target or other group's module is edited. PASS.
2. Compiled both delivered modules separately and in dependency order with `lcompile.py`.
   The new criterion is fully proved; the item's sole existing proper-to-Qbar instance remains
   the only direct hole. Checked the source for forbidden declarations and hollow definitions,
   and checked axioms using a scratch copy. The new criterion and finite-extension instance use
   exactly `propext`, `Classical.choice` and `Quot.sound`; only the unchanged proper-to-Qbar
   instance additionally uses `sorryAx`. No additional axiom or postponed data is introduced.
   The first full-set check timed out at 60 seconds on the item; its individual recheck passed
   in 47.4 seconds. No time limit, statement or definition was changed to obtain that pass.
3. There are no split-off statements with `sorry`. Read the new equivalence hypothesis by
   hypothesis and checked its conjugacy equation on coprojections, both cancellation directions,
   and reflection of isomorphisms. The empty family is valid under the stated decomposition
   hypotheses; a singleton reduces to conjugation by isomorphisms. The finite specialization
   supplies precisely the extra comparison through additivity. PASS.
4. Searched again with LeanFinder, Loogle (`CategoryTheory.Limits.sigmaComparison`) and `rg`
   using coproduct/mate/unit terminology. Mathlib supplies the comparison and mate identity;
   the existing upstream biproduct lemma assumes a finite family and additional adjunctions,
   so neither replaces the arbitrary-family equivalence. Read the bounded-continuity and
   bounded-constructible adjoint signatures: neither supplies the remaining ambient instance.
   The ordinary-module counterexample is not a counterexample in the exact internal-module
   category, and the dispute/report preserve this distinction. No unit statement or realized
   proof step is bypassed, no old proof dependency is removed, and no pruning is claimed. PASS.
5. Matched the new node's statement and exact Lean signature, both proof steps, empty
   `proof_deps` (the proof uses Mathlib), source, origin, chapter/unit and creation record.
   There is no existing node whose primary Lean attachment is this item; the old item-module
   mentions are audit entries, not an attached proof plan to rewrite. The unit's `realized`
   record is unchanged. PASS.

Second-reading repair: reduced the new module's public coproduct import from
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` to
`Mathlib.CategoryTheory.Limits.Shapes.Products`, which suffices for its signature and proof;
updated the import inventory and recorded the independent searches. The categorical proof and
finite specialization were otherwise correct and are retained. Original holes closed: 0 of 1;
holes added: 0; split-offs: 0; pruned existing modules: none.
