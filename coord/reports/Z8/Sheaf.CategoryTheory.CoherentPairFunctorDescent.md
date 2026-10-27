## What changed

Proved `CategoryTheory.CommonStage.coherent_pair_functor_descent` in
`Sheaf.CategoryTheory.CoherentPairFunctorDescent`, with its original signature and all
existing public declarations unchanged. Explicit equivalences of representatives and
quotient Hom types reuse the proved native StageSystem category and preadditive calculus.
Finite biproducts are built at a common stage and transported along isoToStage. Coherent
families and compatible transformations use the native functor and descNatTrans, conjugated
through the quotient equivalences. Representative induction proves identity and composition
preservation; Mathlib functorExtension₂ supplies the Karoubi formulas and sandwich equation.

Private helpers are fully proved. Private proof imports replace the unused module-colimit
import. File-local elaboration settings, reducibility attributes and private wrapper
instances are documented in
`coord/changes/Z8-coherent-pair-descent-private-bridge.md`. No source-library file or public
definition is edited. The existing shared theorem node's proof is extended to record this
original generic theorem, retaining its earlier StageSystem proof route and attachment.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.CommonStage.coherent_pair_functor_descent`
(documented by `lem-sbc-coherent-pair-functor-descent`).
Zero holes remain in the item; zero holes are added. No statements are split off.
The native StageSystem Basic, Functor and Preadditive support modules contain no holes.
The complete module compiles cleanly (12.7 seconds; the axiom-print pass 17.2 seconds).
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the unused private import `Mathlib.Algebra.Colimit.Module`: the explicit quotient
is identified with the existing native quotient, whose additive operations are already
constructed. No separate directed-group-colimit construction or dependency is needed here.
No existing DAG dependency is removed (the node's current proof_deps is already empty),
and no module or node is withdrawn. All existing public imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

The module contains the original generic theorem, but its theorem docstring's node now
attaches to `StageSystem.coefficientPairFunctor_exists` in StageSystemFunctorDescent; that
node's current four proof steps concern the latter interface only. The generic data also
have the newer `def-a1-common-stage-pair-functor-data` ownership node. This delivery preserves
both ownership records and the existing StageSystem proof steps, and adds the actual
original generic proof to the theorem node. No mathematical statement was corrected.

Edge cases checked in the construction: the empty finite family uses the nonempty index;
nonfaithful transitions are allowed because quotient equality is eventual equality;
identity and composite functor equalities are literal by quotient induction; zero and
arbitrary idempotent projectors use only naturality and idempotence. No faithful-transition,
extra unit, universe or finiteness hypothesis is added.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
