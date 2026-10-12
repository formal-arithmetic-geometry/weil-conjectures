## What changed

Completed the proof of `AlgebraicGeometry.etaleInverseImageRingLift` without changing
its signature. Constructed the ten source/target operation maps directly as private
natural transformations. Their naturality follows from naturality of the chosen
product projections and preservation of operations by restriction ring homomorphisms.
All ten section formulas hold by definition.

Split off only the construction of the lifted adjunction and forgetful hom-set
comparison, as `AlgebraicGeometry.etaleInverseImageRingAdjunction` in the new module
`Sheaf.AlgebraicGeometry.EtaleInverseImageRingAdjunction`. The item's proof derives
unit compatibility from that hom-set comparison. Injectivity of the set adjunction
bijection then proves all five transport equations: the constant/unary cases use
preservation of zero, one and negation by the ring-valued unit; the binary cases first
identify the two projections of the adjunct of the product comparison, then use
preservation of addition and multiplication by that same ring homomorphism.

The product-projection calculation is shared between addition and multiplication.
The main theorem's heartbeat allowance is scoped and documented; the file compiles
within the permitted single-file timeout. Removed the earlier attempt's added public
finite-product helper, which was not part of the base library. All new operation
helpers are private, and the item's public imports and existing signatures are unchanged.

## Proved and sorry left

`AlgebraicGeometry.etaleInverseImageRingLift` is proved from the new adjunction theorem;
it contains no local sorry. Its five transport equations and ten section formulas
are proved in Lean, together with the naturality of the five private operation maps.
This is a reduction, not a claim of a sorry-free axiom closure.

The sole sorry in the delivery is the whole proof of
`AlgebraicGeometry.etaleInverseImageRingAdjunction`, node
`lem-weil-pbc-etale-inverse-image-ring-adjunction`. It asserts only existence of the
lifted adjunction, underlying comparison and hom-set identity. It asserts none of the
operation maps, section formulas or transport equations proved by the item's module.
Its docstring and node give the construction from the two existing internal-object
statements, including identification of the right functor with sectionwise direct image.

## No longer needed

Removed the proof imports `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
and `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects` from the item's module.
No internal ring-object equivalence or generic lifting theorem is needed to prove
its operation clauses once the adjunction/hom-set comparison is available.
The remaining adjunction lemma's documented proof plan still uses their two nodes;
this delivery does not claim that those nodes can be pruned from that construction
or globally. The new open adjunction module imports both dependencies as proof-only
imports, as required for its recorded construction plan.

All old `proof_deps` removed from the item's direct dependency list are:
`lem-weil-pbc-etale-base-change-continuous`,
`lem-weil-pbc-sheaf-algebraic-structures-objects`, and
`lem-weil-pbc-adjunction-lifts-group-ring-objects`. Each remains a dependency of the
new adjunction node. Also removed the item's proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; the new adjunction module
imports it for the continuous base-change construction. No node or module is
claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left the item's original sorry untouched, so its proved
finite-product helper could not constitute a delivery. The fact that the generic
ring-object lifting theorem itself has a sorry was not an obstruction to using it.
The unresolved issue is the sheaf/internal-object transport and right-functor
identification, now isolated in a strictly smaller statement.

The original DAG derived left operation formulas from generic lifting formulas.
The implemented proof derives them from the lifted adjunction's unit instead.
The existing docstring retains its source construction plan; the updated node and
this report record the implemented route. Its operation-formula paragraph describes
an alternative generic-lift argument, rather than the implemented unit argument. The unit `sk-def-exchange` and its
realized statement nodes are unchanged and are not bypassed.

LeanSearch returned an Internal Server Error; it is recorded as unavailable.
LeanFinder, Loogle and source searches were run and recorded; no existing theorem
with the required ring-sheaf forgetful hom-set comparison was found. The local
literature path is absent on this clone; the source was read on the official Stacks
pages [00YV](https://stacks.math.columbia.edu/tag/00YV) and
[00YR](https://stacks.math.columbia.edu/tag/00YR).

## New nodes

`lem-weil-pbc-etale-inverse-image-ring-adjunction`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-inverse-image-ring-adjunction.json`,
with module `lean/Sheaf/AlgebraicGeometry/EtaleInverseImageRingAdjunction.lean`.
This isolates steps 1–3 of the former plan; the operation step is fully proved by
the item. The statement keeps the arbitrary scheme morphism and finite-limit
hypothesis, with the same universes. Edge cases checked in the mathematical
construction: identity morphisms give the identity lift; empty schemes do not require
inhabitants of site objects or sections; the zero ring is permitted, since no
nontriviality or distinctness of zero and one is used. No change record is needed:
no existing public interface changes.


## Second reading by T1

1. **Interface: pass.** Diffed the delivered item against the repository version,
   read its complete signature and proof, and checked the declaration table with
   `stage3_delivery.diff_module`. The existing theorem signature is byte-for-byte
   identical. The only existing node fields changed are `proof`, `proof_deps`, and
   `proof_origin`. No existing definition, target, or public import is altered;
   the five added operation helpers are private. The new adjunction statement has
   the same scheme morphism, universes, and finite-limit hypothesis as the item.
2. **Proof: pass as a reduction.** Compiled both modules in import order with
   `lcompile.py --all`, without errors or warnings. The item has no sorry; the
   adjunction theorem has the sole whole-theorem sorry. Searched for forbidden
   declarations, kernel bypasses, and hollow definitions and found none. Compiled
   temporary copies with `#print axioms` for both public theorems and all five
   private operation maps. The helpers use only `propext`, `Classical.choice`, and
   `Quot.sound`; both public theorems additionally use `sorryAx`, as expected from
   the open adjunction theorem. The probes were removed from the delivery.
3. **Split statement: pass.** Read the new theorem, its node and its complete
   docstring construction. Checked the construction against
   [Stacks 00YV](https://stacks.math.columbia.edu/tag/00YV) and
   [00YR](https://stacks.math.columbia.edu/tag/00YR), and read the two generic
   internal-object statements it uses. Identity scheme morphisms, empty schemes,
   and zero rings introduce no missing nonemptiness or nontriviality hypotheses.
   The forgetful comparison has the correct inverse direction for adjuncts.
   Repeated LeanFinder, Loogle and Mathlib grep searches with different queries,
   and searched both local Lean roots. Returned affine-spectrum, free-ring and
   module adjunctions have different objects and do not close this statement.
   Recorded the new search evidence in the new node. The split retains only the
   adjunction construction; the item gives a real sectionwise proof of the ten
   formulas and five transport equations, not a single application of a renamed
   copy of the original statement. Closing the remaining functor transport is
   substantial and was not attempted as a short repair.
4. **Route and pruning: pass after bookkeeping repair.** Checked naturality of
   each helper using restriction ring homomorphisms, unit compatibility from the
   hom-set equation at the identity, and all five uses of adjunct injectivity.
   The shared product-projection calculation has the correct source and target.
   This direct unit argument avoids using the generic lift's operation formulas.
   The two generic construction dependencies are still needed by the open
   adjunction plan and are not globally pruned. Completed `No longer needed`
   with all three old direct proof dependencies and the removed upstream proof
   import. Read `dag/units/sk-def-exchange.json`: its two realized statement nodes
   and empty step list are unchanged; this lower-level reduction bypasses no unit.
   Existing public imports supply the signature and its instances; added imports
   are proof-only. Restored the new open module's planned dependency imports.
5. **DAG: pass.** Both node signatures match the Lean signatures after whitespace
   normalization. Each `proof_deps` list equals the union of its proof steps'
   `uses`. The item's steps describe the implemented naturality, unit and
   projection argument; the new node describes precisely the remaining transport
   construction and has its required source, searches, creation, blueprint, unit,
   chapter and Lean records. Its source gives the ring-object construction; the
   item records the agent-written operation reduction. No change record is needed.

Second reading changed only the new adjunction module's three proof-dependency
imports, the new node's independent search evidence, and the report's complete
pruning accounting and review. The checked proof bodies and existing interfaces
were retained. The original item's docstring describes its earlier generic-lift
proof plan; this report and the updated DAG describe the actual unit-based proof.
