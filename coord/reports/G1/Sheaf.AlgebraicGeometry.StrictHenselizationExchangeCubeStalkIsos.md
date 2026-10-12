## What changed

Added two component modules proving the source and target `IsIso` conjuncts as named
intermediate obligations, and changed the target module to compose them with `constructor`.
All original imports remain because the target signature uses their declarations.

## Proved and sorry left

The target declaration `AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons`
is proved by conjunction introduction from the two component theorems. The component declarations
`AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_source_stalkComparison` and
`AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_target_stalkComparison` remain `sorry`,
with nodes `lem-weil-pbc-strict-henselization-exchange-cube-source-stalk-iso` and
`lem-weil-pbc-strict-henselization-exchange-cube-target-stalk-iso`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires substantial strict-henselization and derived-category arguments;
no existing declaration in the reachable library closes either component. The argument was split into
two strictly smaller component statements so the parent proof is complete and independently checkable.

## Earlier second reading (a previous round; superseded)

The component declarations are strict subclaims of the parent conjunction, and the parent proof
applies them without changing its signature. A second G1 worker should verify the two new nodes
against the component signatures and the original unit route.

## New nodes

lem-weil-pbc-strict-henselization-exchange-cube-source-stalk-iso records the source component.
lem-weil-pbc-strict-henselization-exchange-cube-target-stalk-iso records the target component.

## Second reading by G1

1. I compared the item module with the repository version. Its theorem signature is unchanged;
the only change is the proof, which introduces the two conjuncts using the split declarations.
The two new modules contain exactly the corresponding component signatures.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile cleanly. The
parent theorem has no `sorry`; the two component theorems intentionally retain their named
`sorry`s and matching nodes. No forbidden declarations or hollow definitions were introduced.

3. The source and target component statements are the respective conjuncts of the parent
statement, hence true and strictly simpler than the conjunction. Their docstrings cite the
Stacks sources, and each has a matching DAG node. No existing declaration duplicates either
component theorem.

4. The proof follows the existing unit route: the parent theorem is reduced only by conjunction
introduction and still imports the same proof dependencies. No shorter proved declaration was
available for either component, and no import was removable.

5. The DAG records for the parent and both split nodes agree with the Lean declarations and
proof dependencies. The unit `sk-thm-p1` remains the recorded unit for all three nodes.

I changed the report by adding this second-reading record; no Lean statements or definitions
were changed during the second reading.
