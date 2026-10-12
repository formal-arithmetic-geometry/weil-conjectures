## What changed
Split the transported scalar distributivity theorem into two strictly smaller intermediate theorems, one for additivity in the module variable and one for additivity in the scalar variable. The parent theorem now composes these two statements pointwise.

## Proved and sorry left
The parent declaration `AlgebraicGeometry.etaleInverseImageScalarDistributivity` is proved by applying the two intermediate declarations. The intermediate declarations `AlgebraicGeometry.etaleInverseImageScalarDistributivity_left` and `AlgebraicGeometry.etaleInverseImageScalarDistributivity_right` remain sorry, isolating the categorical transport arguments.

## No longer needed
The prior direct `aesop` attempt and its unused helper `Sheaf.CategoryTheory.BinaryDistributivityTransport` are not imported or needed.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt correctly identified that the categorical transport was substantial, but left the parent as an unstructured sorry. The two missing laws are independent and are now explicit named statements.

## New nodes
`lem-weil-pbc-inverse-image-scalar-distributivity-left` and `lem-weil-pbc-inverse-image-scalar-distributivity-right`.

## Second reading by C1

1. I compared the delivered parent module with the repository version. The theorem signature is unchanged; only its proof and two proof-only imports were added. Verdict: pass.
2. I compiled all three delivered modules with the launcher. They compile without errors, and the only remaining `sorry`s are the two named split declarations. No prohibited declarations or hollow definitions occur. Verdict: pass.
3. I checked the split statements and their nodes. Each node now states exactly one component of the parent conjunction, with the original setup and hypotheses unchanged; both are true consequences of the source module distributivity laws and are strictly smaller than the parent. Verdict: pass.
4. I checked the route and pruning. The parent composes the two component declarations, while the component nodes retain the transport and sectionwise diagram route. The unused binary-transport helper is not imported, and no target-facing import was removed. Verdict: pass.
5. I checked the DAG records and unit route. The component node `proof`, `proof_deps`, and `proof_origin` match the split declarations, and the parent unit remains realized by the original theorem. Verdict: pass.

I changed the two component node statements and proof descriptions to match their actual Lean declarations, and added this second-reading record. No Lean proof text required repair.
