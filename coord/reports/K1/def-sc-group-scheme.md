# Stage 1 report: def-sc-group-scheme

## Files written

- `dag/nodes/sec-abelian-varieties/def-sc-group-scheme.json`: definition, split; no new node and no Mathlib leaf.
- `dag/units/sk-def-av-group-scheme.json`: realized statement `def-sc-group-scheme`; no proof steps in the unit.
- `citations.json`: empty list because the item is a definition with no proof steps.

## Attachments

None. No sorry-free declaration in either source checkout states the full composite project definition under the blueprint tag. The slopmaster2 `Defs.lean` module documents the same terminology in prose but does not declare a single definition for it.

## WANTED

None.

## What was checked and corrected

The imported node had status `imported` and a null `blueprint.same_as`. I changed it to `split` and `same_as: []`, preserving its statement, source, pointer fields, and its existing dependency on `def-weil-pbc-scheme-conventions`. The item is a definition, so it has no proof steps or proof dependencies; the kernel and finite-etale criterion references remain forward pointers to their own nodes rather than dependencies of the definition. No smaller node can be introduced without restating a clause of the definition.

## Review by K1

I read the unit record `sk-def-av-group-scheme` and the blueprint source at `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-def-av-group-scheme/def-sc-group-scheme.md` (node order 422), then compared the statement with `WeilConjectures/AlgebraicGeometry/GroupScheme/Defs.lean` in both `weil-src-slopmaster2` and `weil-conjectures-slopmaster2`. That source describes a group scheme as an object of `Over (Spec K)` equipped with Mathlib's `CategoryTheory.GrpObj`, commutativity as `IsCommMonObj`, homomorphisms as `IsMonHom`, finiteness as `AlgebraicGeometry.IsFinite`, order as `Scheme.Hom.finrankΓ`, and etaleness as `AlgebraicGeometry.Etale`; these are exactly the component notions used by the imported statement. The source has no declaration tagged `def-sc-group-scheme`, and a repository-wide search found no exact sorry-free declaration for the full composite definition.

There are no proof steps, so there are no cited statements or hypotheses to validate in `citations.json`; the only statement dependency is the existing scheme-conventions definition, used for the meanings of finite and etale morphisms. The two displayed theorem names in the statement are forward pointers: `lem-sc-kernel-subgroup` proves the kernel claim and `lem-sc-finite-etale-algebra-criterion` proves the finite-etale algebra criterion, so neither belongs in the definition's `stmt_deps`. I searched the whole DAG and blueprint for duplicate group-scheme definitions and found only this item and the dependent subgroup definition. Mathlib searches were run twice by LeanFinder, Loogle, and source grep; they found only the underlying component notions, not this composite project definition. Small cases such as the trivial group scheme and a finite product of separable fields do not expose any mismatch in the definition.

## Second reading by K1

- Item statement: checked against blueprint node `def-sc-group-scheme` (order 422) and the terminology documented in `WeilConjectures/AlgebraicGeometry/GroupScheme/Defs.lean`, including the field, group-object, finite, order, kernel, and etale clauses; verdict: agrees hypothesis by hypothesis.
- Proof steps: none; the item is a definition and has no proof or proof dependencies, so there are no uncited mathematical steps to repair.
- New nodes: `def-sc-group-scheme` is the item itself and no auxiliary nodes were introduced; B1-B7 and duplicate-node checks therefore have no additional-node findings. The existing `def-weil-pbc-scheme-conventions` dependency defines the finite and etale morphism terminology used by the statement.
- Edge cases: checked the trivial group scheme, a finite product of finite separable field extensions, and the empty-product/zero-ring boundary for the finite etale algebra wording; no contradiction with the blueprint definition was found.
- Mathlib/Lean audit: the source file contains prose and component declarations but no single sorry-free declaration for this composite definition; six recorded searches found no exact Mathlib composite. No Mathlib leaves are added.
- Changes: set the imported node's `status` to `split` and `blueprint.same_as` to `[]`, preserving its statement, source, dependency, and forward pointers; this records the completed split without inventing a proof node.
