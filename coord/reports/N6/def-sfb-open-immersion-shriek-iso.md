## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-open-immersion-shriek-iso.json`: definition, split; no full Mathlib match. The statement and its five statement dependencies are retained verbatim. Recorded eight actual Mathlib searches, filled `blueprint.same_as`, and supplied `split_report`.
- `citations.json`: `[]`. This item is a definition with no proof steps; its inputs are statement dependencies, as stages/1-dag.md §3.2 prescribes.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches of all `WeilConjectures/` and `Comparator/` in slopmaster2 for the exact blueprint id and `openImmersionShriekIso` returned no declaration. The coefficient constructions in `WeilConjectures/SixFunctors/ProEtale/ScalarExtension.lean` use ordinary rings and sheaves valued in `ModuleCat`; its `sheafExtendScalarsCompUpperStarIso` concerns pullback, not this condensed ring-object extension-by-zero comparison. It cannot attach the item.

Upstream master has the intended construction at `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean:281` (body at 285–289). I read it to check the construction, but master is reference material, not an attachment or finished-proof certificate.

## Wanted literature

None. The item is a formal definition, given in the current blueprint and implemented in the upstream reference. No Stacks theorem or SGA source is needed for its construction.

## Issues found

No statement dispute. No hypotheses or conclusion were changed. The imported definition already names all construction inputs, but was unprocessed: `same_as` was null and no split report or Mathlib searches were recorded. These are filled.

Mathlib's `CategoryTheory.conjugateIsoEquiv`, `Mathlib/CategoryTheory/Adjunction/Mates.lean:425`, supplies the generic operation already represented by `def-sfb-conjugate-pull-iso`. Its arguments include two adjunctions and an isomorphism of their right adjoints. It does not itself construct the condensed module adjunctions or `comapUpperStarIso`; treating that generic operation alone as a complete leaf for this project definition would hide its required construction inputs. Read also `CategoryTheory.Adjunction.leftAdjointCompIso`, `Mathlib/CategoryTheory/Adjunction/CompositionIso.lean:72`, and the ordinary-module scalar adjunction in `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:885`. None replaces the full construction with only Mathlib data.

## Unfinished work

No obligation remains at this one-level definition split. The existing dependencies still require their own work. No Lean was written or compiled, and no shared repository or live launcher file was changed.

## Not duplicates

No new nodes were created. Whole-blueprint searches `open-immersion-shriek-iso`, `Extension of scalars commutes`, and `shriek`, together with a whole-DAG search for `openImmersionShriekIso` and the scalar-extension/shriek formulas, found the item, its derived analogue, and the restriction-of-scalars comparison. The derived analogue uses derived categories and derived scalar extension. The restriction comparison uses Res rather than Ext. Neither defines this same underived Ext comparison; `same_as` is therefore empty. The broader unit's statement includes the comparison among several constructions; it is its parent unit, not another definition of the same object.

## Review by N6

I read the chapter and unit records, the entire current blueprint definition at `main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-open-immersion-shriek-iso.md`, and unit step 4, “Extension by zero.” The node realizes exactly the underived conjugate prescribed there. In particular, the unit explicitly says that no flatness is needed for this clause; the flatness assumption belongs to later derived Pull/Push comparisons. The statement remains the source's statement.

I opened the statements of all five dependencies. `sk-def-sfb-coefficient-change` introduces `a_X=p_X^*a` and its source and target ring objects, so the scalar functors in this definition are between the required module categories. `sk-def-sfb-change-of-scalars` clause 2 gives Ext as a functor left adjoint to Res; the coefficient ring objects are commutative and the ambient abelian-sheaf tensor setting is the one of that construction. This uses existence of scalar extension, never exactness or flatness. `sk-def-sfb-module-lower-shriek` explicitly states `j_!` for an open immersion and its adjunction to module pullback; it is used for both coefficient rings. `def-sfb-comap-upper-star-iso` states the displayed Res/pullback isomorphism for every scheme morphism, hence applies to `f=j` with `X=U` and `Y=X` in that node's variable names. Its domain is modules over the primed coefficients, as required.

I checked the remaining dependency, `def-sfb-conjugate-pull-iso`, by assigning its four categories as A=Mod(Λ_X), B=Mod(Λ'_X), A'=Mod(Λ_U), B'=Mod(Λ'_U). Set E1=Ext(a_X), E2=Ext(a_U), U1=j_! over Λ, and U2=j_! over Λ'. Their right adjoints are respectively Res(a_X), Res(a_U), j^* over Λ, and j^* over Λ'. Then its input `Res2 ∘ L2 ≅ L1 ∘ Res1` is exactly the isomorphism supplied by `def-sfb-comap-upper-star-iso`; its output `E1 ∘ U1 ≅ U2 ∘ E2` has the item's direction and its domain Mod(Λ_U) and codomain Mod(Λ'_X). This verifies the construction using dependency statements, not their proofs. Applying that defined operation is elementary substitution; it needs no additional theorem node. The definition carries no independent theorem clause to split off, so adding nodes for its two composites would merely relabel the item. There are no numbered proof steps or proof citations to audit, which explains the empty citations file.

I also read the current source files for the generic conjugate, Res/pullback comparison and scalar-change definition, and compared upstream master lines 281–289: its two composite adjunctions and `.symm` conjugation yield precisely this direction (Lean's `⋙` uses diagrammatic composition). No derived category, compactification, properness or finite-type hypothesis entered the definition.

For small cases I checked the identity coefficient map and identity open immersion, where both sides identify with the expected functor; the empty open immersion, where both composites send the unique zero module to zero; and the non-flat ordinary coefficient example Z→Z/2, viewed as discrete condensed coefficients. Scalar extension in this last example still has its restriction adjoint, so the conjugate construction still exists. These tests expose any accidental flatness or nonempty-open requirement. No new statements were introduced to test. B–E's new-node requirements are vacuous here; the relevant checks of dependency meaning, orientation and hypotheses have been carried out above. No mathematical correction was needed.

## Second reading by N6

- Item statement: checked against blueprint node `def-sfb-open-immersion-shriek-iso` (order 1744), including the coefficient morphism, open immersion, source/target module categories, conjugate orientation, and all five statement dependencies; verdict: agrees hypothesis by hypothesis.
- Statement dependencies: opened `sk-def-sfb-coefficient-change`, `sk-def-sfb-change-of-scalars`, `sk-def-sfb-module-lower-shriek`, `def-sfb-comap-upper-star-iso`, and `def-sfb-conjugate-pull-iso`; verdict: each states the construction input used, with the required adjunction direction and coefficient objects.
- Proof steps: none (definition node); `proof` and `citations.json` are therefore correctly empty.
- New nodes: none; B1–B7 and duplicate-node checks are vacuous. The recorded Mathlib searches were inspected and distinguish generic conjugation machinery from this project-specific condensed comparison.
- Edge cases: identity coefficient/open maps, empty open, and non-flat `Z → Z/2` examples were checked; verdict: no extra flatness or nonemptiness hypothesis is present.

Changes made during second reading: added an independent LeanFinder search using broader adjoint and module-object vocabulary, and recorded its eight actual hits and the mismatch verdict in the item. The hits concern ordinary sheaves of modules and their pullback/pushforward adjunctions, not condensed extension by zero. Appended this second-reading record. The statement and dependency list needed no mathematical correction.
