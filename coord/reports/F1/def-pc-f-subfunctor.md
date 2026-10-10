1. Files written

- `dag/nodes/sec-picard-framework/def-pc-f-subfunctor.json`: item definition, split with 0 new nodes and 0 Mathlib leaves.
- `dag/units/sk-def-picard-f.json`: realized statement field for the unit.
- `citations.json`: empty, because the item is a definition with no proof steps.

2. Attachments

None. `AlgebraicGeometry.picardFunctorInvertibleDirectImage` at `WeilConjectures/AlgebraicGeometry/Picard/Representability.lean:171-194` states the definition, but the declaration is marked `rests_on_sorry` by the audit and is therefore not an attachable sorry-free declaration.

3. WANTED:

None.

4. What was checked

The item source is the blueprint node `def-pc-f-subfunctor`, order 819, and the corresponding unit sketch `sk-def-picard-f`. I read the Lean declaration and its docstring in `Picard/Representability.lean` lines 171-194. Its object field is exactly the predicate that the derived direct image is invertible in degree zero, and its map field is supplied by `IsInvertibleDirectImage.map_of_isProper`; this matches the imported statement and the five existing statement dependencies. The declaration's local hypotheses are the flat, proper, locally finite presentation morphism and the injective-resolution instances, while the blueprint statement abstracts these through the given base-change and invertibility notions.

I also read the audit's open declarations in `Cohomology/DirectImage.lean` (lines 307-324, 421-440, 549-567, and 574-615). They are lower implementation lemmas used transitively by the open-locus and base-change theorems; they are not additional notions required to state this definition, and the definition has no proof-step list in which to cite them. No new node was created, avoiding a restatement of the item or a node for an implementation detail. The required LeanFinder, Loogle, grep, and unavailable LeanSearch records for the item were run through `msearch.py`; no Mathlib declaration states this project-specific Subfunctor construction.

5. What could not be finished

Nothing. The only limitation is that the project declaration cannot be attached as closed because its transitive dependencies contain `sorry`, as recorded by `lean_audit.slopmaster2`.

## Review by F1

I checked the source declaration and docstring against the item and the unit sketch, including the object predicate, the Subfunctor inclusion, and the hypotheses used by the map field. I verified each existing statement dependency is a notion named by the item (`def-pc-derived-direct-image`, `def-pc-base-change`, `def-pc-invertible-in-degree-zero`, `def-pc-pic-sigma-functor`, and `def-pc-subfunctor`). Since this is a definition, there are no proof steps or cited-node quotes; `citations.json` is consequently empty. I checked the audit's four missing lower declarations and confirmed they belong to the transitive implementation of the already-defined map/open-locus machinery, not to the definition's statement. I corrected the blueprint fields, marked the item split, and realized the unit statement.

## Second reading by F1

- Item definition `def-pc-f-subfunctor`: compared with the unit sketch, `lem-pc-f-open-subfunctor`, and `AlgebraicGeometry.picardFunctorInvertibleDirectImage` at `Representability.lean:171-194`. The object predicate and normalized Picard target agree. The imported arbitrary-scheme hypothesis was too broad for the stated subfunctor: the Lean map field assumes flatness, properness, and local finite presentation, and the unit takes a smooth projective curve. Corrected to the smooth projective curve hypothesis; the definition node for that notion is cited. The field need not be separably closed for the definition or the downstream open-subfunctor lemma; the unit's separably closed case is a specialization. Empty base schemes give the empty set as expected; on a genus-zero curve over a field the structure sheaf has degree-zero invertible direct image; on a genus-one curve the structure sheaf has nonzero first cohomology and is excluded. Verdict: definition now matches the source route.
- Proof steps: none, because this is a definition. Checked the Subfunctor map field in `Representability.lean:190-194` and the separate pullback-stability argument in `lem-pc-f-open-subfunctor`; no step or citation belongs in this item. Verdict: empty `proof`, `proof_deps`, and `citations.json` are correct.
- New nodes: none. Checked the five existing definition dependencies and `def-pc-smooth-projective-curve` against their statements; each names a notion used by the item. Verdict: no new node or Mathlib leaf is needed.
- Changes: narrowed the item's statement from arbitrary `X` to a smooth projective curve; added its existing definition node to `stmt_deps`; updated the split summary to name the correction. The unit record and search log remain valid.
