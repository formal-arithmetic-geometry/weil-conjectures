## What changed

`HomologicalComplex₂.tensorBicomplexMap` now directly abbreviates the map of
Mathlib's uncurried tensor bicomplex bifunctor, without a `dsimp%` elaboration
wrapper. `tensorBicomplex` remains the canonical Mathlib object abbreviation;
`chainTensorMap` is unchanged. Removed the DSimpPercent tactic import.
Updated the existing node's proof text to match.

Two forced caller adaptations add only `Functor.uncurry_obj_map` to existing
simp lists. All existing declarations, binders, visibility and mathematical
statements are preserved. Change record:
`coord/changes/tensor-bicomplex-direct-mathlib-map.md`.

## Proved and sorry left

Repair of an already hole-free module: 0 holes closed, 0 holes added, 0 split
off. No sorry remains in the item or is introduced anywhere. The three data
declarations are concrete Mathlib constructions. Scratch verification proves
map equality with the old normalized composition by rfl, the component formula
in arbitrary degrees, and vanishing when either map is zero.

## No longer needed

Removed `Mathlib.Tactic.DSimpPercent`. No Sheaf node or module is pruned: the
same canonical Mathlib construction and the same mathematical dependencies
remain. Compatibility abbreviations are retained as stage 3 requires.

## Where the brief, the DAG or earlier work was wrong

This is the listed duplicate repair, not a sorry-filling item. Earlier landings
already replaced bespoke bicomplex data with canonical Mathlib aliases. The
previous attempt checked an unchanged file and could not pass preflight.
This repair removes the remaining elaboration wrapper and updates the callers
to use Mathlib's uncurrying API explicitly. No assertion of new proof progress.

## Forced adaptations

`Sheaf.Algebra.Homology.TensorResolutionColumnCokernelIso` (unclaimed): the
original fails at line 108 with an unsolved goal containing the uncurried map's
component on the right. Add `Functor.uncurry_obj_map` after `tensorBicomplexMap`
in its final simp list (new line 124).

`Sheaf.Algebra.Homology.TensorResolutionRowCokernelIso` (unclaimed): the original
fails at line 151 because `change` cannot identify the uncurried map's component
with `a.f 0 ⊗ₘ b.f q`. Add `Functor.uncurry_obj_map` to the existing simp list at
line 146. These one-lemma edits expose the same composite that the former
`dsimp%` wrapper normalized. No other consumer is adapted.

## Second reading by Y3

1. I diffed the delivered modules against the repository versions. Declarations
   and signatures are unchanged; the interface change is the direct
   `tensorBicomplexMap` abbreviation, and both caller edits are proof-only
   forced adaptations.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile
   without errors or warnings. The item contains no `sorry`, `axiom`, `unsafe`,
   `opaque`, `extern`, or `implemented_by`; scratch axiom checks use only the
   permitted foundational axioms.
3. The node is updated only in its proof route to mention explicit uncurrying.
   No theorem or split-off statement was added. Scratch checks establish
   definitional equality with the former normalized map, its component formula,
   and its zero-map cases.
4. Mathlib's bifunctor and uncurrying declarations give the shortest route.
   Removing `Mathlib.Tactic.DSimpPercent` is complete; remaining imports are
   used. The unit route and canonical Mathlib construction remain intact.
5. The change record, node proof metadata, report, and Lean proof agree. The
   two one-lemma caller adaptations are forced and minimal; their originals
   fail against the changed dependency.

I changed only this report section while second-reading. No further repair was
needed.

## Forced adaptations

### Sheaf.Algebra.Homology.TensorResolutionColumnCokernelIso
Original against changed dependencies failed:
```
r.flip_obj_map, curriedTensor_map_app, ← tensorHom_id,
    tensorBicomplexMap, Functor.mapBifunctorHomologicalComplex_obj_map_f_f, flipFunctor_map_f_f, Functor.flip_map_app,
    curriedTensor_obj_map, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hb]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-_n88joei/lean/Sheaf/Algebra/Homology/TensorResolutionColumnCokernelIso.lean:125:4: warning: This simp argument is unused:
  Functor.mapBifunctorHomologicalComplex_obj_map_f_f

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, columnAugmentation, chainTensorMap, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.flip_obj_map, curriedTensor_map_app, ← tensorHom_id,
    tensorBicomplexMap, Functor.mapBifunctorHomologicalComplex_map_app_f_f, flipFunctor_map_f_f, Functor.flip_map_app,
    curriedTensor_obj_map, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hb]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-_n88joei/lean/Sheaf/Algebra/Homology/TensorResolutionColumnCokernelIso.lean:127:66: warning: This simp argument is unused:
  hb

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, columnAugmentation, chainTensorMap, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.flip_obj_map, curriedTensor_map_app, ← tensorHom_id,
    tensorBicomplexMap, Functor.mapBifunctorHomologicalComplex_map_app_f_f,
    Functor.mapBifunctorHomologicalComplex_obj_map_f_f, flipFunctor_map_f_f, Functor.flip_map_app,
    curriedTensor_obj_map, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

(with the modules compiled into /tmp/forced-adaptation-_n88joei/.lbuild) [4.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.Algebra.Homology.TensorResolutionRowCokernelIso
Original against changed dependencies failed:
```
eplacing `←` with `-` to only get that effect and silence this warning.

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-bmjmutig/lean/Sheaf/Algebra/Homology/TensorResolutionRowCokernelIso.lean:149:59: warning: This simp argument is unused:
  tensorHom_comp_tensorHom

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, tensorBicomplexMap, Functor.mapBifunctorHomologicalComplex_map_app_f_f,
    Functor.mapBifunctorHomologicalComplex_obj_map_f_f, curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_id,
    ← id_tensorHom, Category.comp_id, Category.id_comp]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-bmjmutig/lean/Sheaf/Algebra/Homology/TensorResolutionRowCokernelIso.lean:150:4: warning: This simp argument is unused:
  Category.comp_id

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, tensorBicomplexMap, Functor.mapBifunctorHomologicalComplex_map_app_f_f,
    Functor.mapBifunctorHomologicalComplex_obj_map_f_f, curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_id,
    ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/tmp/forced-adaptation-bmjmutig/lean/Sheaf/Algebra/Homology/TensorResolutionRowCokernelIso.lean:150:22: warning: This simp argument is unused:
  Category.id_comp

Hint: Omit it from the simp argument list.
  [apply] simp only [HomologicalComplex.comp_f, tensorBicomplexMap, Functor.mapBifunctorHomologicalComplex_map_app_f_f,
    Functor.mapBifunctorHomologicalComplex_obj_map_f_f, curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_id,
    ← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

(with the modules compiled into /tmp/forced-adaptation-bmjmutig/.lbuild) [3.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
