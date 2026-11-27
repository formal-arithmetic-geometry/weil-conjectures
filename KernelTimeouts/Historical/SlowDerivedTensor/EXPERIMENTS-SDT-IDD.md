# Slow Derived Tensor, round 12: instance difference decomposition

## Evidence and scope

This report is Research A. `[A1]` is a fresh direct child replay in `sdtide2/a.out` using
`ide2-a.lean`; `[A2]` is a fresh compiled-environment audit in `sdtide2/providers.out` using
`ide2-providers.lean`; `[AS]` is an audit of the pinned consumer source named below.
`[R2]` refers to the separate original-root reduction replay in the round-12 strategy report.
The replay uses the round-11 pinned Lean 4.33.1, Mathlib, consumer, and READY4.2 kernel.
The original unreduced checked body has no complete shortcut application; this comparison
therefore pairs the direct canonical application reached through `DerivedCategory` with the
canonical application inside the compiled shortcut body. [A1]

`ide2-a.lean` opens the original twelve theorem binders in one local context, takes the two
original elaborated provider expressions, weak-head reduces each to the monoidal structure,
then extracts the canonical and shortcut applications. It unfolds the shortcut and instantiates
its compiled let spine before extracting the nested canonical application. All three
applications pass `Kernel.check`; their universe levels are compatible and both canonical
heads have levels `[max (u + 1) u', 0, u + 1]`. The canonical applications are structurally
different and Kernel DefEq. The 19 arguments and their inferred types are compared separately
in the same context. [A1]

## Canonical application arguments

The canonical declaration is
`HomotopyCategory.MonoidalCategory.instMonoidalCategory`. Its source parameters are in
`WeilConjectures/FromJoel/Algebra/Homology/HomotopyCategory/Monoidal.lean` (the variable block
and final instance). The shortcut is
`instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures` in
`WeilConjectures/CategoryTheory/Monoidal/Instances/HomotopyCategory.lean`. In this table,
`=` means structural Expr equality; `D` means structurally different. Every value pair and
every inferred-type pair is Kernel DefEq; `T-D` marks a structurally different inferred type.
Full first-difference paths and exact application heads are in `a.out`. [A1, AS]

| Index | Canonical role / inferred type | Direct provider -> shortcut-body provider | Expr / type | First value diff path |
|---:|---|---|---|---|
| 0 | `C : Type` | same sheaf type | = / = | none |
| 1 | `Category C` | same full-subcategory category | = / = | none |
| 2 | `Preadditive C` | same `Abelian.toPreadditive` | = / = | none |
| 3 | `MonoidalCategory C` | same `Etale.sheafMonoidalCategory` | = / = | none |
| 4 | `HasZeroObject C` | same `Abelian.hasZeroObject` | = / = | none |
| 5 | `(curriedTensor C).Additive` | `MonoidalPreadditive.instAdditiveFunctorCurriedTensor` -> `_proof_3` | D / = | `root/fn/fn/fn/fn/fn` |
| 6 | `forall X, ((curriedTensor C).obj X).Additive` | direct lambda -> `_proof_4` | D / = | `root` |
| 7 | `I : Type` | same `Int` | = / = | none |
| 8 | `AddMonoid I` | same `Int.instAddMonoid` | = / = | none |
| 9 | `c : ComplexShape I` | `ComplexShape.up` with expanded `IsRightCancelAdd Int` provider -> `ComplexShape.up` with `_proof_2` | D / = | `root/fn/arg` |
| 10 | `c.TensorSigns` | same `ComplexShape.instTensorSignsIntUp` | = / = | none |
| 11 | `forall X1 X2 : GradedObject I C, X1.HasTensor X2` | `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory._proof_3` -> shortcut `_proof_1` | D / T-D | `root/fn/fn/fn/fn` |
| 12 | left tensor preserves empty colimits | direct lambda -> `_proof_5` | D / = | `root` |
| 13 | right tensor preserves empty colimits | direct lambda -> `_proof_6` | D / T-D | `root` |
| 14 | graded four-object tensor coherence | `DerivedCategory..._proof_4` -> `_proof_7` | D / = | `root/fn/fn/fn/fn` |
| 15 | graded `HasGoodTensor12` coherence | `DerivedCategory..._proof_5` -> `_proof_8` | D / = | `root/fn/fn/fn/fn/fn` |
| 16 | graded `HasGoodTensor23` coherence | `DerivedCategory..._proof_6` -> `_proof_9` | D / = | `root/fn/fn/fn/fn` |
| 17 | `DecidableEq I` | same `Int.instDecidableEq` | = / = | none |
| 18 | `forall K1 K2, HasMapBifunctor K1 K2 (curriedTensor C) c` | direct lambda -> `_proof_12` | D / T-D | `root` |

Nine arguments are structurally equal and ten differ. The three structurally unequal
argument types are 11, 13, and 18; their first differences are respectively a graded
`HasTensor` proposition shape, `Functor.obj` versus `tensorRight`, and the
`IsRightCancelAdd Int` witness inside `ComplexShape.up`. The first difference in the whole
canonical application is argument 5 (`instAdditiveFunctorCurriedTensor` versus `_proof_3`),
not argument 9. Equal printed result types alone would have missed these differences. [A1]

The direct generated providers at arguments 11 and 14-16 come from
`WeilConjectures/CategoryTheory/Monoidal/Instances/DerivedCategory.lean`'s
`monoidalCategoryOfMonoidalClosedBraidedCategory` instance. The common canonical
recipe itself comes from `HomotopyCategory/Monoidal.lean`'s `.ofBifunctor` instance;
the shortcut re-elaborates its own instance arguments at the separate source site. [A1, AS]

## Generated providers and source origin

All `_proof_1` through `_proof_12` declarations are opaque theorems, not definitions or
registered instance declarations. `providers.out` records their exact pretty-printed types,
their Expr paths in the compiled shortcut body, and a dependency scan of their theorem values.
The shortcut source has one local `have` for the graded tensor witness followed by
`inferInstance`; the other declarations are generated while elaborating that instance and
its inferred canonical arguments. [A2, AS]

| Declaration | Exact proposition family / compiled location | Canonical connection |
|---|---|---|
| `_proof_1` | `forall X1 X2 : GradedObject Int A, X1.HasTensor X2`; local `have` value | arg 11 |
| `_proof_2` | `IsRightCancelAdd Int`; three occurrences in compiled body, including `ComplexShape.up` | arg 9 and dependent terms |
| `_proof_3` | `(curriedTensor A).Additive` | arg 5 |
| `_proof_4` | `forall X1, ((tensoringLeft A).obj X1).Additive` | arg 6 |
| `_proof_5` | `forall X1, PreservesColimit (Functor.empty A) ((curriedTensor A).obj X1)` | arg 12 |
| `_proof_6` | `forall X2, PreservesColimit (Functor.empty A) (tensorRight X2)` | arg 13 |
| `_proof_7` | four graded objects and indices: preservation of a `mapTrifunctor` colimit by left tensor | arg 14 |
| `_proof_8` | three graded objects and indices: preservation of a `mapBifunctor` colimit by right tensor | arg 15 |
| `_proof_9` | three graded objects and indices: preservation of a `mapBifunctor` colimit by left tensor | arg 16 |
| `_proof_10` | `(curriedTensor A).PreservesZeroMorphisms` | no occurrence in shortcut body or generated theorem bodies |
| `_proof_11` | `forall X1, ((curriedTensor A).obj X1).PreservesZeroMorphisms` | no occurrence in shortcut body or generated theorem bodies |
| `_proof_12` | graded `HasTensor` hypothesis implies coproducts for `mapBifunctorHomologicalComplex` components | arg 18 |

`_proof_2` is special: its proposition is an integer cancellation class used *inside the
data expression* `ComplexShape.up`, and its value head is the expanded provider
`instIsRightCancelAddOfAddRightReflectLE`. It is not one of the ten canonical class
arguments generated as `_proof_3` through `_proof_12`. `_proof_1` is the shortcut's
source-level graded tensor `have`. The exact elaboration step that emitted unused
`_proof_10` and `_proof_11` remains unidentified; their absence from the compiled
shortcut and generated theorem-value graph is directly checked. [A1, A2, AS]

## Structure-field provenance

The fields below are fully exposed by WHNF of isolated, well-typed projections of the
direct canonical and shortcut applications. Each is structurally different and each
pair is Kernel DefEq. Every field's first unequal leaf is the expanded
`instIsRightCancelAddOfAddRightReflectLE ...` on the direct side versus shortcut
`_proof_2` on the other, originating in canonical argument 9. This is a witness inside
`ComplexShape.up`; its propagation into field *types* is checked separately by the
recorded first type-difference paths. Other differing arguments above remain independent
representation differences and are not ruled out by a first-leaf map. [A1]

| Parent data field | First value difference path | Classification |
|---|---|---|
| `tensorObj` | `root/domain/arg/fn/arg` | witness in dependent data |
| `whiskerLeft` | `root/domain/arg/fn/arg` | witness in dependent data |
| `whiskerRight` | `root/domain/arg/fn/arg` | witness in dependent data |
| `tensorHom` | `root/domain/arg/fn/arg` | witness in dependent data |
| `tensorUnit` | `root/fn/fn/fn/arg/arg/fn/arg` | witness in data expression |
| `associator` | `root/domain/arg/fn/arg` | witness in dependent data |
| `leftUnitor` | `root/domain/arg/fn/arg` | witness in dependent data |
| `rightUnitor` | `root/domain/arg/fn/arg` | witness in dependent data |

| Law field | First value difference path | Classification |
|---|---|---|
| `tensorHom_def` | `root/fn/fn/arg/arg/fn/arg` | proof with dependent proposition |
| `id_tensorHom_id` | `root/fn/fn/arg/arg/fn/arg` | proof with dependent proposition |
| `tensorHom_comp_tensorHom` | `root/fn/fn/arg/arg/fn/arg` | proof with dependent proposition |
| `whiskerLeft_id` | `root/fn/fn/arg/arg/fn/arg` | proof with dependent proposition |
| `id_whiskerRight` | `root/fn/fn/arg/arg/fn/arg` | proof with dependent proposition |
| `associator_naturality` | `root/domain/arg/fn/arg` | proof with dependent proposition |
| `leftUnitor_naturality` | `root/fn/fn/fn/fn/arg/arg/fn/arg` | proof with dependent proposition |
| `rightUnitor_naturality` | `root/fn/fn/fn/fn/arg/arg/fn/arg` | proof with dependent proposition |
| `pentagon` | `root/fn/fn/fn/fn/arg/arg/fn/arg` | proof with dependent proposition |
| `triangle` | `root/fn/fn/fn/fn/fn/fn/fn/arg/arg/fn/arg` | proof with dependent proposition |

For all 18 fields, the first structural difference in the inferred type is also
argument 9's witness. `tensorUnit` has type path `root/fn/fn/arg/arg/fn/arg`;
the other 17 type paths are `root/domain/arg/fn/arg`. The map does not claim
that `_proof_2` is the only difference in these large expressions. [A1]

## Classification and cross-reference

The shortcut wrapper, its compiled lets, and the common canonical head are exposed by
ordinary delta, zeta, and beta reduction. This accounts for a representation layer that
disappears under reduction. The generated theorem arguments and `_proof_2` differ as
proof expressions; Kernel DefEq accepts the corresponding well-typed proof arguments.
The whole `ComplexShape.up` terms and all 18 field values are different data Exprs yet
Kernel DefEq. Arguments 11, 13, and 18, and every field's inferred type, also exhibit
structural differences in dependent types. [A1, A2]

The structural difference is distributed: besides `_proof_2` and the graded tensor
witness, arguments 5, 6, 12-16, and 18 have independently different providers. No
first-difference origin in the 18 fields remains unidentified, but this experiment does
not enumerate every deeper unequal subtree in every field. `_proof_10` and `_proof_11`'s
exact generation trigger is unknown. [A1, A2, AS]

Research B links the observed shortcut application to original-root event 183 and
the nested canonical head to event 184. That event relationship establishes *when*
the body becomes visible; the A-track field map does not itself explain side selection.
See `EXPERIMENTS-SDT-RSR.md` and `sdtide2/root-focused.jsonl`. [A1, R2]
