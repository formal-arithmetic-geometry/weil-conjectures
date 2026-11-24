# Slow Derived Tensor: Source Instance to Target Morphism Cost Report

## Scope and evidence labels

This round used fresh READY4.2 observational runs on the pinned Lean 4.33.1 / Mathlib
environment. The fresh focused probe compared the exact source and generated fields and
captured parent-child events; the fresh G probe replayed the target-category and
`curriedTensor` controls. No kernel decision or semantic rule was changed. Labels below
mean: **Direct root evidence**, **Direct child replay**, **API-level counterfactual**,
**Inference**, or **Unknown**.

The fresh original root returned `true`: 6,239,463 recursive calls, 72.354 s trace wall
time, 48.009 s comparison-exclusive time, and 24.345 s reduction-exclusive time. The
same run attributed 21.412 s to `map`, 48.869 s to `map_comp`, 0.530 s to `obj`, and
0.962 s to `map_id`. These are same-run field shares; replay times below are not summed
with them. **Direct root evidence.**

## 12.1 Exact source producer

The two source functors are

```lean
F_L = curriedTensor C ⋙
  (Functor.whiskeringRight C C (DerivedMonoidal Qh quasiIso)).obj
    (toDerivedMonoidal Qh quasiIso_L)
F_R = curriedTensor C ⋙
  (Functor.whiskeringRight C C (DerivedMonoidal Qh quasiIso)).obj
    (toDerivedMonoidal Qh quasiIso_R)
```

where `C` is the relevant `HomotopyCategory`. Their printed syntax is identical. The
first exact structural leaf is the universe-instantiated provider
`HomotopyCategory.quasiIso`: `max (succ u) u'` on the left and
`max (max u' (succ u)) u` on the right. The first operational divergence is the sixth
argument of `Functor.comp`, the `curriedTensor` factor. Its left monoidal instance is
`HomotopyCategory.MonoidalCategory.instMonoidalCategory`; its right instance is the
named historical `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures`.
**Direct child replay.**

The source definition is:

```lean
curriedTensor C := {
  obj X := { obj := fun Y => X ⊗ Y, map := fun g => X ◁ g }
  map f := { app := fun Y => f ▷ Y }
}
```

Thus `curriedTensor.obj` uses the `MonoidalCategoryStruct.tensorObj` projection and
the inner functor map uses `whiskerLeft`. `curriedTensor.map` uses
`whiskerRight` in the natural-transformation component. The `MonoidalCategoryStruct`
also exposes `tensorHom`; it is not the first projection reached by this displayed
`curriedTensor` body. Its law fields (`tensorHom_def`, identity/composition laws,
whisker laws, associator/unitors and coherence proofs) occur in the instance terms and
dependent types, and are reached when the generated source fields are compared.
**Direct API evidence plus direct child replay.**

The first source-side operational chain is therefore

```text
different MonoidalCategory instance
  -> tensorObj / whiskerRight / whiskerLeft projections in curriedTensor
  -> different source Functor expressions
  -> source F.map and F.obj terms
```

The direct `F_L`/`F_R` comparison took 372 ms in the fresh focused child replay and
stopped at the composed source representation; it did not compare the generated
uncurried fields. **Direct child replay.**

The quasi-isomorphism universe leaf survives in source and generated field expressions,
but the fresh G controls did not isolate a valid same-typed provider-only replacement.
Its structural presence is observed; its independent cost contribution is unresolved.
**Direct child replay; Unknown for independent causality.**

## 12.2 `DerivedMonoidal` transport

The actual definitions are:

```lean
def DerivedMonoidal (_ : C ⥤ D) (_ : MorphismProperty C) := D
def toDerivedMonoidal : C ⥤ DerivedMonoidal L W := L
instance : Category (DerivedMonoidal L W) := inferInstanceAs (Category D)
```

Consequently `toDerivedMonoidal.obj X` is `L.obj X`, and
`toDerivedMonoidal.map f` is `L.map f`; there is no quotient or localization algorithm
inside this wrapper. In the focused Expr probe, the transported target object has head
`DerivedMonoidal`, its category instance is `instCategoryDerivedMonoidal`, and the
transported map remains a target morphism in `Quiver.Hom` of `DerivedMonoidal`.
**Direct API evidence; Direct child replay.**

The wrapper is cheap as a definition, but it changes the context in which the source
map is compared: the target morphisms are compared using `DerivedMonoidal`'s category
instance and `CategoryStruct.comp`. The fresh parent-child trace shows
`toDerivedMonoidal`/`Functor.whiskerRight` descendants feeding `CategoryStruct.comp`,
`NatTrans.app`, and target `Functor.map` comparisons. **Direct child replay.**

Therefore `DerivedMonoidal` is not an independently sufficient producer: changing only
the target type or target category instance leaves the expensive uncurried comparison.
It is nevertheless a material comparison context because its Hom and composition terms
are the endpoints exposed by `uncurry`. **API-level counterfactual; Inference.**

## 12.3 `uncurry.map`

The exact implementation is:

```lean
map := fun {X} {Y} f =>
  (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
```

The generated target is `Functor (C × C) (DerivedMonoidal ...)`. The fresh field probe
reports `map` as a lambda with a 170,455/148,023 node type (left/right), and the field
comparison is 1,902,386 calls and 21.412 s in the root. **Direct root evidence.**

The exact path is:

1. `F.map f.1` is the outer map of the source composed functor. Its `curriedTensor`
   component carries the inferred/named monoidal-instance difference.
2. `.app X.2` enters the natural-transformation component. The trace reaches
   `CategoryTheory.NatTrans.app` and then `NatTrans.proj`; the `NatTrans.app` delta
   itself is cheap (542,714 unfolds, 0.366 s in the fresh root).
3. `F.obj Y.1` is the inner source functor object action. Its map uses the source
   `whiskerLeft` path.
4. `(F.obj Y.1).map f.2` is the inner `Functor.map` path.
5. `≫` is target `CategoryStruct.comp`, whose result has target `Quiver.Hom` type.

Direct replays from the same focused extraction measured the outer map/`NatTrans.app`
argument at about 20.0 s, the inner map argument at about 0.98 s, and the target
composition body at about 21.2 s. These overlap and are not additive. **Direct child
replay.**

The first expensive target morphism comparison is the target `CategoryStruct.comp`
whose arguments contain the outer `Functor.map`/`NatTrans.app` result and the inner
`Functor.map` result. The source instance difference is still visible in the nested
`whiskerRight`/`whiskerLeft` and `tensorObj` descendants. **Direct child replay.**

## 12.4 `uncurry.map_comp`

The field has five dependent binders: three product objects followed by two product
morphisms. Their domains are `Prod`, `Prod`, `Prod`, `Quiver.Hom`, and `Quiver.Hom`;
all five compare equal, with only domain 0 taking noticeable setup time (2.933 s in
the fresh focused replay). **Direct child replay.**

The conclusion is an `Eq` over target `Quiver.Hom`. Its two endpoints are both
`CategoryStruct.comp` expressions. The focused probe reports:

| endpoint | fresh child replay |
|---|---:|
| equality carrier (`Eq.arg0`) | 3.470 s |
| LHS (`Eq.arg1`) | 23.701 s |
| RHS (`Eq.arg2`) | 43.519 s |

The same-root field attribution is 1.290 s for the carrier, 21.566 s for the LHS, and
26.013 s for the RHS, totaling 48.869 s for `map_comp`. The child replays are separate
overlapping measurements; the same-root partition is the attribution to use for shares.
**Direct root evidence; Direct child replay.**

The LHS expands as `uncurry.map (f ≫ g)`: product morphism composition, one source
`curriedTensor.map`, one outer map/`NatTrans.app`, one inner map, and one target
`toDerivedMonoidal.map`/composition path. The RHS expands as
`uncurry.map f ≫ uncurry.map g`: two uncurried maps followed by target composition.
Thus the RHS exposes an intermediate target morphism and repeats the source map tree.
**Direct API expansion; Direct child replay.**

The fresh strategy trace links the expensive branches by parent and child IDs. It shows
application congruence entering `Functor.map` and `NatTrans.app`, projection and
second-WHNF descending through `CategoryStruct.comp`, and lazy-delta/WHNF exposing
`MonoidalCategoryStruct.tensorObj`, `whiskerLeft`, and `whiskerRight`. Proof
irrelevance is entered for the proof field, but the proof body is not compared; the
dependent proposition type is compared instead. **Direct root evidence; Direct child
replay.**

The RHS is 4.447 s more expensive in same-root exclusive attribution (26.013 minus
21.566). The exact child accounting identifies the extra RHS target composition and
its intermediate `Functor.map`/Hom structure as the responsible branch. It is not an
object-count explanation. **Direct root evidence; Inference from the exact endpoint
tree.**

## 12.5 Cheap fields

`obj` compares object actions (`tensorObj` followed by `toDerivedMonoidal.obj`) and does
not construct a target morphism composition. It costs 56,018 calls / 0.530 s.
`map_id` is proof-irrelevant, but its proposition has an identity-shaped endpoint and
does not contain the two-map composition tree of `map_comp`; it costs 84,173 calls /
0.962 s. **Direct root evidence; Inference for the structural reason.**

## 12.6 Source/target interaction and controls

Fresh G measurements:

| control | fresh result |
|---|---|
| source `F` comparison | 28223 calls, about 0.31--0.37 s |
| G target-category argument (`source arg5`) | source 306 ms; uncurried 63.937 s |
| G `curriedTensor` argument (`source arg6`) | source 2 ms; uncurried 6 ms |
| original focused uncurried fields | 76.755 s (`arg4` replay), 83.259 s (`arg7` replay), root 72.354 s |

The target-category-only control retains the expensive path. Aligning the
`curriedTensor` factor removes it. Existing one-factor controls G1, G5, and G6 likewise
retain the expensive path, while G4 (monoidal-instance argument only) makes `F` about
2 ms, `U` about 5 ms, and all fields about 0--3 ms. These are API-level rebuilt
expressions and do not preserve the original M0 theorem obligation. **API-level
counterfactual.**

The demonstrated interaction is: the source monoidal instance creates the unequal
source morphism representation; `toDerivedMonoidal` places it in target Hom and
composition terms; `uncurry` repeats those terms in data and dependent fields. The
target representation is therefore a material amplifier/context, but target-only
replacement is insufficient. **Direct child replay; API-level counterfactual;
Inference.**

The F2/F3 alternative type-preserving target representation was not constructible in
the pinned API without changing the target type or the original theorem terms. Thus F
has fresh source/target interaction evidence from the target-only and aligned-source
controls, but no independent alternative-target measurement. **Unknown; API-level
counterfactual limitation.**

## 12.7 Causal conclusion

**Source mismatch is materially amplified by the target `DerivedMonoidal` Hom/composition
representation.** The sufficient producer-level observation is the differing
`curriedTensor` monoidal instance: aligning that one argument collapses the uncurried
comparison. The amplification mechanism is independently observed: `toDerivedMonoidal`
is definitionally `L`, while `uncurry.map` and especially the dependent `map_comp`
equality expose the source map structure as target `Quiver.Hom` and
`CategoryStruct.comp` comparisons. The fresh root assigns 29.8% to `map` and 68.1% to
`map_comp`; the RHS endpoint is the larger endpoint. **Direct root evidence; Direct
child replay; API-level counterfactual.**

The selected right Kan extension and counit are not primary causes: the original-root
trace does not enter their bodies. **Direct root evidence.** The exact contribution of
the universe-normalized `quasiIso` leaf, and the exact per-field causal split among
individual monoidal law proofs, remains unresolved. **Unknown.**

## Answers to §13

1. **Direct root evidence:** `F_L` and `F_R` are the two `curriedTensor C` compositions above, each postcomposed through `whiskeringRight` with `toDerivedMonoidal Qh quasiIso`.
2. **Direct child replay:** left `HomotopyCategory.MonoidalCategory.instMonoidalCategory`; right named `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures`.
3. **Direct API evidence:** `obj` uses `tensorObj`; the inner map uses `whiskerLeft`; the outer natural-transformation map uses `whiskerRight`; `tensorHom` and law/coherence fields occur in the instance-dependent representation.
4. **Direct child replay:** `F.map f.1` enters `NatTrans.app`, while `(F.obj Y.1).map f.2` enters the inner map; both retain the source instance terms.
5. **Direct root evidence:** both equality endpoints contain `uncurry.map`; the RHS contains two uncurried maps plus target composition, and both endpoints retain the source mismatch.
6. **Direct API evidence:** `toDerivedMonoidal.map f` is `Qh.map f` at the definitional level; it changes the target Hom/category context.
7. **Direct child replay:** target `Quiver.Hom` carriers and `CategoryTheory.CategoryStruct.comp` endpoints, with `NatTrans.app`, `Functor.map`, projections, WHNF and lazy delta below them.
8. **Direct root evidence:** `map_comp` compares a dependent equality proposition with two composition endpoints; same-root cost is 48.869 s versus 21.412 s for `map`.
9. **Direct root evidence; Inference:** `obj` lacks morphism composition; `map_id` has one identity-shaped endpoint rather than two nested maps and a target composition.
10. **Direct child replay; API-level counterfactual:** `DerivedMonoidal` materially amplifies the source mismatch through target Hom/composition, but does not independently produce it.
11. **API-level counterfactual:** target-category-only replacement stays expensive; `curriedTensor` alignment is cheap; this demonstrates source producer plus target-context amplification.
12. **Unknown:** the independent cost of the universe-instantiated `quasiIso` leaf and the exact contribution of each individual monoidal law proof are not isolated by a valid same-typed control.

## Reproducibility and limits

Reduced fresh measurements and the bounded parent-child strategy trace are in `sdtstm/`.
Each reduced file is below 5 MB; no raw trace was copied into the repository. The
instrumentation is observational and the run used at most three Lean processes. The
Weil filesystem remained below the 90% limit. No commit or push was performed.
