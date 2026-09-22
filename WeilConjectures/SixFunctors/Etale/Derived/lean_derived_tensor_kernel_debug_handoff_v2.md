# Lean / mathlib Derived Tensor Kernel DefEq Performance Debugging Handoff

## 1. Context

This work is based primarily on:

- mathlib4 PR: https://github.com/leanprover-community/mathlib4/pull/25848
- the new monoidal structure on `DerivedCategory`
- the use of `MonoidalClosed` and `BraidedCategory` / `SymmetricCategory`
- a concrete application to derived tensor products on Etale sheaves

The ambient assumptions are roughly:

```lean
(A : Type u')
[Category.{u + 1, u'} A]
[Abelian A]
[IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
[MonoidalCategory A]
[MonoidalPreadditive A]
[SymmetricCategory A]
[MonoidalClosed A]
[Abelian.HasFunctorialFlatResolution A]
```

with:

```lean
C := Sheaf X.smallEtaleTopology A
```

The Etale-sheaf monoidal instances themselves elaborate quickly.

The performance problem only appears when the abstract derived-category monoidal infrastructure is instantiated at this concrete sheaf category.

The key symptom is:

> elaboration is fast, but kernel type checking takes roughly one to two minutes.

The problem has now been isolated very precisely to **kernel definitional equality (`Kernel.isDefEq`)**.

## 2. Main reproducers

### 2.1 Minimal `tensorObj` reproducer

```lean
lemma test_tensorObj
    (A : Type u')
    [Category.{u + 1, u'} A]
    [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A]
    [MonoidalPreadditive A]
    [SymmetricCategory A]
    (X : Scheme)
    [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj
      (DerivedCategory (Sheaf X.smallEtaleTopology A))
      _ inferInstance K L
      =
    @tensorObj
      (DerivedMonoidal DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf X.smallEtaleTopology A)
          (ComplexShape.up ℤ)))
      _ inferInstance K L := by
  rfl
```

Kernel checking takes about **50–60 seconds**.

If the sheaf category is replaced by an abstract category satisfying the same abstract assumptions, the performance problem disappears.

Therefore:

> the pathology is not intrinsic to abstract `DerivedCategory` / `DerivedMonoidal`; the Etale-sheaf instantiation is required to trigger or amplify the bad reduction path.

### 2.2 Final simplified target

```lean
instance isLeftDerivedFunctor₂_derivedTensor
    (A : Type u')
    [Category.{u + 1, u'} A]
    [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A]
    [MonoidalPreadditive A]
    [SymmetricCategory A]
    (X : Scheme)
    [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] :
    (curriedTensor
      (DerivedCategory
        (Sheaf X.smallEtaleTopology A))).IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology A)
        (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology A)
        (ComplexShape.up ℤ)) :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor
    (Sheaf X.smallEtaleTopology A)
```

Kernel checking takes roughly **two minutes**.

## 3. Confirmed facts

### 3.1 Typeclass synthesis is not the bottleneck

Examples such as:

```lean
#synth MonoidalCategory (DerivedCategory C)
#synth (DerivedCategory.Q (C := C)).LaxMonoidal
#synth (DerivedCategory.Qh (C := C)).LaxMonoidal
```

finish in under about 0.5 seconds.

### 3.2 Skipping kernel checking removes the delay

With:

```lean
set_option debug.skipKernelTC true
```

the problematic declarations complete in roughly 0.1–0.5 seconds.

### 3.3 The RHS theorem application is cheap by itself

```lean
def foo_raw :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor
    (Sheaf X.smallEtaleTopology A)
```

kernel-checks in under 0.1 seconds.

### 3.4 The explicit target is also cheap by itself

If the same explicit target is given a `sorry` proof, kernel checking is under 0.1 seconds.

Therefore:

> neither side is expensive in isolation; the expensive step is proving that the inferred RHS type and the explicitly written target are definitionally equal.

## 4. Direct kernel probe

The declaration was inserted with `debug.skipKernelTC`, and kernel checking was replayed manually as:

```text
Kernel.check(value)
Kernel.isDefEq(inferredType, declaredType)
```

### 4.1 `test_tensorObj`

```text
value sizeWithoutSharing: 3095
declared type sizeWithoutSharing: 18845

Kernel.check(value): 1 ms

inferred type sizeWithoutSharing: 5389
Expr.equal inferred declared: false

Kernel.isDefEq inferred → declared:
  result: true
  time: 49867 ms

Kernel.isDefEq declared → inferred:
  result: true
  time: 50279 ms
```

Conclusion:

> essentially the entire 50-second cost is the final kernel definitional-equality check.

### 4.2 Final derived-functor target

```text
value sizeWithoutSharing: 885
declared type sizeWithoutSharing: 57603

Kernel.check(value): 1 ms

inferred type sizeWithoutSharing: 57719
Expr.equal inferred declared: false

Kernel.isDefEq inferred → declared:
  result: true
  time: 131963 ms

Kernel.isDefEq declared → inferred:
  result: true
  time: 121742 ms
```

Again, almost all cost is in `Kernel.isDefEq`.

The similar timings in both directions indicate that this is not merely a trivial top-level left/right unfolding asymmetry.

## 5. Earlier kernel diagnostics

Global kernel diagnostics showed very large unfold counts, including:

```text
AddGroup.toSubNegMonoid       ~743k
Preadditive.homGroup          ~711k
AddCommGroup.toAddGroup       ~674k
Functor.obj                   ~658k
NatTrans.app                  ~542k
SubNegMonoid.toAddMonoid      ~460k
CategoryTheory.Functor.map    ~204k
CategoryStruct.comp           ~201k
Quiver.Hom                    ~147k
```

The reduction path also touched:

```text
MorphismProperty.HasLocalization.hD
MorphismProperty.HasLocalization.D
MorphismProperty.HasLocalization.L

instCategoryDerivedCategory._aux_5
instCategoryDerivedMonoidal._aux_5

ShrinkHoms.fromShrinkHoms
ShrinkHoms.equivalence
ShrinkHoms.functor

Functor.rightKanExtension
Functor.totalLeftDerived
Functor.leftDerived₂
DerivedMonoidal.bifunctor

tensorObj

DerivedCategory.Q
DerivedCategory.Qh
toDerivedMonoidal
```

and attempted to unfold existing opaque / non-exposed boundaries such as:

```text
Shrink
equivShrink
getLimitCone
```

These counters are evidence of where the kernel eventually descends, but they are not sufficient to identify the root cause.

## 6. Directions already tested without meaningful improvement

The following have already been tried:

- raising / overriding `Qh.HasDerivedMonoidalCategory`;
- explicitly sharing basic instances;
- explicitly sharing `HasDerivedCategory`;
- replacing `MonoidalPreadditive`;
- adding `@[no_expose]` to:
  ```lean
  CategoryTheory.DerivedMonoidal.bifunctor
  CategoryTheory.DerivedMonoidal.counit
  ```

None produced meaningful improvement.

## 7. New recursive kernel trace

A custom instrumentation of recursive kernel `isDefEq` produced this slow descent chain for `test_tensorObj`:

```text
depth  0- 5   #forall → Eq → tensorObj → Functor.obj ×2 → proj Functor      84589 ms
depth  6      HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂  84587 ms
depth  7- 9   HasLeftDerivedFunctor₂ → Functor.obj → Functor.mk            84587 ms
depth 10-12   #lam → Functor.uncurry._proof_3 → Eq                         59656 ms
depth 13-16   CategoryStruct.comp ×3, Equiv.toFun                          33539 ms
depth 17-20   DFunLike.coe → EquivLike.coe → Equiv.toFun → Equiv.invFun    24060 ms
depth 21-25   NatTrans.app → Functor.map → NatTrans.app → proj → Quot.lift 24059 ms
depth 26-31   the same five-step cycle again                               19410 ms
depth 32-40   Quotient.lift._proof_1 → Eq → Functor.map …                   7846 ms
```

This is currently the most important evidence.

Depths 0–9 are essentially one unbranched chain with no substantial cost of their own. Almost all time is spent below them.

The expensive descent begins after:

```text
HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂
```

and proceeds through:

```text
HasLeftDerivedFunctor₂
→ Functor.obj
→ Functor.mk
→ Functor.uncurry._proof_3
→ Eq
→ CategoryStruct.comp
→ Equiv / NatTrans / Quot.lift
```

## 8. Current interpretation

The current strongest hypothesis is about kernel control flow around `tensorObj`.

The trace suggests that the kernel has already projected / unfolded `tensorObj` from the two `MonoidalCategory` instances instead of first comparing the hidden application arguments.

In lazy delta reduction, the same-head shortcut that tries `is_def_eq_args` before unfolding is guarded by the head definition being `regular`.

The working hypothesis is therefore:

> `tensorObj` is not treated as a regular definition in this situation; the kernel does not first try cheap congruence on its arguments; instead it unfolds the head and descends into the derived-functor implementation, eventually reaching quotient/localization and additive-Hom machinery.

This is a concrete, testable hypothesis.

## 9. Highest-value next experiments

### 9.1 Kernel-control-flow experiment: remove the `is_regular()` guard

In a custom Lean kernel build, locate the same-head shortcut in `lazy_delta_reduction_step`.

Conceptually:

```cpp
if (is_app(t_n) && is_app(s_n) &&
    is_eqp(*d_t, *d_s) &&
    d_t->get_hints().is_regular()) {
    ...
    if (is_def_eq_args(t_n, s_n))
        return reduction_status::DefEqual;
}
```

For diagnostic purposes only, test:

```cpp
if (is_app(t_n) && is_app(s_n) &&
    is_eqp(*d_t, *d_s)) {
```

i.e. remove only:

```cpp
d_t->get_hints().is_regular()
```

Do not change any other logic.

Then rerun only `test_tensorObj`.

Interpretation:

```text
~50 s → milliseconds / <1 s
```

would be strong evidence that the pathological descent is caused by failing to try same-head argument comparison before unfolding this non-regular head.

If runtime is unchanged, this hypothesis is false.

### 9.2 Pure Lean control experiment: regular wrapper around `tensorObj`

Define a normal `def`, not an `abbrev`:

```lean
def tensorObjRegular
    {C : Type u}
    [Category.{v, u} C]
    [MonoidalCategory C]
    (X Y : C) : C :=
  tensorObj X Y
```

Then duplicate the minimal equality using:

```lean
@tensorObjRegular ...
```

on both sides.

If:

```text
test_tensorObj          ~50 s
test_tensorObjRegular   ~milliseconds
```

this independently supports the same reducibility-heuristic diagnosis.

### 9.3 Instrument `is_def_eq_args` specifically for the `tensorObj` head

If either previous experiment gives a large speedup, instrument argument comparison and time each argument pair separately.

The ideal result would look like:

```text
tensorObj argument comparison:
arg 0: 0 ms
arg 1: 0 ms
arg 2: 2 ms
arg 3: 0 ms
arg 4: 0 ms
```

This would establish that the kernel spends tens of seconds unfolding `tensorObj` instead of performing a cheap argument-wise comparison.

## 10. Secondary investigation: `Functor.uncurry._proof_3`

If the `tensorObj` reducibility experiments do not explain the slowdown, the next important node is:

```text
Functor.uncurry._proof_3
```

The trace shows a major descent through:

```text
Eq
CategoryStruct.comp
Equiv.toFun
DFunLike.coe
EquivLike.coe
NatTrans.app
Functor.map
Quot.lift
```

A useful next diagnostic is to instrument the proof-irrelevance path and inspect:

```text
type(lhs proof)
type(rhs proof)
```

for the `_proof_3` comparison.

The question is:

> is the kernel spending tens of seconds proving that the proposition types of two proof fields are definitionally equal before proof irrelevance can discharge the proof terms themselves?

If yes, the `_proof_3` proof body is not the real issue; the expensive part is the definitional equality of its proposition types.

## 11. Recommended debugging order

Use only `test_tensorObj` as the primary reproducer.

1. Remove the `is_regular()` guard in the custom kernel and record runtime.
2. Test `tensorObjRegular` and record runtime.
3. If either gives a major speedup, instrument `is_def_eq_args` for `tensorObj`.
4. If neither helps, move to the depth-10 region and instrument proof irrelevance around `Functor.uncurry._proof_3`.
5. Only after identifying the exact bad transition should `@[no_expose]`, reducibility hints, or mathlib API changes be considered.

## 12. Existing Lean-side kernel probe

```lean
open Lean Elab Command

private def probeKernelDecl (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let lctx : LocalContext := default

  let some info := env.find? declName
    | throwError m!"cannot find declaration {declName}"

  let value := info.value! true
  let declaredType := info.type

  logInfo m!""
  logInfo m!"============================================================"
  logInfo m!"Kernel probe: {declName}"
  logInfo m!"============================================================"

  logInfo m!"value sizeWithoutSharing: {value.sizeWithoutSharing}"
  logInfo m!"declared type sizeWithoutSharing: {declaredType.sizeWithoutSharing}"

  let checkStart ← IO.monoMsNow

  let inferredType ←
    match Kernel.check env lctx value with
    | .ok ty => pure ty
    | .error _ =>
        throwError m!"Kernel.check failed for {declName}"

  let checkEnd ← IO.monoMsNow

  logInfo m!"Kernel.check(value): {checkEnd - checkStart} ms"
  logInfo m!"inferred type sizeWithoutSharing: {inferredType.sizeWithoutSharing}"
  logInfo m!"Expr.equal inferred declared: {Expr.equal inferredType declaredType}"

  let forwardStart ← IO.monoMsNow

  let forwardResult ←
    match Kernel.isDefEq env lctx inferredType declaredType with
    | .ok result => pure result
    | .error _ =>
        throwError m!"forward Kernel.isDefEq failed for {declName}"

  let forwardEnd ← IO.monoMsNow

  logInfo m!"Kernel.isDefEq inferred → declared:"
  logInfo m!"  result: {forwardResult}"
  logInfo m!"  time:   {forwardEnd - forwardStart} ms"

  let reverseStart ← IO.monoMsNow

  let reverseResult ←
    match Kernel.isDefEq env lctx declaredType inferredType with
    | .ok result => pure result
    | .error _ =>
        throwError m!"reverse Kernel.isDefEq failed for {declName}"

  let reverseEnd ← IO.monoMsNow

  logInfo m!"Kernel.isDefEq declared → inferred:"
  logInfo m!"  result: {reverseResult}"
  logInfo m!"  time:   {reverseEnd - reverseStart} ms"

  logInfo m!"============================================================"
  logInfo m!""
```

## 13. Current best hypothesis

The current best hypothesis is:

> the kernel reaches a `tensorObj` comparison whose two applications have the same high-level head but syntactically different hidden arguments; because the head is not considered `regular`, the kernel does not first attempt a cheap argument-wise defeq; instead it unfolds the head, exposing `curriedTensor_hasLeftDerivedFunctor₂`, then `Functor.uncurry`, then category-composition / equivalence / quotient machinery; the comparison eventually descends into localization and additive Hom structure, causing the observed explosion.

This hypothesis is not yet proven.

The two next experiments — removing the `is_regular()` guard and testing a regular wrapper — are intended to confirm or falsify it directly.

## 14. Desired next report

The next useful report should contain:

```text
baseline test_tensorObj:
  ~50 s

custom kernel without is_regular() guard:
  ?

tensorObjRegular wrapper:
  ?
```

If either is fast, also provide:

```text
per-argument timing for is_def_eq_args on the tensorObj application
```

If both remain slow, move to:

```text
Functor.uncurry._proof_3
```

and report:

```text
lhs proof type
rhs proof type
time spent proving those proposition types defeq
```

The goal is now to identify the exact kernel control-flow decision that causes the descent, rather than infer the cause from global reduction statistics.
