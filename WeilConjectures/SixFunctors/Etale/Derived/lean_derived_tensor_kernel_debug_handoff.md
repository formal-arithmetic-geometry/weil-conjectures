# Lean / mathlib Derived Tensor Kernel DefEq Performance Debugging Handoff

## 1. Context

This work is based primarily on:

- mathlib4 PR: https://github.com/leanprover-community/mathlib4/pull/25848
- the new monoidal structure on `DerivedCategory`
- the use of `MonoidalClosed` and `BraidedCategory`/`SymmetricCategory` to avoid older “good tensor” infrastructure

The concrete application is the derived tensor product on Etale sheaves.

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

The relevant monoidal structures on Etale sheaves are already available and do not cause noticeable elaboration-performance problems on their own.

The problem appears only when using the abstract derived-category tensor infrastructure on this concrete sheaf category.

The key symptom is:

> elaboration is fast, but kernel type checking takes around one to two minutes.

At this point the problem has been narrowed down very clearly to **kernel definitional equality (`isDefEq`)**, not elaboration, typeclass search, or proof construction.

---

# 2. Main Reproducers

## 2.1 Minimal `tensorObj` reproducer

This is currently the best small reproducer:

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

This takes about **50–60 seconds** in kernel checking.

If the sheaf category is replaced by an abstract category `A` satisfying the same relevant assumptions, the performance problem disappears.

Therefore:

> the problem is not intrinsic to the abstract `DerivedCategory` / `DerivedMonoidal` construction itself;
> the Etale-sheaf instance graph is necessary to trigger or amplify the bad kernel reduction path.

---

## 2.2 Final simplified target

The original application can be reduced to:

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

Kernel checking for this declaration takes roughly **two minutes**.

---

# 3. Confirmed Facts

The following points have been experimentally established.

## 3.1 Typeclass synthesis is not the bottleneck

For example:

```lean
#synth MonoidalCategory (DerivedCategory C)
```

and:

```lean
#synth (DerivedCategory.Q (C := C)).LaxMonoidal
#synth (DerivedCategory.Qh (C := C)).LaxMonoidal
```

all finish in under about 0.5 seconds.

So the issue is not slow typeclass search.

---

## 3.2 Skipping kernel checking removes the delay

Using:

```lean
set_option debug.skipKernelTC true
```

reduces the problematic declarations from one or two minutes to roughly 0.1–0.5 seconds.

Therefore the bottleneck is definitively in kernel checking.

---

## 3.3 The RHS theorem application is cheap by itself

For example:

```lean
def foo_raw :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor
    (Sheaf X.smallEtaleTopology A)
```

kernel-checks in under 0.1 seconds.

So the theorem application itself is not expensive.

---

## 3.4 The explicit target type is also cheap by itself

If the RHS is replaced by `sorry`:

```lean
lemma foo_sorry :
    (curriedTensor
      (DerivedCategory
        (Sheaf X.smallEtaleTopology A))).IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology A)
        (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology A)
        (ComplexShape.up ℤ)) := by
  sorry
```

kernel checking is also under 0.1 seconds.

Therefore:

> the explicit target is cheap;
> the RHS theorem application is cheap;
> the expensive operation is the kernel proving that the inferred RHS type is definitionally equal to the explicitly written target.

---

# 4. Direct Kernel Probe

A custom probe was used to separate:

```text
Kernel.check(value)
```

from:

```text
Kernel.isDefEq(inferredType, declaredType)
```

This is the most important diagnostic result obtained so far.

---

## 4.1 `test_tensorObj`

Measured values:

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

---

## 4.2 Final `IsLeftDerivedFunctor₂` target

Measured values:

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

Again:

> the proof term itself is essentially free;
> the cost is overwhelmingly in `Kernel.isDefEq`.

The fact that both directions are similarly slow is also significant:

> this does not look like a trivial top-level left-vs-right unfolding asymmetry;
> both orientations appear to enter the same expensive recursive reduction path.

---

# 5. Kernel Diagnostics

The `test_tensorObj` reproducer gives extremely large kernel unfold counts.

Representative hotspots include:

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

This shows that the kernel eventually reduces all the way down to additive structure on Hom types.

However, these should currently be treated as **symptoms**, not necessarily the root cause.

The earlier part of the reduction path also repeatedly touches terms such as:

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

Diagnostics also reports attempted unfolding of non-exposed / opaque boundaries such as:

```text
Shrink
equivShrink
getLimitCone
```

So the kernel is definitely entering a deep derived/localization implementation path before eventually reaching additive Hom structure.

---

# 6. Directions Already Tested

The following ideas have already been tried and did not produce meaningful improvement.

They should not be repeated as first-line hypotheses.

---

## 6.1 Raising or overriding the `Qh.HasDerivedMonoidalCategory` instance

No substantial improvement.

There is a custom instance:

```lean
DerivedCategory.hasDerivedMonoidalCategory
    (A : Type u)
    ...
    [Abelian.HasFunctorialFlatResolution A] :
    Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
```

Its proof is currently `sorry`.

Therefore its proof body cannot be responsible for the slow kernel reduction.

---

## 6.2 Explicitly sharing basic instances

Making the dependencies on:

```text
Category A
Abelian A
MonoidalCategory A
MonoidalClosed A
...
```

syntactically explicit did not substantially improve performance.

---

## 6.3 Explicitly sharing `HasDerivedCategory`

Adding an explicit:

```lean
[hDC : HasDerivedCategory C]
```

did not substantially improve performance.

---

## 6.4 Replacing `MonoidalPreadditive`

Replacing the `MonoidalPreadditive` instance locally, even with a `sorry` proof, did not improve performance.

Also:

```lean
MonoidalPreadditive C
```

is a proposition.

Therefore it is unlikely to be the large data-valued object causing the pathological reduction itself.

---

## 6.5 `@[no_expose]` on `DerivedMonoidal.bifunctor` and `DerivedMonoidal.counit`

Both have been tested:

```lean
@[no_expose] CategoryTheory.DerivedMonoidal.bifunctor
@[no_expose] CategoryTheory.DerivedMonoidal.counit
```

There was no performance improvement.

Therefore the bad path is not simply caused by directly unfolding those two definitions.

---

# 7. Current Interpretation

The strongest current interpretation is:

> during kernel `isDefEq`, some recursive subproblem fails to terminate at an appropriate high-level abstraction boundary;
> the kernel then enters derived/localization implementation details;
> from there it eventually unfolds all the way down to Hom-level additive structures;
> this creates hundreds of thousands or millions of reductions.

The key unknown is no longer:

> “which declaration was unfolded most often?”

The important question is:

> **which pair of expressions is the kernel actually trying to prove definitionally equal at the point where the expensive path begins?**

That information is not available from the normal kernel diagnostics.

---

# 8. Recommended Next Step: Instrument Kernel `isDefEq`

The next useful step is to inspect the kernel itself.

Use the exact Lean version required by the project's:

```bash
cat lean-toolchain
```

and check out the matching Lean 4 source revision.

Relevant files:

```text
src/kernel/type_checker.cpp
src/kernel/type_checker.h
src/kernel/environment.cpp
```

The goal is to inspect the recursive kernel call:

```cpp
type_checker::is_def_eq_core(expr const & t, expr const & s)
```

and identify the **deepest slow recursive pair**.

---

## 8.1 Instrument `is_def_eq_core`

For every recursive `is_def_eq_core(t, s)` call:

1. record recursion depth;
2. record start time;
3. on return, if elapsed time exceeds a threshold such as 500 ms, print:
   - recursion depth,
   - elapsed time,
   - LHS head constant,
   - RHS head constant,
   - application arity;
4. for the deepest calls taking more than e.g. 5 seconds, dump the raw LHS and RHS expressions.

The output should look conceptually like:

```text
[DEFEQ-SLOW] depth=47 ms=48120 lhs=Foo.bar rhs=Baz.qux
[DEFEQ-SLOW] depth=46 ms=48125 lhs=Functor.map rhs=Functor.map
[DEFEQ-SLOW] depth=45 ms=48130 lhs=...
```

The most useful line is the **deepest slow pair**.

The shallower ones may merely be waiting for that recursive subproblem to finish.

---

## 8.2 Then instrument `lazy_delta_reduction_step`

Only after the slow pair has been identified.

For that specific recursion depth or head pair, log:

```text
lhs head
rhs head
lhs reducibility hint
rhs reducibility hint
regular-definition height, if applicable
chosen action
```

Possible actions include:

```text
unfold lhs
unfold rhs
try arguments
unfold both
projection reduction
```

The objective is to determine:

> why the kernel entered the expensive reduction path from this particular pair.

This is much more informative than global unfold counters.

---

# 9. Existing Lean-Side Probe

The following Lean code is useful and should be kept.

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
    | .ok ty =>
        pure ty
    | .error _ =>
        throwError m!"Kernel.check failed for {declName}"

  let checkEnd ← IO.monoMsNow

  logInfo m!"Kernel.check(value): {checkEnd - checkStart} ms"
  logInfo m!"inferred type sizeWithoutSharing: {inferredType.sizeWithoutSharing}"
  logInfo m!"Expr.equal inferred declared: {Expr.equal inferredType declaredType}"

  let forwardStart ← IO.monoMsNow

  let forwardResult ←
    match Kernel.isDefEq env lctx inferredType declaredType with
    | .ok result =>
        pure result
    | .error _ =>
        throwError m!"forward Kernel.isDefEq failed for {declName}"

  let forwardEnd ← IO.monoMsNow

  logInfo m!"Kernel.isDefEq inferred → declared:"
  logInfo m!"  result: {forwardResult}"
  logInfo m!"  time:   {forwardEnd - forwardStart} ms"

  let reverseStart ← IO.monoMsNow

  let reverseResult ←
    match Kernel.isDefEq env lctx declaredType inferredType with
    | .ok result =>
        pure result
    | .error _ =>
        throwError m!"reverse Kernel.isDefEq failed for {declName}"

  let reverseEnd ← IO.monoMsNow

  logInfo m!"Kernel.isDefEq declared → inferred:"
  logInfo m!"  result: {reverseResult}"
  logInfo m!"  time:   {reverseEnd - reverseStart} ms"

  logInfo m!"============================================================"
  logInfo m!""
```

Pair it with:

```lean
set_option debug.skipKernelTC true in
lemma test_tensorObj_kernelProbe
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

and run:

```lean
set_option maxHeartbeats 0 in
run_cmd do
  probeKernelDecl ``test_tensorObj_kernelProbe
```

---

# 10. Desired Output From the Local Agent

The next high-value report should contain:

1. the slowest / deepest recursive `is_def_eq_core` pair:
   - recursion depth,
   - elapsed time,
   - LHS head,
   - RHS head;

2. the raw LHS and RHS expressions for that pair;

3. the `lazy_delta_reduction_step` sequence for that pair:
   - current head pair,
   - reducibility hints,
   - regular-definition heights,
   - chosen unfolding action;

4. the first transition where the reduction clearly enters one of:

```text
leftDerived / totalLeftDerived
localization
ShrinkHoms
quotient
Hom
Preadditive / AddCommGroup
```

5. only after that, decide whether:
   - a concrete term should be marked `@[no_expose]`,
   - a definition should be implemented differently,
   - or a high-level API should avoid relying on this definitional equality.

---

# 11. Guiding Principles

At this stage:

- do not prioritize typeclass-search tuning;
- do not prioritize instance priority changes;
- do not assume `MonoidalPreadditive` or `Preadditive` is the root cause merely because additive structures dominate the unfold counters;
- do not modify low-level hotspots such as `Preadditive.homGroup` just because they are unfolded most frequently;
- do not treat the abstract `DerivedCategory` construction itself as sufficient to reproduce the issue, because the abstract case is fast;
- treat the Etale-sheaf setup as a necessary trigger or amplifier;
- use `test_tensorObj` as the primary reproducer;
- focus on the exact recursive kernel `isDefEq` subproblem that first enters the pathological reduction path.

The final objective is to identify:

> the highest-level definitional equality that should have stopped at an abstraction boundary, but instead remained transparent enough for the kernel to descend into an extremely expensive implementation path.
