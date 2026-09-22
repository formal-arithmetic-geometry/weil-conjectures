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

---

# 12. How to Run the Diagnostics in This Folder

## 12.1 The Lean-side probes

They live at the bottom of `Tensor.lean`, after `end AlgebraicGeometry`:

| probe | what it answers |
| --- | --- |
| `probeKernelDecl` | §9 — `Kernel.check value` vs `Kernel.isDefEq inferred declared`, both orientations |
| `reportSlow` | §10.1/§10.2 — the **minimal** expensive defeq subproblems, with their raw expressions |
| `explodeDecl` | times every argument pair of one node, to see whether congruence was available |
| `drillDecl` | the same, recursively following the most expensive differing argument |
| `hintsOf` | §8.2 — the reducibility hints `lazy_delta_reduction_step` uses to choose a direction |

Uncomment one of the `run_cmd` driver blocks at the end of the file and run:

```bash
lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false \
  -Dbackward.isDefEq.respectTransparency=false -Dweak.linter.mathlibStandardSet=true \
  -Dweak.linter.style.header=false -DmaxSynthPendingDepth=3 -Dwarn.sorry=false \
  WeilConjectures/SixFunctors/Etale/Derived/Tensor.lean > /tmp/probe.log 2>&1
```

Two things to know about **where the feedback appears**:

* The `-D` flags are required. `lake env lean` does *not* apply `[leanOptions]` from
  `lakefile.toml`, and without `backward.isDefEq.respectTransparency=false` the file
  fails with a spurious "not type-correct under the `implicit` transparency level".
* `lean` buffers its message log: **nothing is printed until the whole file has
  finished elaborating.** A probe that runs for five minutes looks completely silent
  and then prints everything at once. Redirect to a file and wait rather than
  watching the terminal. In VS Code the same output shows up in the infoview when the
  cursor is on the `run_cmd`, with the same all-at-the-end behaviour.

Run times on the reference machine: `probeKernelDecl` + `reportSlow` ≈ 4 min 30 s
total; `explodeDecl` on the `tensorObj` node ≈ 5 min.

## 12.2 The instrumented kernel (§8)

`kernel_defeq_trace.patch` in this folder patches `src/kernel/type_checker.{h,cpp}`
of Lean `v4.33.1`. It splits `type_checker::is_def_eq_core` into a traced wrapper
plus `is_def_eq_core_impl`, and logs the branch taken by
`lazy_delta_reduction_step`. Everything is off unless an environment variable is
set, so the patched binary behaves exactly like a stock one otherwise:

| variable | effect |
| --- | --- |
| `LEAN_DEFEQ_TRACE_MS=<n>` | print `[DEFEQ-SLOW] depth=… ms=… res=… lhs=… rhs=…` for every `is_def_eq_core` call taking ≥ `n` ms |
| `LEAN_DELTA_TRACE_N=<n>` | print the first `n` `[DELTA] depth=… action=… lhs=… [hint] rhs=… [hint]` decisions |
| `LEAN_DELTA_TRACE_MINDEPTH=<n>` | restrict the `[DELTA]` log to `is_def_eq_core` depth ≥ `n` |

Both logs go to **stderr**, unbuffered, so unlike the Lean-side probes they stream
while the check is running.

Build (NixOS; Lean's own dev shell supplies cmake/clang/GMP/libuv):

```bash
git clone --depth 1 --branch v4.33.1 https://github.com/leanprover/lean4.git
cd lean4
git apply /path/to/kernel_defeq_trace.patch
nix --extra-experimental-features "nix-command flakes" develop -c cmake --preset release
cd build/release
nix --extra-experimental-features "nix-command flakes" develop ../.. -c make -j20 stage1
```

Do **not** commit the patch into the lean4 checkout: the githash is what Lean uses to
decide whether existing `.olean` files are loadable, and leaving the tree dirty keeps
it at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, which is exactly the githash of the
released `v4.33.1` toolchain. The resulting `build/release/stage1/bin/lean` therefore
loads the Mathlib `.olean` files that are already built for this project — Mathlib
does **not** have to be recompiled.

Run it against the project by borrowing lake's environment:

```bash
export LEAN_PATH=$(lake env printenv LEAN_PATH)
LEAN_DEFEQ_TRACE_MS=2000 \
  .../build/release/stage1/bin/lean <the same -D flags> \
  WeilConjectures/SixFunctors/Etale/Derived/Tensor.lean
```

with a copy of the reproducer that does **not** carry `set_option
debug.skipKernelTC true`, so that the kernel actually performs the check.

## 12.3 Results already obtained with these tools

`probeKernelDecl` on `test_tensorObj_kernelProbe` (stock `v4.33.1`):

```text
value sizeWithoutSharing: 3095
declared type sizeWithoutSharing: 18845
Kernel.check(value): 3 ms
inferred type sizeWithoutSharing: 5389
Expr.equal inferred declared: false
Kernel.isDefEq inferred → declared: result true, time 85110 ms
Kernel.isDefEq declared → inferred: result true, time 90061 ms
```

`reportSlow` finds exactly one minimal expensive pair, and it is the whole cost:

```text
[DEFEQ-SLOW] depth=13 ms=92531 result=some true
  path = root/∀body×12/a2
  lhs head = CategoryTheory.MonoidalCategoryStruct.tensorObj/5   (size 2293)
  rhs head = CategoryTheory.MonoidalCategoryStruct.tensorObj/5   (size 15749)
```

`explodeDecl` on that node breaks the cost down by argument:

```text
NODE: ms=145413 res=some true  sizes 2293/15749
  fn syntactically equal: false; #args 5/5
  arg0: ms=0      res=some true  sizes  243/1877   DerivedCategory/4 vs CategoryTheory.DerivedMonoidal/6
  arg1: ms=3      res=some true  sizes  243/1877   instCategoryDerivedCategory/4 vs CategoryTheory.instCategoryDerivedMonoidal/6
  arg2: ms=135234 res=some true  sizes 1799/11987  inferInstance/2 vs inferInstance/2
  arg3: SYNTACTICALLY EQUAL
  arg4: SYNTACTICALLY EQUAL
```

So the object-level arguments are free, the *category* and its `Category` instance
are free (0 ms and 3 ms — `DerivedMonoidal L W` unfolds to `D` immediately), and
essentially the entire cost is the single pair

```text
MonoidalCategoryStruct (DerivedCategory (Sheaf X.smallEtaleTopology A))
  =?=
MonoidalCategoryStruct (DerivedMonoidal Qh (HomotopyCategory.quasiIso … (.up ℤ)))
```

i.e. the `MonoidalCategory` instance itself, at 135 s.

Reducibility hints of the declarations on that path (from `hintsOf`):

```text
CategoryTheory.MonoidalCategoryStruct.tensorObj              def/abbrev
CategoryTheory.DerivedMonoidal                               def/regular:2
CategoryTheory.MonoidalCategory.ofBifunctor                  def/regular:5
CategoryTheory.DerivedMonoidal.bifunctor                     def/regular:8
CategoryTheory.Functor.leftDerived₂                          def/regular:7
DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory  def/regular:27
DerivedCategory.Qh                                           def/regular:15
DerivedCategory.Q                                            def/regular:15
CategoryTheory.toDerivedMonoidal                             def/regular:2
CategoryTheory.ShrinkHoms.equivalence                        def/regular:5
```

`tensorObj` being an *abbreviation* matters: in `lazy_delta_reduction_step` the
"try the arguments first" shortcut is guarded by `d_t->get_hints().is_regular()`,
so for `tensorObj` the kernel never attempts congruence and unfolds both sides
instead. Note also that the two head constants are not syntactically equal
(`fn syntactically equal: false`), which is why a purely structural descent stops
at this node.

The open question is therefore narrower than in §7: **why is comparing the two
`MonoidalCategory` instances expensive**, given that
`MonoidalCategory (DerivedCategory C)` is *defined* as
`inferInstanceAs (MonoidalCategory (DerivedMonoidal Qh …))` and should delta-reduce
to the right-hand side in a couple of steps? That is what the `[DELTA]` log of the
instrumented kernel is meant to answer.

## 12.4 Status of the patched kernel

The patch has been built and run against this project (Lean `v4.33.1`, stage1,
githash `819816b2…`, existing Mathlib oleans reused, no Mathlib rebuild). It
streams to stderr *while* the check runs, unlike the Lean-side probes. Running
`test_tensorObj` (with `debug.skipKernelTC` removed) under
`LEAN_DEFEQ_TRACE_MS=3000` produces lines such as:

```text
[DEFEQ-SLOW] depth=30 ms=3955  res=1 lhs=CategoryTheory.Functor.obj/6           rhs=CategoryTheory.Functor.obj/6
[DEFEQ-SLOW] depth=29 ms=3955  res=1 lhs=CategoryTheory.Functor.obj/6           rhs=CategoryTheory.Functor.obj/6
[DEFEQ-SLOW] depth=28 ms=5307  res=1 lhs=CategoryTheory.Functor.obj/6           rhs=CategoryTheory.Functor.obj/6
[DEFEQ-SLOW] depth=27 ms=10566 res=1 lhs=CategoryTheory.NatTrans/6              rhs=CategoryTheory.NatTrans/6
[DEFEQ-SLOW] depth=26 ms=10566 res=1 lhs=Quiver.Hom/4                           rhs=Quiver.Hom/4
[DEFEQ-SLOW] depth=32 ms=3652  res=1 lhs=CategoryTheory.NatTrans.mk/8           rhs=CategoryTheory.NatTrans.mk/8
[DEFEQ-SLOW] depth=31 ms=3652  res=1 lhs=CategoryTheory.Functor.map/8           rhs=CategoryTheory.Functor.map/8
[DEFEQ-SLOW] depth=30 ms=3652  res=1 lhs=CategoryTheory.Functor.whiskerRight/10 rhs=CategoryTheory.Functor.whiskerRight/10
```

Read these **bottom-up by depth**: a shallow line's time includes the time of the
deeper lines nested inside it, so the interesting entry is the *deepest* one whose
time is still close to its parent's — that is the subproblem actually doing the
work, and the shallower frames are merely waiting for it. In the excerpt above the
`Quiver.Hom` / `NatTrans` frame at depth 26-27 costs 10.5 s and its `Functor.obj`
child at depth 28 costs 5.3 s, i.e. the descent has already reached Hom-level
structure by depth ~26.

To get the reduction decisions that led there, re-run with
`LEAN_DELTA_TRACE_N=3000 LEAN_DELTA_TRACE_MINDEPTH=<d>` where `<d>` is a depth just
above the slow frames, and read the `action=` column: `try-args-then-both` is the
congruence shortcut being attempted, `unfold-both` / `unfold-lhs(height)` /
`unfold-rhs(height)` are delta steps. The first `[DELTA]` line mentioning
`leftDerived`, `localization`, `ShrinkHoms`, `Quot`, `Hom` or `Preadditive` is the
transition asked for in §10.4.

A caveat when reading the `ms` column: the kernel memoises successful `is_def_eq`
calls, so an identical pair met a second time is reported as ~0 ms. Times are
wall-clock for that particular invocation, not the intrinsic cost of the pair.

---

# 13. Result: the `is_def_eq_core` Descent Chain

Obtained with the patched kernel, `LEAN_DEFEQ_TRACE_MS=3000`, on `test_tensorObj`
with `debug.skipKernelTC` removed. 173 `[DEFEQ-SLOW]` lines; below is the maximum
time recorded at each recursion depth, which traces the single hot path.

```text
depth= 0 ms=84589  #forall
depth= 1 ms=84589  Eq/3
depth= 2 ms=84589  CategoryTheory.MonoidalCategoryStruct.tensorObj/5
depth= 3 ms=84588  CategoryTheory.Functor.obj/6
depth= 4 ms=84588  CategoryTheory.Functor.obj/6
depth= 5 ms=84588  #proj:CategoryTheory.Functor
depth= 6 ms=84587  CategoryTheory.Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂/10
depth= 7 ms=84587  CategoryTheory.Functor.HasLeftDerivedFunctor₂/9
depth= 8 ms=84587  CategoryTheory.Functor.obj/6
depth= 9 ms=84587  CategoryTheory.Functor.mk/8
depth=10 ms=59656  #lam
depth=11 ms=59656  CategoryTheory.Functor.uncurry._proof_3/12
depth=12 ms=59656  Eq/3
depth=13 ms=33539  CategoryTheory.CategoryStruct.comp/7
depth=14 ms=33539  CategoryTheory.CategoryStruct.comp/7
depth=15 ms=24778  Equiv.toFun/4
depth=16 ms=24778  CategoryTheory.CategoryStruct.comp/7
depth=17 ms=24061  DFunLike.coe/6
depth=18 ms=24060  EquivLike.coe/6
depth=19 ms=24060  Equiv.toFun/4
depth=20 ms=24060  Equiv.invFun/4
depth=21 ms=24060  CategoryTheory.NatTrans.app/8
depth=22 ms=24060  CategoryTheory.Functor.map/8
depth=23 ms=24059  CategoryTheory.NatTrans.app/8
depth=24 ms=24059  #proj:CategoryTheory.NatTrans
depth=25 ms=24059  Quot.lift/6
depth=26 ms=19411  Equiv.invFun/4
depth=27 ms=19411  CategoryTheory.NatTrans.app/8
depth=28 ms=19411  CategoryTheory.Functor.map/8
depth=29 ms=19410  CategoryTheory.NatTrans.app/8
depth=30 ms=19410  #proj:CategoryTheory.NatTrans
depth=31 ms=19410  Quot.lift/6
depth=32 ms= 7846  CategoryTheory.Quotient.lift._proof_1/9
depth=33 ms= 7846  #forall
depth=34 ms= 7846  Eq/3
depth=35 ms= 5620  CategoryTheory.Functor.map/8
depth=36 ms= 3987  CategoryTheory.Functor.map/8
depth=37 ms= 3987  CategoryTheory.Functor.map/8
depth=38 ms= 3761  Eq/3
depth=39 ms= 3212  #forall
depth=40 ms= 3212  Eq/3
```

Reading it against the questions in §10:

**1-2. The slow pair.** Depths 0-9 are a single nested chain with no branching and
essentially no time of their own; all 84.6 s live below depth 9. The pair that
starts the expensive path is the one at depth 2, already identified by the
Lean-side probes:

```text
@MonoidalCategoryStruct.tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inst₁ K L
  =?=
@MonoidalCategoryStruct.tensorObj (DerivedMonoidal Qh (HomotopyCategory.quasiIso … (.up ℤ))) _ inst₂ K L
```

At depth 10 the work splits into two sibling subproblems of 23.4 s and 59.7 s.

**4. Where it enters the implementation.** The transition is at **depth 6**:
`Functor.HasDerivedMonoidalCategory.curriedTensor_hasLeftDerivedFunctor₂`, i.e. a
*field projection out of the `HasDerivedMonoidalCategory` class instance*. Rather
than comparing the two `MonoidalCategory` instances as instances, the kernel has
by then already projected `tensorObj` out of both (depth 2-5) and is comparing the
resulting `((bifunctor L W).obj K).obj L` terms structurally. From depth 6 onwards
it is inside the left-derived-functor construction and can no longer stop.

**3. What happens below.** Depths 8-12 are the giveaway: the kernel compares two
`Functor.mk` structures *field by field*, reaching the proof field
`Functor.uncurry._proof_3` at depth 11. Kernel proof irrelevance does not make a
proof field free — it first has to check that the two proofs' **types** are
definitionally equal, and those types are equations (`Eq/3` at depth 12) between
composites of natural transformations. That is what forces the descent into
`CategoryStruct.comp` (depths 13-16), then into

* `Equiv.toFun` / `Equiv.invFun` / `DFunLike.coe` / `EquivLike.coe` — the
  `ShrinkHoms` equivalence on Hom types, and
* `Quot.lift` (depths 25 and 31) — the homotopy-category quotient.

Depths 21-25 and 27-31 are **the same five-step cycle repeated**
(`NatTrans.app → Functor.map → NatTrans.app → proj NatTrans → Quot.lift`), and
depth 32 re-enters proof-type comparison at `Quotient.lift._proof_1`. This
repetition is the multiplier that turns a handful of unfoldings into the ~700k
`Preadditive.homGroup` / `AddCommGroup.toAddGroup` reductions reported in §5;
those really are symptoms, as §7 suspected.

**5. Where to intervene.** The highest-level definitional equality that should have
stopped at an abstraction boundary is the depth-2 → depth-3 step. Two observations
bear on it:

* `MonoidalCategoryStruct.tensorObj` has reducibility hint `def/abbrev`. In
  `lazy_delta_reduction_step` the "compare the arguments instead of unfolding"
  shortcut is guarded by `d_t->get_hints().is_regular()`, so for an abbreviation it
  is never attempted. The kernel unfolds both sides instead of asking
  `inst₁ =?= inst₂`.
* Asking `inst₁ =?= inst₂` directly is *also* expensive (135 s, §12.3), so making
  the shortcut fire is not by itself a fix. The two instances are
  `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory …` and
  `instMonoidalCategoryDerivedMonoidal …`, and the former is *defined* as
  `inferInstanceAs` of the latter; they ought to meet after a couple of delta
  steps. They do not, which means some argument of the instance — one of the
  `HasDerivedCategory` / `HasDerivedMonoidalCategory` / `Category` instances
  reconstructed along the two routes — is not syntactically shared, and comparing
  *it* is what drags in the chain above.

The next measurement to make is therefore a `LEAN_DELTA_TRACE_N` run pinned at
`LEAN_DELTA_TRACE_MINDEPTH=2`, reading the `action=` column for depths 2-9: it will
say whether the kernel ever tries `try-args-then-both` on the instance pair, and
which side it chooses to unfold on the way into
`curriedTensor_hasLeftDerivedFunctor₂`. Marking `@[no_expose]` further up (§6.5
tried `bifunctor` and `counit`, which sit *below* depth 6 and so cannot help) would
have to target the depth-6 projection or the instance itself.
