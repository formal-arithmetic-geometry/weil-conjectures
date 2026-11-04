# Report 1 — `Reproducer.lean`: `exact h2` elaboration timeout and `congr 1` kernel timeout

Diagnosis following `DiagnoseGuide1.md`. All experiments ran on scratch copies; the repository
file `WeilConjectures/Reproducer.lean` was not modified.

## TL;DR

* **Root cause (confirmed by controls):** a *representation mismatch* between two definitionally
  equal spellings of the derived pullback:
  * `moduleObjectDerivedPullback Λ f` — the local regular-`def` wrapper, used to instantiate the
    functor variables of `dncSectionSquareCoherenceVars` and in the explicit parts of the goal;
  * `(f)^*⟦Λ⟧.leftDerivedFunctor` (`L((f)^*⟦Λ⟧)`) — the form in the declared types of upstream
    `leftDerivedUpperStarComp` / `leftDerivedUpperStarId`, hence in the *implicit* functor arguments
    (`F`, `G`, …) of `Iso.app`, `NatTrans.app`, `Iso.symm`, `≪≫` in the goal.

  `h2`'s type and the goal differ in 88 smallest subterms, 85 of them exactly this pair; each pair
  alone is defeq in about 10 ms.
* **Expensive comparison:** at path `type.2.5`, i.e. the first factor of the RHS,
  `(ci'bb.symm ≪≫ eqToIso hR ≪≫ cbi).hom.app (La.obj C)` against the goal's
  `((leftDerivedUpperStarComp Λ i' bb).symm ≪≫ … ≪≫ leftDerivedUpperStarComp Λ b i).hom.app (…)`.
  Comparing the natural transformations is cheap (kernel `HEq` 1.5 s). Comparing their
  `.app X` components gives a kernel deterministic timeout (108 s). In the elaborator, all 8
  arguments of that `NatTrans.app` pair are individually defeq in ≤ 20 ms, but the whole
  application takes 338 s (it succeeds, at 3.7 GB RSS).
* **Mechanism (consistent with all probes; kernel C++ not traced):** `NatTrans.app`,
  `CategoryStruct.comp`, `Functor.map` and `Iso.hom` are structure projection functions with
  `abbrev` reducibility hints (verified). Neither Meta's args-first `tryHeuristic` (it requires a
  non-trivial *regular* head, a matcher, or metavariables; verified in `Lean/Meta/ExprDefEq.lean`)
  nor the kernel's lazy-delta args-first shortcut (regular hints only, per upstream
  `type_checker.cpp`) applies. Both sides are therefore unfolded instead of compared
  argument-wise. The iso composite reduces to a composite of components *in the derived category*,
  whose `CategoryStruct.comp` is again a projection, and so on into the localization machinery.
  This is the guide's Pattern A (conversion beneath a projection) and Pattern D (same-head
  `abbrev` prefers unfolding) together.
* **Working fix (X6):** wrap the compositors so that their *types* use the same spelling as the
  functors (`dncComp Λ f g : mODP (f ≫ g) ≅ mODP g ⋙ mODP f`, `dncId`), state the goal with them,
  and pass the upstream coherence lemmas through thin wrappers. `exact h2` then works under normal
  kernel checking: whole file 30 s wall / 22.8 s user / 2.0 GB, versus 20–24 s for the
  sorried-goal baseline, with axioms `[propext, Classical.choice, Quot.sound]`.
  **Caveat:** this changes the statement, which now uses `dncComp`/`dncId` instead of
  `leftDerivedUpperStarComp`/`Id`. Every bridge I tried back to the original statement (X7a, X7b)
  brings the timeout back.

## Environment

| item | value |
|---|---|
| Lean | 4.33.1 (commit 819816b2e0a3), x86_64 Linux, Release |
| Mathlib | v4.33.1 (lakefile `rev`) |
| repo | branch `slopmaster2` at `55376e1a60` (= `origin/slopmaster2`) |
| machine | 24 cores, 94 GB RAM, **shared and heavily loaded** (load average 40–60 during the runs) |
| options | lakefile `leanOptions` passed by hand: `pp.unicode.fun=true relaxedAutoImplicit=false backward.isDefEq.respectTransparency=false maxSynthPendingDepth=3 warn.sorry=false` (+ `linter.style.longLine=false` for noise) |
| runner | `lake env lean <opts> file.lean` under `/run/current-system/sw/bin/time`, `timeout 2400`, one run at a time |

Because of the load, wall time is noisy (see the `sys` outliers). CPU time and the profiler's
per-phase numbers are more reliable. Each variant ran once (no repetitions).

Scratch layout (session scratchpad `…/scratchpad/diag/`): `prefix.lean` = lines 1–125 of the
reproducer (header, local def, helper lemmas); `ok.lean` / `exact.lean` / `congr.lean` = the three
test theorems; `v_ok|v_exact|v_congr.lean` = prefix + one theorem; `x*.lean` = interventions;
`difftool.lean`, `deftool.lean`, `bisecttool.lean`, `kerneltool.lean` = meta probes; `*.log` = outputs.

## Baseline: async × skipKernelTC matrix

One file per theorem (prefix + the theorem).

| variant | Elab.async | skipKernelTC | result | wall s | user s | sys s | peak RSS |
|---|---|---|---|---|---|---|---|
| `repro_have_ok` | false | false | ok | 24.5 | 19.5 | 2.2 | 2.09 GB |
| | false | true | ok | 18.4 | 16.0 | 1.8 | 2.02 GB |
| | true | false | ok | 19.9 | 21.1 | 1.9 | 2.23 GB |
| | true | true | ok | 16.7 | 15.2 | 1.9 | 2.06 GB |
| `repro_exact_elab_timeout` | false | false | elab timeout (`whnf`) | 53.6 | 49.2 | 2.5 | 2.20 GB |
| | false | true | elab timeout | 39.5 | 36.6 | 2.0 | 2.15 GB |
| | true | false | elab timeout | 47.1 | 48.0 | 2.2 | 2.34 GB |
| | true | true | elab timeout | 49.1 | 46.4 | 2.4 | 2.19 GB |
| `repro_congr_kernel_timeout` | false | false | **kernel** timeout | 225.6 | 142.0 | 35.5 | 3.76 GB |
| | false | true | ok | 22.1 | 18.6 | 2.3 | 2.02 GB |
| | true | false | **kernel** timeout | 149.5 | 135.6 | 12.5 | 3.86 GB |
| | true | true | ok | 21.1 | 19.3 | 2.2 | 2.06 GB |

Conclusions:
* `exact h2` is a pure **elaboration** cost: skipping the kernel changes nothing, and the timeout
  costs about 20–30 s CPU on top of `ok`.
* `congr 1` elaborates fine, and the cost is purely **kernel** (+~120 s CPU, +1.7 GB RSS). It is
  the same conversion problem, just moved to the kernel (see below).
* `Elab.async` plays no role.

## Structural localization

### Structural diff of `type h2` against the goal (Meta level, in situ)

A tactic run after `have h2`: `Expr.equal = false`, **88 smallest differing pairs**.

| category | count | example | isolated `isDefEq` |
|---|---|---|---|
| functor spelling | 85 | `moduleObjectDerivedPullback Λ a` vs `(a)^*⟦Λ⟧.leftDerivedFunctor` | `true`, 6–15 ms each |
| proof-only | 3 | `Functor.congr_obj (congrArg (fun f ↦ mODP Λ f) h₂) C` vs `congrArg (fun f ↦ (mODP Λ f).obj C) h₂` | `true`, 0–1 ms |

No universe, instance or `_proof_n` differences. The 85 functor pairs sit in implicit positions
(paths ending in `.4.6` / `.4.7` etc., i.e. the `F`/`G` arguments of `Iso.app`, `NatTrans.app`,
`Iso.hom`, …). They come from the compositors' declared types. In `h2` those positions are filled
by the named instantiation `P₁ := moduleObjectDerivedPullback Λ (bb ≫ a)`, …; in the goal by the
inferred types of `leftDerivedUpperStarComp …`, which are written with the `L(...)` notation
(`UpperLowerStar.lean:324`, `UpperStarCoherence.lean:431`).

The sum of the isolated pair costs is under 1 s, so the cost lies in *how* the outer conversion
reaches those pairs.

### Top-down Meta-level bisection (default transparency, fresh heartbeat budget per probe)

| pair | result |
|---|---|
| Eq-LHS (`Li'.map (…) ≫ (…).hom`) | true, 43 ms |
| Eq-RHS | timeout (200k heartbeats); **with `maxHeartbeats 0`: true after 338 s, 3.74 GB RSS** |
| LHS first / second factor | true 30 ms / 19 ms |
| RHS first factor `(…).hom.app (La.obj C)` | timeout |
| RHS second factor `Lb.map (…)` | true 16 ms |
| whole type | timeout |

Automatic descent (`type.2` → `type.2.5`):

* `type.2` = RHS `CategoryStruct.comp`: arg 2 `Functor.obj` 14 ms, arg 3 `Functor.obj` 16 ms,
  **arg 5 `NatTrans.app` timeout (26.8 s)**, arg 6 `Functor.map` 13 ms.
* `type.2.5` = `@NatTrans.app _ _ _ _ F G η X`: arg 4 `F` (a `Functor.comp`) 13 ms, arg 5 `G` 12 ms,
  arg 6 `η` (`Iso.hom (… ≪≫ …)`) 20 ms, `X` syntactically equal. **Every argument is cheap, yet
  the application is expensive.** The unifier is not using argument congruence here.

### Kernel P1–P5 controls (guide §5; fresh `mkAuxTheorem … (cache := false)`, in situ)

| probe | `η` (path 2.5.6) | `η.app X` (path 2.5) |
|---|---|---|
| P5 `type(a) = type(b) := rfl` | 0.8 s | 0.8 s |
| P1 `a = a := rfl` | 0.8 s | 0.9 s |
| P2 `b = b := rfl` | 1.2 s | 1.3 s |
| **P3 `HEq a b := HEq.refl a`** | **1.5 s** | **kernel deterministic timeout, 107.7 s** (RSS up to 3.9 GB) |

Self checks, proposition types and the natural-transformation-level comparison are all cheap.
Only the cross-expression conversion *under* `NatTrans.app` is expensive. This is Case B of the
guide almost verbatim.

### Reducibility hints (checked in this environment)

| constant | hints | projection fn |
|---|---|---|
| `NatTrans.app`, `CategoryStruct.comp`, `Functor.map`, `Iso.hom` | `abbrev` | yes |
| `Iso.trans`, `Functor.comp` | `regular 1` | no |

`Lean/Meta/ExprDefEq.lean:1468` (`tryHeuristic`, the args-first attempt in lazy delta) is skipped
unless the head is a non-trivial regular definition, a matcher, **or one side has
metavariables**. The kernel's lazy-delta args-first shortcut is likewise conditioned on regular
hints (upstream `src/kernel/type_checker.cpp`; the C++ source is not shipped with the local
toolchain, so this point rests on the upstream code and was not traced here).

## Mechanism hypothesis

1. The goal and `h2` contain `@NatTrans.app _ _ _ _ F G η X` against `@NatTrans.app _ _ _ _ F' G' η' X`.
   They differ only by `mODP f` against `L(f)` in implicit positions, inside `F`/`G` and inside the
   implicit arguments of `Iso.trans`/`Iso.symm` within `η`.
2. Because `NatTrans.app` has `abbrev` hints and neither side has metavariables, both elaborator
   and kernel unfold it instead of comparing arguments. They whnf `η`: `Iso.trans` unfolds to a
   constructor, giving a composite `α.app X ≫ β.app X ≫ γ.app X` **in the derived category**.
3. That `CategoryStruct.comp` is again an `abbrev` projection, so the derived-category `Category`
   instance is unfolded and the comparison descends into the localization/homotopy-category
   construction rather than comparing `α.app X` with `α'.app X`. Hence the minutes of CPU and
   GBs of memory.

What the controls establish: (1) and the location of the cost (P3 at the `.app` level only), and
the `abbrev` hints and Meta condition. What remains hypothesis: the exact reduction path in step 3
(no C++ trace was done).

Supporting observations:
* Comparisons that share the *same leaf* `τ` and differ only in implicit `F` are cheap. In
  `repro_have_ok` and in X6, the hypotheses `A₁ … U₂` compare
  `(leftDerivedUpperStarComp …).hom.app C` with `c₁.hom.app C` at differing implicit functors with
  no measurable cost (X6 even used the upstream `…_id_left_app`/`…_id_right_app` unchanged for
  `U₁`/`U₂`). Trouble starts only when the transformations differ structurally (an `Iso.trans`
  chain whose own implicit arguments differ), forcing reduction to components.
* X4 (`apply`, unification with metavariables) elaborates in 1.8 s, matching the
  "metavariables enable `tryHeuristic`" clause. Its kernel check still fails, because the kernel
  has no such clause.

## Intervention comparison

| id | change | elaboration | kernel | wall / user / RSS | verdict |
|---|---|---|---|---|---|
| X1 | instantiate the functor variables with `(upperStar Λ x).leftDerivedFunctor` instead of `mODP` | **timeout** at `exact` | – | 50.7 / 47.3 / 2.14 GB | fails: explicit `mODP` occurrences in the goal (`.map`, `.obj`) now mismatch the other way round |
| X2 | `simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, eqToIso.hom, NatTrans.comp_app, eqToHom_app, Functor.map_comp, Category.assoc] at h2 ⊢; exact h2` | 1.35 s ok | **timeout** (86.6 s) | 103 / 98.4 / 3.78 GB | cost *transferred* to the kernel |
| X3 | spell everything (statement + instantiation) as raw `(upperStar Λ f).leftDerivedFunctor` | **statement elaboration** times out (`isDefEq`, at `….leftDerivedFunctor).map`) | – | 45.0 / 41.7 / 2.05 GB | fails. The regular-def wrapper `mODP` actually *protects* the elaborator (args-first on a regular head). A first attempt with untyped `fun f ↦` binders failed for an unrelated reason (metavariable scheme types) |
| X4 | `apply dncSectionSquareCoherenceVars (C := C)`, functor variables assigned *from the goal* by unification; side goals by `case`, 12 leftover functor-equality goals sorried | **1.78 s** ok | **timeout** (113 s) | 129 / 124 / 3.78 GB | elaborator fixed (metavariables, so `tryHeuristic`), kernel not: the instantiated conclusion still mixes spellings |
| **X6** | regular-def wrappers `dncComp`, `dncId` typed in `mODP` form; goal restated with them; thin wrappers for `assoc_app`/`congr_left`/`congr_right` (proved by the upstream terms) | 3.37 s (whole file) | 5.33 s (whole file) | **30.4 / 22.8 / 2.03 GB** | **works**; axioms `propext, Classical.choice, Quot.sound`; statement changed |
| X7a | original statement := X6 theorem applied to the same arguments | **timeout** (elab 30 s) | – | 69.2 / 52.3 / 2.14 GB | the original-vs-X6 conversion is the same bad conversion |
| X7b | original statement: `rw [eC bb a, …, eI B]` with `eC : leftDerivedUpperStarComp Λ f g = dncComp Λ f g := rfl` (Iso-level transport, Pattern A), then X6 | rw 8.7 s, then **timeout** | – | 38.8 / 32.4 / 2.02 GB | Iso-level transport is cheap, but the goal's implicit `F`/`G` remain in `L(...)` form, so the final `exact` still compares mixed spellings under `NatTrans.app` |

X6 core (scratch `x6.lean`):

```lean
def dncComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleObjectDerivedPullback Λ (f ≫ g) ≅
      moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f :=
  leftDerivedUpperStarComp Λ f g

def dncId (X : Scheme.{u}) : moduleObjectDerivedPullback Λ (𝟙 X) ≅ 𝟭 _ :=
  leftDerivedUpperStarId Λ X

theorem dncComp_assoc_app … :
    (dncComp Λ (f ≫ g) h).hom.app K ≫ (dncComp Λ f g).hom.app ((moduleObjectDerivedPullback Λ h).obj K) =
      eqToHom (by rw [Category.assoc]) ≫ (dncComp Λ f (g ≫ h)).hom.app K ≫
        (moduleObjectDerivedPullback Λ f).map ((dncComp Λ g h).hom.app K) :=
  leftDerivedUpperStarComp_assoc_app Λ f g h K
-- dncComp_congr_left/right: copies of dncPullbackComp_congr_left/right with dncComp
-- main theorem: the statement and the `have h` with leftDerivedUpperStarComp/Id ↦ dncComp/dncId;
-- the proof ends in a plain `exact h2`.
```

## Validation

* X6 compiles with normal kernel checking (no `skipKernelTC`, default `maxHeartbeats`), and
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. No sorry in the theorem; the
  helper lemmas `dncSectionSquareCoherenceVars`, `dncMapCancel` are unchanged.
* Total cost of all new declarations is included in the X6 whole-file numbers (the wrappers and
  bridges together cost a few seconds).
* X6 changes the theorem *statement*: it uses `dncComp`/`dncId`, which are definitionally but not
  syntactically `leftDerivedUpperStarComp`/`Id`. Downstream consumers stated with the upstream
  compositors would hit the X7 problem.

## Conclusion and recommendations

1. **Confirmed root cause:** mixing the `moduleObjectDerivedPullback` wrapper with the bare
   `L((f)^*⟦Λ⟧)` spelling. Upstream compositors are typed in the bare spelling, while the local
   instantiation and the explicit parts of the goal use the wrapper. The expensive pair is the
   `NatTrans.app` of the RHS iso composite (path `type.2.5`), whose cost comes from unfolding
   `abbrev` projection heads instead of argument congruence.
2. **Best boundary found:** keep *one* spelling throughout, with the compositors' types in the same
   regular-def spelling as the functors (X6). For slopmaster2 this suggests: `moduleObjectDerivedPullback`
   is used in many files (`ScalarPullbackSquareCoherence.lean`, `InternalScalarPullbackNormalizationData.lean`,
   `ScalarGeometricExchangeRectangle.lean`, `FreeParameterScalarMaps.lean`, `InternalCanonicalTensorPullRouteModel.lean`,
   `InternalPullNormalizationExistence.lean`, …), several of which already `unfold`/`delta` it, a sign
   of the same friction. Consider providing upstream `moduleObjectDerivedPullbackComp` / `…Id`
   typed in terms of `moduleObjectDerivedPullback`, together with their `assoc`/unit lemmas, and
   stating downstream coherence in that vocabulary, rather than mixing it with
   `leftDerivedUpperStarComp`.
3. **Open problem:** a cheap proof of the *original* statement (with `leftDerivedUpperStarComp`).
   X7a/X7b show that bridging after the fact recreates the bad conversion. Untested ideas:
   * restate `dncSectionSquareCoherenceVars` so that its conclusion is already in component form
     (`cia.inv.app C ≫ eqToHom _ ≫ e.hom.app C` etc., no `≪≫`), so the remaining mismatches sit only
     on stuck leaves (`(c).inv.app X`), which were cheap in every observation;
   * a Pattern-A transport lemma whose conclusion takes its implicit `F`/`G` from the goal side
     (`σ.app X ≫ f = k` from `τ.app X ≫ f = k` and `σ = τ`), applied per `NatTrans.app` occurrence;
   * X4-style `apply` (cheap in the elaborator) combined with a statement form whose instantiated
     conclusion is syntactically uniform, so the kernel needs no mixed-spelling conversion.
4. **Caveats:** single runs on a heavily loaded shared machine; kernel C++ reduction path inferred,
   not traced; RSS figures are peak RSS of the whole `lean` process.
