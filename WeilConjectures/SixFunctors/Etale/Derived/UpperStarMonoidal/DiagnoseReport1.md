# Kernel performance of `UpperStarMonoidal/Comparison.lean`: diagnosis report 1

This report follows `DebugInstruction1.md`. It continues `DiagnoseReport.md`, whose conclusions it
assumes. It covers the two requested experiments: controls for the `HEq` conversion probe, and
an exact-binder-type auxiliary theorem for the `hδ` argument of `ofLaxSquare`.

## Setup

* Lean `v4.33.1`, Mathlib `v4.33.1`, branch `slopmaster2-diagnose-1` at `0798f9a8b3`.
* Every run uses `lake env lean` with the `leanOptions` of `lakefile.toml` passed as `-D` flags,
  plus `-DElab.async=false -Ddebug.skipKernelTC=false -Dtrace.profiler=true
  -Dtrace.profiler.threshold=500`. Per-declaration kernel times are the
  `[Kernel] typechecking declarations [...]` trace entries. Wall time and peak memory come from
  GNU `time -v`.
* Machine: 24 cores, 94 GB RAM. **All runs were sequential** (one Lean process at a time).
* Variant files were generated from the unchanged `Comparison.lean` in the session scratchpad and
  were not committed.

## Experiment 1: controls for the `HEq` probe

The pair is the one at `lhs.5.6` in the previous report, taken from `type(h)` and the goal just
before `exact h` in `leftDerivedUpperStarTensorComparison_app_app_comp`:

```lean
-- a (from `Functor.leftDerived₂NatTrans_app_app`)
NatTrans.app ((derivedTensorLeftDerivedUpperStar A g).leftDerived₂NatTrans …) (Qh.obj K)
-- b (from the statement)
NatTrans.app (leftDerivedUpperStarTensorComparison A g) (Qh.obj K)
```

`a == b` is false: the heads of the natural-transformation arguments are
`Functor.leftDerived₂NatTrans` and `leftDerivedUpperStarTensorComparison`.

Each probe ran in **its own Lean process**, on the file truncated after the lemma, with
`exact h` replaced by the probe followed by `sorry`. The probe adds the theorem with
`Lean.Meta.mkAuxTheorem ty val (cache := false)`, so nothing is shared between probes. Times are
the kernel trace entry of the generated `_proof_2`. The wall-clock time around `mkAuxTheorem`
agrees to within 0.3 s.

| probe | type | proof | succeeds | kernel time | process peak memory |
|---|---|---|---|---|---|
| P1 | `HEq a a` | `HEq.refl a` | yes | 3.5 s | 2.5 GB |
| P2 | `HEq b b` | `HEq.refl b` | yes | 0.03 s | 2.5 GB |
| P3 | `HEq a b` | `HEq.refl a` | yes | **303.2 s** | **8.3 GB** |
| P4 | `HEq a b` | `sorry` | yes | 2.1 s | 2.3 GB |
| P5 (extra) | `type(a) = type(b)` | `Eq.refl` | yes | 0.05 s | 2.5 GB |

P5 isolates the conversion of the two *types*, which `HEq.refl a : HEq a b` also needs.

(P3 also prints a `maxHeartbeats` timeout at the enclosing `by`, because the
`set_option maxHeartbeats 0` covered only the `run_tac`. The probe itself finished and its
declaration was accepted.)

**What it establishes.** P1, P2, P4 and P5 together account for under 6 s. P3 costs 303 s and
pushes peak memory from 2.5 GB to 8.3 GB. So the cost really is the cross-expression
definitional equality `a ≡ b`: not checking `a` or `b` on their own, not forming the
proposition, and not comparing their types. This is the "P1/P2/P4 fast, P3 very slow" case of the
instructions. The 280–303 s figure is a reliable measure of conversion cost.

## Experiment 2: exact binder-type auxiliary theorem for `hδ`

### Step 1: the instantiated `hδ` binder type

A `run_meta` step reads the elaborated value of a kernel-unchecked copy of the def
(`oplaxProbe`, identical body). Under `lambdaTelescope`, the body is
`ofLaxSquare.{u+1, max (u+1) u', …}` applied to 28 arguments, and `hδ` is argument 22. The binder
type is then computed **the way the kernel does it**: the `Π`-binders of `ofLaxSquare`'s type are
instantiated one argument at a time with `Expr.instantiate1`, with no beta-reduction. The result
(`P_raw`) is:

```lean
∀ (a b : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (ComplexShape.up ℤ)),
  ((leftDerivedUpperStarTensorComparison A g).app (Qh.obj a)).app (Qh.obj b) ≫
      ((fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a) a ⊗ₘ
        (fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a) b) ≫
        μ Qh (((g)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)).obj a)
          (((g)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)).obj b) =
    L((g)^*[A]).map (μ Qh a b) ≫
      (fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a) (a ⊗ b) ≫
        Qh.map (δ ((g)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)) a b)
```

`P_beta := Core.betaReduce P_raw`. Structural `Expr` diffs (the smallest differing subterm pairs,
descending while head and arity agree):

| comparison | differing pairs | nature of the differences |
|---|---|---|
| `P_raw` vs `P_beta` | 3 | exactly the three beta-redexes `(fun a ↦ counit.app a) x`, for `x = a`, `b`, `a ⊗ b` |
| `type(…_app_app_comp A g)` vs `P_raw` | 726 | hidden arguments only (below) |
| `type(…_app_app_comp A g)` vs `P_beta` | 810 | the same kinds |

The 726 differences between the lemma's own statement and the binder type all print the same.
They are:

* **Universe levels:** 42 × `DerivedCategory.{u+1, u+1, max (max u' (u+1)) u}` against
  `{u+1, u+1, max (u+1) u'}`, and 7 × `Functor.{…}` with similarly unnormalized `max` levels.
* **Instance paths:** e.g. 80 × `Preadditive.fullSubcategory` against `Abelian.toPreadditive`,
  `HomotopyCategory.MonoidalCategory.instMonoidalCategory` against
  `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures`, `Sheaf.monoidalPreadditive`
  against `leftDerivedUpperStarTensorComparison._proof_5`, `hasDerivedMonoidalCategory` against
  `leftDerivedUpperStarUnitIso._proof_2`.
* **Auxiliary proof constants:** 219 × `instIsRightCancelAddOfAddRightReflectLE` against
  `leftDerivedUpperStarTensorComparison._proof_1`, plus many `derivedTensorLeftDerivedUpperStar._proof_n`
  against `…TensorComparison._proof_m`. These are the same proofs, picked up from different
  declarations.
* **Object representations:** e.g. `derivedTensorLeftDerivedUpperStar …` against
  `Functor.obj …`, `Functor.comp …` against `Qh`, and lambdas against constants.
* 280 `fvar` against `fvar` pairs, which are bound variables of the binder telescope at
  differing positions (the `a`, `b` above).

The lemma's statement also contains 7 beta-redexes of its own, against 3 in `P_raw`.

So the expensive conversion in the original def is **not mainly a beta-redex issue**. The lemma
statement (elaborated in the lemma's context) and the binder type (elaborated in `ofLaxSquare`'s
context) differ in hundreds of hidden instance, universe and proof arguments.

### Step 2: auxiliary theorems

Both theorems are added by the same `run_meta` step with `addDecl` (kernel checking on):

* **B1** `delta_raw : ∀ (section variables), P_raw := fun … ↦ leftDerivedUpperStarTensorComparison_app_app_comp A g`
* **B2** `delta_beta : ∀ (section variables), P_beta := (same value)`

The variables are exactly the 13 lambda binders of the original def, with their binder infos and
the def's universe parameters. The value is the literal argument 22 of the original
application. The def is then written in source as before, with only `hδ` changed:

```lean
noncomputable def leftDerivedUpperStarOplaxMonoidal : L((g)^*[A]).OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh (Sheaf Z.smallEtaleTopology A)
  Functor.OplaxMonoidal.ofLaxSquare (Q₁ := Qh) (Q₂ := Qh)
    (F := (g)^*[A].mapHomotopyCategory (.up ℤ)) (leftDerivedUpperStarTensorComparison A g)
    (fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ (g)^*[A].leftDerivedFunctorCounit.naturality f)
    (delta_raw A g) (kFlatUpperStar A g)   -- or `delta_beta A g`
    (exists_kFlatUpperStar_iso A g) (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)
```

A use-site check (another `run_meta` after the def) confirms that:

* all 28 arguments except argument 22 are syntactically equal to those of the original def;
* **B1:** the kernel-style type of `delta_raw A g …` (constant type instantiated with its
  arguments, no beta) is **syntactically identical** to the `hδ` binder type (0 differences);
* **B2:** the type of `delta_beta A g …` differs from the binder only by the 3 beta-redexes.

### Step 3: benchmarks

**Truncated file** (stops after the def, `…_app_app_comp` proof := `sorry`; one run each):

| measurement | B1 (`delta_raw`) | B2 (`delta_beta`) |
|---|---|---|
| auxiliary theorem kernel time | 7.4 s | 8.8 s |
| `leftDerivedUpperStarOplaxMonoidal` kernel time | 3.2 s | 2.9 s |
| wall / peak memory | 71 s / 2.2 GB | 76 s / 2.2 GB |

**Full file** (all proofs as in the original, nothing `sorry`ed; one run each, sequential):

The first B1/B2 full runs were invalid. The real def reused the auxiliary lemmas
(`_proof_n`, cached by type) of the kernel-unchecked `oplaxProbe`, so the ~20 s `hμ` proof was
never kernel-checked. The variants were rerun with an extra, kernel-checked `oplaxProbe0` (same
body with `hδ := sorry`) placed first. Its `_proof_n` are then the shared auxiliary lemmas, and
they are counted below. The `oplaxProbe0` body itself (3.5–3.6 s) is measurement overhead and is
excluded from the sums.

| measurement | B0 original | B1 `delta_raw` | B2 `delta_beta` |
|---|---|---|---|
| `…_app_app_comp` (Target A, unchanged) | 328.4 s | 346.2 s | 301.3 s |
| auxiliary `_proof_2/15/16/17` (`hμ` etc.) | 0.7 + 0.6 + 2.5 + 20.3 = 24.1 s | 0.6 + 0.5 + 3.2 + 19.1 = 23.4 s | 0.7 + 0.6 + 2.5 + 18.7 = 22.5 s |
| `delta_…` theorem | — | **9.0 s** | **9.5 s** |
| `leftDerivedUpperStarOplaxMonoidal` | **382.6 s** | **3.6 s** | **3.4 s** |
| **oplax total** (aux + delta + def) | **406.7 s** | **36.0 s** | **35.4 s** |
| `isIso_…_δ` / `isIso_…_η` (incl. `_proof_1`) | 1.0 / 8.9 + 2.0 s | 0.7 / 6.3 + 2.8 s | 0.6 / 6.7 + 2.4 s |
| kernel checking succeeds, no `sorry` | yes | yes | yes |
| wall clock (whole file) | 830 s | 492 s | 451 s |
| peak memory | 9.4 GB | 7.4 GB | 8.8 GB |

No new expensive conversion shows up in any generated auxiliary proof: every other kernel entry
is under 7 s. The downstream `δ`/`η` lemmas and `leftDerivedUpperStarMonoidal` are unchanged.
Wall time and peak memory are now dominated by Target A (`…_app_app_comp`, 300–350 s, about
9 GB), which this experiment did not touch.

Single runs only. `…_app_app_comp` alone varies from 301 s to 346 s between runs, so treat
differences under about 15% as noise.

### Interpretation

* **Case "auxiliary theorem ~10 s, oplax definition ~3 s" (the hoped-for case):** the oplax
  part drops from about 407 s to about 36 s (−91%), and about 23 s of that is the pre-existing
  `hμ` side proof. **The cost was eliminated, not transferred.** The theorem pays about 9 s, not
  the ~380 s that the same check costs inside the def.
* **Raw against beta-normal makes no difference.** B2's use site still differs from the binder by
  the 3 beta-redexes, yet the def costs 3.4 s, the same as B1's exactly matching 3.6 s. So
  beta-redex placement is *not* what made the original slow. That rules out the beta-redex
  hypothesis of the previous report.
* **Same conversion, two contexts, 40× apart.** Kernel-checking `delta_raw` performs the same
  conversion `type(…_app_app_comp A g) ≡ P_raw` as the original def's argument check: the same
  two `Expr`s, the same universe parameters and free variables. Yet it costs 9 s as a standalone
  theorem and about 380 s as argument 22 of `ofLaxSquare` inside the def. So the expense depends
  on the **kernel state** in which the check runs (after inferring and checking the 21 preceding
  arguments of `ofLaxSquare`), not only on the two terms. A plausible mechanism, **not verified**:
  the kernel caches (in particular the lazy-delta "failed before" cache, and whnf/infer caches
  filled while checking the earlier arguments) send the later conversion down the unfold-first
  path instead of the compare-arguments-first path.
* This is consistent with X1 from the previous report: `by exact …` built `_proof_18` with the
  elaborator's expected type (18 s), but that type is *not* the kernel's binder type. B2 shows
  that beta-redexes alone are cheap, so the remaining difference must be elsewhere (most likely
  instance or universe arguments as the elaborator instantiated them). The def body then still
  had to convert a non-identical type, in the expensive context. Not re-measured here.

## Deliverables summary

1. **HEq probes:** P1 3.5 s, P2 0.03 s, P4 2.1 s, P5 (type-only) 0.05 s, P3 303 s. The cross
   conversion `a ≡ b` is genuinely expensive. The earlier 280 s figure was not an artefact of
   checking the expressions themselves.
2. **Exact `hδ` binder type:** shown above. It differs from the lemma statement in 726 hidden
   argument positions (universe-level normal forms, instance paths, auxiliary proof constants,
   object representations) and from its beta-normal form only by 3 beta-redexes.
3. **Auxiliary theorems:** `delta_raw` (exact binder type) and `delta_beta` (beta-normal) are
   both cheap to check. The oplax def then costs 3–4 s.
4. **Combined runtime/memory:** see the full-file table.
5. **Abstraction boundary:** found. See the interpretation and next steps.
6. **Unresolved:** see below.

## Effective abstraction boundary and next steps

**An effective boundary was found for Target B:** pass `ofLaxSquare` a *separate theorem* whose
statement is the `hδ` binder type as `ofLaxSquare` instantiates it, either raw or beta-normal.
What matters is that the theorem's type is the binder type built in `ofLaxSquare`'s context
(same instance paths, universe normal forms and auxiliary proof constants), not the lemma's
statement. The conversion then happens in a fresh kernel context, where it is cheap.

The current construction is a **diagnostic `run_meta`**, not a source-level solution: it reads the
binder type off an unchecked copy of the def. Suggested next steps:

1. **Make it source-level.** The aim is a theorem whose statement elaborates to the same `Expr`
   as the binder, or at least to the same hidden arguments, since B2 shows beta-redexes don't
   matter. The cleanest way is to give the `hδ` hypothesis of `ofLaxSquare` a name in
   `CategoryTheory/Monoidal/OplaxOfLaxSquare.lean`, e.g.
   `def LaxSquareCompat (δG) (e) : Prop := ∀ a b, …`, so that
   `theorem … : LaxSquareCompat (Q₁ := Qh) (Q₂ := Qh) (F := …) (leftDerivedUpperStarTensorComparison A g) (fun a ↦ …) := leftDerivedUpperStarTensorComparison_app_app_comp A g`
   elaborates the instances the way the `ofLaxSquare` application does. Then check with the
   structural diff that the theorem's type matches the use-site binder, and re-benchmark.
   (This edits a pre-existing shared file, so it needs a decision.)
2. **Confirm the context-dependence** (optional): kernel-check, as a standalone theorem, the
   original def's body truncated just after argument 22. Compare it with `delta_raw`'s 9 s and
   with the kernel's diagnostics for unfold counts.
3. **Target A** (`…_app_app_comp`, 300–350 s, now the dominant cost) is untouched, as instructed.
   The result above suggests trying the same trick first: put the final `exact h` conversion into
   a separate theorem stated in the exact form of `type(h)`, before the `NatTrans`-level refactor.

## Smallest unresolved difference

For B1 there is none: the use-site types are syntactically identical. For B2 the only difference
is the 3 beta-redexes `(fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a) x` (x = `a`, `b`,
`a ⊗ b`), and they cost nothing measurable. What is still unexplained is why the identical
conversion costs about 9 s in a standalone theorem but about 380 s inside the original def.

## Reproduction

All files were in the session scratchpad (`r3/`) and were not committed: `gen_probe.sh` (P1–P5),
`gen_b.js` (B0/B1/B2 × truncated/full), `mkdelta.lean` (binder extraction, structural diff,
`addDecl` of `delta_raw`/`delta_beta`), and `checkuse.lean` (use-site check). The core of the
binder extraction:

```lean
lambdaTelescope (← getConstInfoDefn `oplaxProbe).value fun xs body => do
  let args := body.getAppArgs           -- ofLaxSquare applied to 28 arguments; hδ is #22
  let mut t ← inferType body.getAppFn
  for j in [:22] do t := t.bindingBody!.instantiate1 args[j]!   -- kernel-style, no beta
  let pRaw := t.bindingDomain!
  addDecl (.thmDecl { name := `delta_raw, levelParams := ci.levelParams,
    type := ← mkForallFVars xs pRaw, value := ← mkLambdaFVars xs args[22]! })
```
