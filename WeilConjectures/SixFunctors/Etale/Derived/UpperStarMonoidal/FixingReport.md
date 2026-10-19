# Kernel performance of `UpperStarMonoidal/Comparison.lean`: fixing report

This report follows `FixingInstruction.md` and builds on `DiagnoseReport.md` and
`DiagnoseReport1.md`. It records every attempt, including the ones that failed.

**Outcome:** a fix was found and applied to `Comparison.lean`. It is variant **V1W** below and
needs no new module, no `@[no_expose]`, no `sorry` and no new axioms. Under the same machine
load, the file goes from **25 min wall / 697 s CPU / 7.0 GB** to **3 min wall / 140 s CPU /
2.4 GB**. Target A drops from 707 s to 42 s of kernel time, and Target B from 637 s to 3.3 s
(plus 8.8 s for one new lemma).

## Setup and caveat on timings

* Lean `v4.33.1`, branch `slopmaster2-diagnose-1`. Every run uses `lake env lean` with the
  lakefile `leanOptions` as `-D` flags, plus `-DElab.async=false -Ddebug.skipKernelTC=false
  -Dtrace.profiler=true -Dtrace.profiler.threshold=500`. Kernel times are the
  `[Kernel] typechecking declarations` trace entries. Wall time, CPU (user) time and peak
  memory come from GNU `time -v`. All runs were sequential.
* **The machine was shared and heavily loaded during this round** (load average 62–66 on 24
  cores, from another user's Lean builds). Kernel trace times are wall-clock based, so they
  are about 2× the unloaded figures of the earlier reports: V0's Target A is 707 s here against
  217–346 s before. **Compare variants within this report only.** All V-runs ran under the same
  load (63.6–66.5). CPU time is the most load-independent column.
* Module variants: the wrapper was written to
  `UpperStarMonoidal/ComparisonWrapper.lean`, compiled once with the trace (reported
  separately) and once with `lake build`. The consumer is a scratch copy of `Comparison.lean`
  with the def removed and `public import …ComparisonWrapper` added. The temporary wrapper file
  was deleted afterwards.

## The wrapper and the changes tried

### Wrapper location (Experiment 1)

The "common natural transformation" behind both sides of the expensive Target A conversion is
`Functor.leftDerived₂NatTrans … (derivedTensorLeftDerivedUpperStarCounit A g) …`. A named
regular `def` wrapping exactly this already exists: `leftDerivedUpperStarTensorComparison A g`.
So no new wrapper `def` was introduced in V1; the existing def is the wrapper. What was missing
was a way to make Target A's `h` *mention* the wrapper. `h` comes from the generic
`Functor.leftDerived₂NatTrans_app_app` and so mentions the unfolded `leftDerived₂NatTrans …`,
with hidden arguments elaborated differently from the def body.

**Target A change (V1).** One generic lemma replaces the natural transformation *at the level
of natural transformations*, before any `NatTrans.app`:

```lean
/-- Replace the natural transformation `τ` in `(τ.app X).app Y ≫ f = k` by `σ = τ`, at the level
of natural transformations. -/
lemma app_app_comp_of_eq {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D ⥤ E} {τ : F ⟶ G} {X : C} {Y : D} {Z : E} {f : (G.obj X).obj Y ⟶ Z}
    {k : (F.obj X).obj Y ⟶ Z} (h : (τ.app X).app Y ≫ f = k) (σ : F ⟶ G) (hσ : σ = τ) :
    (σ.app X).app Y ≫ f = k :=
  hσ ▸ h
```

The last line of `leftDerivedUpperStarTensorComparison_app_app_comp` becomes

```lean
  exact app_app_comp_of_eq h (leftDerivedUpperStarTensorComparison A g) rfl
```

`h` is elaborated first, so `τ` is syntactically `h`'s `leftDerived₂NatTrans …`. The `rfl` is a
conversion `leftDerivedUpperStarTensorComparison A g ≡ leftDerived₂NatTrans …` between two
natural transformations, which the earlier probe measured at about 3.5 s. It is no longer a
conversion under `NatTrans.app`, which cost about 300 s.

### Module wrapper (Experiment 2)

`ComparisonWrapper.lean` is a `module` with the same imports and section variables as
`Comparison.lean`, containing only the def (V2: exposed; V3/V4: `@[no_expose]` inside the
`@[expose] public section`). V4 adds the characterizing lemma:

```lean
/-- The defining equation of `leftDerivedUpperStarTensorComparison`. -/
theorem leftDerivedUpperStarTensorComparison_eq :
    leftDerivedUpperStarTensorComparison A g =
      Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
        (leftDerivedUpperStarDerivedTensorCounit A g)
        (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh) :=
  by unfold leftDerivedUpperStarTensorComparison; rfl
```

The consumer then uses `(leftDerivedUpperStarTensorComparison_eq A g).symm` for
`leftDerivedUpperStarTensorNatIso_hom`, and
`app_app_comp_of_eq h _ ((leftDerivedUpperStarTensorComparison_eq A g).trans rfl)` in Target A.

### Target B change (W: my addition, from `DiagnoseReport1.md`)

`ofLaxSquare`'s `hδ` hypothesis gets a name as a **regular** `def`, plus a thin wrapper around
`ofLaxSquare` that takes it in that form:

```lean
def LaxSquareHδ {K₁ K₂ D₁ D₂ : Type*} … {G : D₁ ⥤ D₂} (δG : …) {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂}
    [Q₁.LaxMonoidal] [Q₂.LaxMonoidal] {F : K₁ ⥤ K₂} [F.OplaxMonoidal]
    (e : ∀ a, G.obj (Q₁.obj a) ⟶ Q₂.obj (F.obj a)) : Prop :=
  ∀ a b, (δG.app (Q₁.obj a)).app (Q₁.obj b) ≫ (e a ⊗ₘ e b) ≫
    μ Q₂ (F.obj a) (F.obj b) = G.map (μ Q₁ a b) ≫ e (a ⊗ b) ≫ Q₂.map (δ F a b)

noncomputable def ofLaxSquareHδ … (hδ : LaxSquareHδ δG e) … : G.OplaxMonoidal :=
  Functor.OplaxMonoidal.ofLaxSquare δG e he hδ S hS hμ

lemma leftDerivedUpperStarTensorComparison_laxSquareHδ :
    LaxSquareHδ (Q₁ := Qh) (Q₂ := Qh) (F := (g)^*[A].mapHomotopyCategory (.up ℤ))
      (leftDerivedUpperStarTensorComparison A g)
      (fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a) :=
  leftDerivedUpperStarTensorComparison_app_app_comp A g
```

`leftDerivedUpperStarOplaxMonoidal` calls `ofLaxSquareHδ … (leftDerivedUpperStarTensorComparison_laxSquareHδ A g) …`.
The expensive conversion (lemma statement against the binder) now runs once, inside the small
lemma (8–9 s). At the def, the kernel compares `LaxSquareHδ args₁` with `LaxSquareHδ args₂`:
the same head with *regular* reducibility hints, so it compares arguments first (cheap
universe-level, type and proof-irrelevant instance differences) and never unfolds the square.

**Failed first attempt (W0): `abbrev LaxSquareHδ`.** The lemma checks in 8.8 s, but the def
still costs 580 s. Comparing an `abbrev` application against the binder unfolds it, and after
unfolding the statement differs from the binder in **942 hidden places**, all printing the same.
For example, `DerivedCategory.{u+1, u+1, max (max u' (u+1)) u}` against `{…, max (u+1) u'}`
(482×), and `derivedTensorLeftDerivedUpperStar._proof_n` against
`leftDerivedUpperStarTensorComparison._proof_m`. The lemma statement picks up `D₁`/`D₂` and
instance proofs from a different elaboration path than the def. A regular `def` avoids having
to match these syntactically.

## Benchmark matrix (full file, sequential, same machine load)

Kernel times in seconds. "B" is the oplax def itself, and "B aux" is its `_proof_16` + `_proof_17`
(the pre-existing `hμ` side proofs). ✗ means compile errors (see the next section).

| variant | wrapper / exposure | Target A | B | B aux | new decls | ok | wall | CPU | peak mem |
|---|---|---|---|---|---|---|---|---|---|
| V0 | original | **706.5** | **637.3** | 3.5 + 29.2 | — | ✓ | 25:09 | 697 s | 7.0 GB |
| V1 | existing def as wrapper, A via `app_app_comp_of_eq … rfl` | **45.5** | 722.8 | 2.9 + 25.6 | — | ✓ | 15:22 | 411 s | 7.0 GB |
| V2 | separate module, exposed | 65.0 | 502.4 | 2.6 + 19.5 | `…TensorIso_hom` **599.9** | ✗ | 22:12 | 682 s | 7.1 GB |
| V3 | separate module, `@[no_expose]` | (13.3, proof failed) | 611.4 | 2.5 + 21.4 | — | ✗ | 12:23 | 383 s | 7.1 GB |
| V4 | V3 + `…_eq` lemma | 28.7 | 598.8 | 2.7 + 17.8 | `NatIso_hom` 2.4 | ✗ | 12:34 | 402 s | 7.0 GB |
| **V1W** | V1 + `LaxSquareHδ` (no module) | **41.7** | **3.3** | 2.5 + 20.8 | `…_laxSquareHδ` 8.8 | ✓ | **2:59** | **140 s** | **2.4 GB** |
| V4W | V4 + `LaxSquareHδ` | 39.8 | 2.8 | 2.4 + 21.4 | 8.6; `NatIso_hom` 2.9 | ✗ | 2:50 | 135 s | 2.6 GB |
| V4W′ | V4W + interface proofs | 46.4 | 2.8 | 2.1 + 20.0 | 7.8; `NatIso_hom` 3.2 | ✓ | 3:08 | 137 s | 2.1 GB |

Wrapper module compilation, reported separately (V2–V4W′): 31–43 s wall, 10–19 s CPU,
1.9–2.0 GB. Kernel: `leftDerivedUpperStarTensorComparison` 1.4–2.0 s, and
`leftDerivedUpperStarTensorComparison_eq` 6.4–6.5 s. The δ/η lemmas downstream stay at
≤ 10 s in every variant.

## Definitional equalities that stop working across the module boundary

* **V2 (exposed, different module).** `leftDerivedUpperStarTensorNatIso_hom := rfl` fails in
  *elaboration* (`whnf` heartbeat timeout). The `rfl` lemma `leftDerivedUpperStarTensorIso_hom`
  then costs **600 s** in the kernel. Once the def lives in another module, the consumer's
  `leftDerived₂NatIso …` no longer shares the auxiliary proof constants (`_proof_n`) of the def
  body. The same-module aux-lemma cache had been making these terms syntactically equal.
  Separating modules *without* hiding the def is strictly worse.
* **V3 (`@[no_expose]`).** As expected, every `rfl` that needs the body fails, with
  `Not a definitional equality` / `Type mismatch`:
  `leftDerivedUpperStarTensorNatIso_hom`, `isIso_leftDerivedUpperStarTensorComparison`
  (`(…NatIso A g).isIso_hom`), `leftDerivedUpperStarTensorIso_hom`, and the V1 `rfl` in Target A.
* **V4.** The characterizing lemma can't be proved by the term `rfl` in the defining module:
  "This theorem is exported from the current module. This requires that all definitions that
  need to be unfolded to prove this theorem must be exposed." `by unfold …; rfl` works (6.5 s).
  With it, `NatIso_hom` and Target A go through. `isIso_…Comparison` and `…TensorIso_hom` still
  fail until **V4W′** adds explicit interface proofs:
  `leftDerivedUpperStarTensorNatIso_hom A g ▸ (leftDerivedUpperStarTensorNatIso A g).isIso_hom` and
  `NatTrans.congr_app (NatTrans.congr_app (leftDerivedUpperStarTensorNatIso_hom A g) K) M`.
  These are cheap (< 2 s each). Downstream files were **not** tested against a hidden
  comparison. `LowerStarProjectionBaseChange.lean` and others use it heavily and may contain
  further `rfl`s that rely on its body.

## Does `@[no_expose]` prevent the expensive unfolding?

* **Target A:** it *forces* the fix but doesn't provide it. With the def hidden, the
  expensive conversion simply fails (V3). It succeeds cheaply only once the proof is routed
  through a natural-transformation-level equation (V4: 28.7 s). That is the same mechanism as
  V1 (45.5 s), which needs no hiding. Within this load's noise (±15–30%), V1 and V4 are the same.
* **Target B: no.** With the comparison hidden, the oplax def still costs 599–611 s (V3, V4),
  the same as V0. So Target B's cost was never about unfolding the comparison. It is the
  conversion of the lemma statement into `ofLaxSquare`'s binder, whose hundreds of hidden
  differences (universe-level normal forms, instance paths, aux proof constants) sit under
  projections such as `CategoryStruct.comp`. Only the `LaxSquareHδ` boundary fixes it (V1W,
  V4W, V4W′: 2.8–3.3 s).

## Smallest successful abstraction boundary

1. **Target A:** a natural-transformation-level equation applied *before* `NatTrans.app`. That is
   `app_app_comp_of_eq h (leftDerivedUpperStarTensorComparison A g) rfl`, with the existing
   regular def as the wrapper. No module boundary is needed.
2. **Target B:** a named *regular* (not `abbrev`) `def` for `ofLaxSquare`'s `hδ` hypothesis,
   plus a wrapper `ofLaxSquareHδ` that takes it. The expensive conversion then runs once inside a
   small standalone lemma, and the def compares two `LaxSquareHδ` applications argument by
   argument.

V1W, with both, is what has been applied to `Comparison.lean`: 49 lines added, 3 changed. The
module/`@[no_expose]` route (V4W′) reaches the same performance but needs a new module, a hidden
def, the `unfold`-proved characterizing lemma and two interface proofs, and it risks downstream
`rfl` breakage. It brings no measurable gain over V1W.

## Remaining costs and follow-ups

* Target A still costs about 42 s (35 s in a lighter truncated run). The residual is most
  likely the final `exact` conversion of the other, cheaper parts of the square: implicit
  objects such as `((derivedTensorLeftDerivedUpperStar A g).obj _).obj _` against `_ ⊗ _`, and
  the `μ`/counit morphisms. Not bisected this round.
* `leftDerivedUpperStarOplaxMonoidal._proof_17` (the `hμ` argument) costs about 20 s and is
  untouched.
* `LaxSquareHδ` and `ofLaxSquareHδ` are generic. They currently live in `Comparison.lean`, in
  namespace `AlgebraicGeometry.Etale`, because that is the benchmarked placement. They belong in
  `CategoryTheory/Monoidal/OplaxOfLaxSquare.lean`, and ideally `ofLaxSquare` itself would take
  `hδ : LaxSquareHδ δG e`. That would also help the ProEtale analogue if it uses `ofLaxSquare`.
  Moving them means editing a shared file, so it is left as a decision.
* `app_app_comp_of_eq` is likewise generic and could move to a `CategoryTheory` file.

## Verification of the applied fix

`lake build` of `Comparison` together with all 11 modules that import it directly
(`UpperStarMonoidal`, `…/Shift`, `…/Comp`, `…/CompUnit`, `Exchange`, `WeilComplexTensorHom`,
`LowerStarProjectionUnit`, `CompactConstructible`, `Kunneth/Comparisons`, `Perfect/Pullback`,
`Perfect/SitePerfect`), plus their dependencies: **Build completed successfully (13774 jobs)**,
with no errors and no warnings on `Comparison`. Downstream proofs that use
`leftDerivedUpperStarOplaxMonoidal` (now built with `ofLaxSquareHδ`) or the comparison lemmas are
unaffected. In this build, `Comparison` itself took 469 s under `lake build` (default
`Elab.async`, sharing the loaded machine with the parallel build). The whole build took 2 h 3 min
wall and 9.2 GB peak, mostly rebuilding dependencies on the loaded machine.

## Reproduction

The scratch files (session scratchpad `r4/`, not committed) were: `gen.js` (V0/V1/V1W from
`Comparison.lean`), `genmod.js` (wrapper module and consumer for V2–V4W′), `ofeq.lean`,
`laxsq.lean`, `run.sh`, and `batch.sh`/`batch2.sh` (sequential runs).
