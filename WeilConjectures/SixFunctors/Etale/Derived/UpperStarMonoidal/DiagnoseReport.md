# Kernel performance of `UpperStarMonoidal/Comparison.lean`: diagnosis report

This report follows `DebugInstruction.md`. It covers both rounds: the first round (async × kernel
benchmark, profiler, diagnostics) and the second round (top-down isolation, subterm bisection,
abstraction-boundary tests).

## Setup

* Lean `v4.33.1` (`819816b2e0a3`), Mathlib `v4.33.1`, branch `slopmaster2` at `fb73788b92`.
* Benchmark file: an unchanged copy of `Comparison.lean` (no `skipKernelTC` overrides), compiled
  with `lake env lean` plus the `leanOptions` of `lakefile.toml` passed as `-D` flags.
* Round 2 runs all use `-DElab.async=false -Ddebug.skipKernelTC=false -Dtrace.profiler=true
  -Dtrace.profiler.threshold=500`. Per-declaration kernel times come from the
  `[Kernel] typechecking declarations [...]` trace entries.
* Machine: 24 cores, 94 GB RAM. Round 2 variants ran **5 at a time**, so absolute times are about
  10–40% higher and noisier than single runs. Only large changes (several ×) count as signal.
* Variants were made by text-substituting the benchmark file. "Truncated A" files stop after
  `leftDerivedUpperStarTensorComparison_app_app_comp`. "Truncated B" files stop after
  `leftDerivedUpperStarOplaxMonoidal` and replace the proof of `…_app_app_comp` by `sorry`. That is
  safe because it is a theorem, and run I1 confirms it doesn't change the oplax cost.

## Round 1 summary

| `Elab.async` | `skipKernelTC` | wall (s), 3 runs | mean | peak memory |
|---|---|---|---|---|
| true | false | 523 / 654 / 551 | 576 | 8.6–8.9 GB |
| true | true | 30 / 40 / 40 | 36.5 | 2.0 GB |
| false | false | 476 / 553 / 421 | 483 | 8.8–9.4 GB |
| false | true | 33 / 49 / 33 | 38.5 | 1.9 GB |

* The kernel is the bottleneck; `Elab.async` doesn't explain it.
* The profiler shows `type checking 398 s` against `elaboration 2.9 s` and `tactic execution 5 s`.
* Kernel diagnostics show about 1.5M unfoldings each of `AddGroup.toSubNegMonoid` and
  `Preadditive.homGroup`, plus the `Equiv.addCommGroup` / `Function.Injective.addCommGroup`
  hom-group hierarchy of `Sheaf` (an `InducedCategory`), in exactly two declarations.
* `isIso_leftDerivedUpperStarOplaxMonoidal_δ` is cheap: about 1.5 s in total, with no kernel
  entry above 1 s. In the editor it most likely only *waits* for the oplax definition (not
  verified).

## Experiment 1: declaration-level isolation

Kernel times in seconds.

| run | `…_app_app_comp` | `OplaxMonoidal` (def) | `…_proof_17` | `η._proof_1` + `η` | wall | peak memory |
|---|---|---|---|---|---|---|
| I0 original (full file) | **216.7** | **250.4** | 13.8 | 4.7 + 1.5 | 539 s | 9.4 GB |
| I1 `…_app_app_comp` body := `sorry` | **4.7** | 234.1 | 10.8 | 4.1 + 1.3 | 293 s | 9.0 GB |
| I2 oplax body := `sorry` | 218.1 | **< 0.5** | — | δ, η: kernel error (†) | 269 s | 8.9 GB |
| I3 both := `sorry` | 4.5 | < 0.5 | — | δ, η: kernel error (†) | 40 s | 2.1 GB |

(†) With the oplax body replaced by `sorry`, `isIso_…_δ` and `isIso_…_η` still elaborate but fail
in the kernel (`declaration type mismatch` on their `_proof_1`). Their `inferInstanceAs` proofs
rely on the oplax def unfolding to `leftDerivedUpperStarTensorComparison`. That is the expected
downstream effect.

Conclusions:

* The two costs are **independent and localized**. Removing either body removes only that
  declaration's cost (about 212 s and about 250 s). Neither propagates downstream; the `δ`/`η`
  lemmas cost under 7 s of kernel time in every run.
* About 4.5 s of `…_app_app_comp` is the statement itself. The remaining ~212 s is the proof.
* Peak memory drops from about 9 GB to about 2 GB only when both bodies are removed.

## Experiment 2: top-down subterm bisection

### Target A: `leftDerivedUpperStarTensorComparison_app_app_comp` (truncated A file)

| replacement (typed `sorry`) | kernel time of `…_app_app_comp` |
|---|---|
| A0 none | 222 s |
| A1 proof of `e₁` | 242 s |
| A2 proof of `e₂` (`rfl`) | 247 s |
| A3 proof of `e₃` (`rfl`) | 255 s |
| A7 `e₁`, `e₂`, `e₃` together | 230 s |
| A5 `h` (`have h := (sorry : type_of% (Functor.leftDerived₂NatTrans_app_app …))`) | 238 s |
| A4 the final `rw [e₁, e₂, e₃] at h; simp only [Category.assoc] at h; exact h` | **22 s** |
| A6 only `exact h` | **18 s** |

So about 204 s is the **type conversion at `exact h`**, not the construction of any subterm.
After the `rw`/`simp`, the type of `h` and the goal print identically, but they differ in hidden
arguments.

Bisection of that conversion was done with a probe. For each pair of corresponding subterms
`(a, b)` of `type(h)` and the goal, it kernel-checks an auxiliary theorem `HEq a b := HEq.refl a`
(`Lean.Meta.mkAuxTheorem`) and descends into the expensive pairs:

| path | `h` side vs goal side | kernel time |
|---|---|---|
| `lhs` | `… ≫ (counit.app K ⊗ₘ counit.app M) ≫ μ Qh _ _` (both sides) | 240 s |
| `lhs.2`, `lhs.3`, `lhs.4` | implicit objects of `≫` | 0.04–0.06 s each |
| `lhs.6` | `(counit.app K ⊗ₘ counit.app M) ≫ μ Qh _ _` | 2.0 s |
| `lhs.5` | `((leftDerived₂NatTrans …).app (Qh.obj K)).app (Qh.obj M)` vs `((leftDerivedUpperStarTensorComparison A g).app (Qh.obj K)).app (Qh.obj M)` | 253 s |
| `lhs.5.4`, `lhs.5.5` | implicit objects | 0.04 s each |
| **`lhs.5.6`** | **`(leftDerived₂NatTrans …).app (Qh.obj K)` vs `(leftDerivedUpperStarTensorComparison A g).app (Qh.obj K)`** | **280 s** |
| `lhs.5.6.0`–`lhs.5.6.3` | categories and instances | < 0.01 s each |
| `lhs.5.6.6` | `leftDerived₂NatTrans … ` vs `leftDerivedUpperStarTensorComparison A g` (different heads) | **3.5 s** |
| `lhs.5.6.7` | `Qh.obj K` vs `Qh.obj K` | 0.03 s |
| `rhs` | right-hand side, whole | 9.9 s |

**Smallest expensive conversion (Target A):**

```lean
-- h side (from `Functor.leftDerived₂NatTrans_app_app`)
NatTrans.app
  ((derivedTensorLeftDerivedUpperStar A g).leftDerived₂NatTrans
    (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
    (leftDerivedUpperStarDerivedTensor A g) (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh))
  (Qh.obj K)
-- goal side (from the statement)
NatTrans.app (leftDerivedUpperStarTensorComparison A g) (Qh.obj K)
```

Every argument of this `NatTrans.app` is cheap on its own: the two natural transformations take
3.5 s and everything else under 0.05 s. Under `NatTrans.app`, the same comparison takes 280 s. So
the cost isn't in any subterm. It comes from how the kernel handles the comparison *under the
projection* `NatTrans.app`. A plausible mechanism, which I did not verify in the kernel source: the
kernel's lazy-delta step only tries "compare the arguments" for definitions with *regular*
reducibility hints. Structure projections such as `NatTrans.app` have `abbrev` hints, so the kernel
unfolds the projection and reduces the natural transformations. That means evaluating
`leftDerived₂NatTrans …` (a localization lift) down to a constructor, which is where the
millions of `Preadditive.homGroup` / `AddGroup` unfoldings come from.

### Target B: `leftDerivedUpperStarOplaxMonoidal` (truncated B file)

| replacement (typed `sorry`) in `ofLaxSquare …` | kernel time of the oplax def |
|---|---|
| B0 none | 251 s (+ `_proof_17` 12.8 s, `_proof_16` 1.5 s) |
| B2 `he` | 317 s |
| B3 `hS` | 330 s |
| B4 `hμ` | 335 s (and `_proof_17` disappears, so `_proof_17` is `hμ`) |
| B1 **`hδ`** (`leftDerivedUpperStarTensorComparison_app_app_comp A g`) | **2.4 s** |
| B5 `δG` and `hδ` | 4.4 s |

B2–B4 are slower than B0 only because of load; they are not reductions.

* **Elaborated terms:** comparing the elaborated `ofLaxSquare` applications of B0 and B1
  argument by argument (all 28 arguments, using `Expr` equality) shows that **only argument 22
  (`hδ`) differs**. All implicit and instance arguments (`G`, the `MonoidalCategory`/`LaxMonoidal`
  instances, `e`, …) are syntactically identical. So the whole ~250 s is the kernel checking that
  `type(leftDerivedUpperStarTensorComparison_app_app_comp A g)` matches `ofLaxSquare`'s `hδ`
  binder type, instantiated with the actual arguments: δG := the comparison,
  `e := fun a ↦ counit.app a`, and so on.
* **Isolation:** checked on its own as `HEq` against the elaborator's expected type (which
  `instantiateMVars` has beta-reduced), this conversion costs only **18.6 s** (`lhs` 3.9 s,
  `rhs` 6.2 s, every sub-piece ≤ 3.4 s). Inside the def it costs about 230 s. The cost depends on
  the term's exact syntactic shape. The obvious difference between the two is the beta-redexes
  `(fun a ↦ counit.app a) a` that come from substituting `e` into the binder type, but that is
  not yet confirmed.

Both targets are therefore **type conversions of the same commutative-square statement**, not
expensive subterms. Target A converts the `leftDerived₂NatTrans_app_app` form to the statement
form. Target B converts the statement form to the `ofLaxSquare` binder form.

## Experiment 3: abstraction-boundary tests (so far negative)

| run | change | result |
|---|---|---|
| X1 (truncated B) | `hδ := (by exact leftDerivedUpperStarTensorComparison_app_app_comp A g)` | oplax def **326 s**, new `_proof_18` 18 s: no improvement |
| X2 (full file) | same as X1 | `…_app_app_comp` 317 s, oplax def **386 s**: no improvement |
| X3 (truncated A) | `rw [leftDerivedUpperStarTensorComparison]` before `exact h` | **373 s**: no improvement |
| X4 (truncated A) | `delta leftDerivedUpperStarTensorComparison` before `exact h` (control) | **371 s**: no improvement |

X1–X4 ran under heavy parallel load, so only "no large improvement" can be concluded.

* **X1:** the `by exact` wrapper doesn't move the expensive conversion into an auxiliary lemma.
  The def body still pays for it. The new 18 s `_proof_18` matches the isolated conversion cost,
  so the def body appears to do a second, expensive comparison against the binder type.
* **X3:** rewriting the goal's `leftDerivedUpperStarTensorComparison` into `leftDerived₂NatTrans …`
  doesn't make it syntactically equal to `h`. Some arguments still differ (from the round 2
  structural diff, likely instance arguments such as the `IsLeftDerivedFunctor₂` /
  `IsLocalization` instances, or the `MonoidalCategory (DerivedCategory …)` instance arguments
  `Sheaf.monoidalPreadditive` / `hasDerivedMonoidalCategory …` against `derivedTensor._proof_3`
  / `derivedTensor._proof_9`). So the same projection-unfolding path is still taken.

Separately, three conversions between those instance-level terms are cheap in isolation
(< 0.5 s each):
* `type_of% derivedTensor._proof_3 A Z = MonoidalPreadditive (Sheaf …)`
* `type_of% derivedTensor._proof_9 A Z = Qh.HasDerivedMonoidalCategory …`
* `derivedTensor A Z = curriedTensor _`

## Most likely root cause

In both declarations the kernel has to show that two versions of the same equation
`Lg^*(…) ≫ (ε ⊗ ε) ≫ μ = Lg^*(μ) ≫ ε ≫ Qh(δ)` are definitionally equal. They differ only in
*how* some morphisms and objects are written:
* the unfolded `leftDerived₂NatTrans …` against the constant `leftDerivedUpperStarTensorComparison`;
* implicit objects such as `((derivedTensorLeftDerivedUpperStar A g).obj _).obj _` against
  `_ ⊗ _`;
* beta-redexes from `ofLaxSquare`'s `e`.

When such a difference sits under a structure projection (`NatTrans.app`, and probably
`CategoryStruct.comp` / `tensorHom`), the kernel doesn't compare the arguments. It unfolds the
projection and evaluates the localized natural transformations and the derived-category structure
down to constructors. That is where the huge `Preadditive.homGroup` / `AddGroup` unfolding counts
come from. The `Preadditive` unfoldings are a *consequence* of this high-level conversion, not its
cause.

## Recommended next steps

The highest-level place to avoid the expensive check is **the statement of
`leftDerivedUpperStarTensorComparison_app_app_comp`, together with the binder form `ofLaxSquare`
expects**.

1. **Remove the representation mismatch syntactically, not by defeq.** For Target A: state an
   intermediate lemma in exactly the form `Functor.leftDerived₂NatTrans_app_app` produces (same
   implicit objects and instances), then reach the public statement through `rw`/`simp` steps
   whose equations live at the level of natural transformations or functors, never under
   `NatTrans.app`. For example, an equation lemma `leftDerivedUpperStarTensorComparison A g =
   leftDerived₂NatTrans …` that the kernel checks at the `NatTrans` level, where it costs 3.5 s.
   X3 shows that the bare equation lemma isn't enough. The remaining hidden differences must be
   identified first: run the same bisection probe on the X3 variant.
2. **For Target B,** make the `hδ` argument's type *syntactically* equal to the binder type. For
   example, state an auxiliary lemma whose statement is literally `ofLaxSquare`'s `hδ` instantiated
   with `e := fun a ↦ counit.app a`, beta-redexes included, prove it from `…_app_app_comp` once
   (about 18 s by the isolated measurement), and pass it. Alternatively, change `ofLaxSquare` to
   take `e` as a natural transformation `Q₁ ⋙ G ⟶ F ⋙ Q₂` and `hδ` in a whiskered form, so that no
   beta-redexes are created.
3. **Confirm the projection mechanism directly.** Kernel-check
   `HEq ((leftDerived₂NatTrans …).app X) ((leftDerivedUpperStarTensorComparison A g).app X)` with
   the comparison first unfolded once by hand. If that is cheap, the cost is the abbrev-hinted
   projection path, and making terms agree before any projection is the right fix.
4. Only if 1–2 fail: consider making `leftDerivedUpperStarTensorComparison` (or
   `Functor.leftDerived₂NatTrans`) irreducible to the kernel, as an `irreducible_def` or a structure
   wrapper with characterizing lemmas. That would block the evaluation outright, but it is a larger
   change.

## Reproduction

The variant files and probes lived in the session scratchpad and were not committed. The key
probe is:

```lean
/-- kernel-check `HEq a b` as an auxiliary theorem; return elapsed ms -/
def kernelHEqTime (tag : String) (a b : Expr) : MetaM (Option Nat) := do
  let ty ← mkHEq a b
  let val ← mkHEqRefl a
  let t0 ← IO.monoMsNow
  try
    let _ ← mkAuxTheorem ty val (cache := false)
    return some ((← IO.monoMsNow) - t0)
  catch _ => return none
```

`bisect` calls it on corresponding arguments (same head, same arity) of `type(h)` and the goal,
recursing into pairs above 2 s. It runs through `run_tac` placed just before `exact h`, with
`set_option maxHeartbeats 0`.
