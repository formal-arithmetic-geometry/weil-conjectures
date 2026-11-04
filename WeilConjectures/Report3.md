# Report 3 — Alternative fix: opaque `moduleObjectDerivedPullback` + equality lemma

Question: instead of the component-lemma repair (Report 2), should the wrapper
`moduleObjectDerivedPullback` be removed, or made opaque (`@[no_expose]`)?

**Answer:** do **not** remove it. **Opaque works**, provided the compositors and their coherence
lemmas are restated in the wrapper vocabulary inside the defining module (proved while the body is
still visible) and consumers use only that vocabulary. With that, the *original proofs*
(`exact h2`, `congr 1`) go through in seconds under ordinary kernel checking. The price is that
the theorem statements change vocabulary: `leftDerivedUpperStarComp/Id` become
`moduleObjectDerivedPullbackComp/Id`. Other downstream files were ignored, as requested.

Same environment as Reports 1–2 (Lean/Mathlib 4.33.1, `slopmaster2` @ `55376e1a60`, shared
machine, load average 35–100). Scratch files are under the session scratchpad: `wrap/`
(consumers, logs, `run2.sh`) and `nx/ScratchNX/` (scratch modules compiled with
`lean -R nx -o …`, added to `LEAN_PATH`).

## 1. Wrapper variants with the original statements and original proofs

| variant | change | result | wall / user / RSS |
|---|---|---|---|
| original | local `def` | elab timeout (`exact`) + kernel timeout (`congr 1`) | ~152 s / – / 3.7 GB |
| `v_imp_plain` | local def removed; same `def` imported from another module (boundary control) | same two failures (elab 3.5 s, kernel 120 s) | 173 / 155 / 3.75 GB |
| `v_abbrev` | `abbrev` | same two failures (kernel 122 s) | 187 / 171 / 3.75 GB |
| `v_red` | `@[reducible] def` | same two failures (kernel 144 s) | 205 / 172 / 3.75 GB |
| `v_nowrap` | **wrapper removed**: macro expanding every use to `(upperStar Λ f).leftDerivedFunctor` | **all three statements** fail to elaborate (`whnf` timeout at the `congrArg (fun f ↦ …)` lambdas; `.leftDerivedFunctor` over not-yet-known schemes stalls instance search) | 171 / 157 / 2.04 GB |
| `v_imp_noexpose` | imported `@[no_expose] def`, consumer unchanged | **type errors** in `dncPullbackComp_congr_left/right` and all three theorem statements: they *mix* the wrapper with the `L(f)`-typed `leftDerivedUpperStarComp/Id`, which only typechecks if the wrapper unfolds | 11.5 / 8.0 / 1.97 GB |

So changes to the reducibility of the wrapper alone do nothing (`abbrev`, `@[reducible]`, moving
it to another module). Removing it is worse. Opacity turns the *slow* mixed-spelling conversions
into *errors*, which shows exactly which statements mix vocabularies.

## 2. Opaque wrapper with an equality lemma and wrapper-vocabulary API

Defining module (`nx/ScratchNX/NoExposeAPI.lean`; standalone: 23.5 s wall / 19.6 s user / 2.09 GB):

```lean
@[no_expose]
def moduleObjectDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) : … := (upperStar Λ f).leftDerivedFunctor

/-- The direct equality lemma. -/
theorem moduleObjectDerivedPullback_eq (f : X ⟶ Y) :
    moduleObjectDerivedPullback Λ f = (upperStar Λ f).leftDerivedFunctor := by
  delta moduleObjectDerivedPullback; rfl

@[no_expose] def moduleObjectDerivedPullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleObjectDerivedPullback Λ (f ≫ g) ≅
      moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f :=
  leftDerivedUpperStarComp Λ f g
@[no_expose] def moduleObjectDerivedPullbackId (X) : moduleObjectDerivedPullback Λ (𝟙 X) ≅ 𝟭 _ :=
  leftDerivedUpperStarId Λ X

-- coherence, stated in the wrapper vocabulary, proved by the upstream lemmas:
theorem moduleObjectDerivedPullbackComp_assoc_app … := leftDerivedUpperStarComp_assoc_app Λ f g h K
theorem moduleObjectDerivedPullbackComp_id_left_app … := leftDerivedUpperStarComp_id_left_app Λ g K
theorem moduleObjectDerivedPullbackComp_id_right_app … := leftDerivedUpperStarComp_id_right_app Λ f K
```

Module-system notes (found while building it):
* An exported `:= rfl` theorem must check in the *public* view, so `moduleObjectDerivedPullback_eq
  := rfl` is rejected. A tactic proof (`delta …; rfl`) is accepted.
* A def whose body needs the hidden unfolding (`…Comp := leftDerivedUpperStarComp Λ f g`) must
  itself be `@[no_expose]`.
* A "bridge" lemma equating `(moduleObjectDerivedPullbackComp Λ f g).hom.app K` with
  `(leftDerivedUpperStarComp Λ f g).hom.app K` cannot even be *stated* in the public view: the two
  sides have different hom-types once the wrapper is opaque. Mixed statements are exactly what
  opacity forbids. Use `moduleObjectDerivedPullback_eq` (with `eqToHom`/`rw`) when a transition
  is really needed.

Consumer: the reproducer **with its original proofs**, the local def removed, and every
`leftDerivedUpperStarComp Λ` / `leftDerivedUpperStarId Λ` / `…_assoc_app` / `…_id_left_app` /
`…_id_right_app` replaced by the wrapper-vocabulary API, in `dncPullbackComp_congr_left/right`
and in the three repro theorems. `dncSectionSquareCoherenceVars` and `dncMapCancel` are
unchanged.

| variant | result | elab / kernel | wall / user / RSS (3 runs) |
|---|---|---|---|
| `v_irr`: same file, wrapper + API defined locally, then `attribute [irreducible] moduleObjectDerivedPullback` | **0 errors** | 2.8 s / 3.1 s | 26.5–29.6 / 22.5–25.7 / 1.99 GB |
| `v_nx`: real `@[no_expose]` across the module boundary (API module above + consumer) | **0 errors** | 1.1 s / 0.8 s | 9.5–12.4 / 6.0–8.0 / 1.98 GB (+23.5 s once for the API module) |

* `exact h2` and `congr 1` both succeed, because `h2`'s type and the goal are now in one
  vocabulary, so only the proof-only differences remain and the projection-level conversion
  never arises.
* `#print axioms` on `repro_exact_elab_timeout` and `repro_congr_kernel_timeout` gives
  `[propext, Classical.choice, Quot.sound]`. No `sorry` (apart from the pre-existing control
  `repro_have_ok`) and no checker options.
* As the user expected, local `irreducible` and cross-module `@[no_expose]` behave the same.
  `irreducible` only blocks elaborator unfolding (the kernel could still unfold), but nothing
  needs unfolding any more.

## 3. Comparison with the Report 2 repair

| | Report 2 (component lemmas) | Report 3 (opaque wrapper) |
|---|---|---|
| theorem statements | **unchanged** (`leftDerivedUpperStarComp/Id`) | changed to `moduleObjectDerivedPullbackComp/Id` |
| proofs | new: component lemma + 2 side lemmas, `Eq.trans` chain | **original** (`exact h2`, `congr 1`) |
| cost (full reproducer) | ~50 s wall / 45 s user / 2.07 GB | ~29 s (irreducible, all in one file); ~12 s consumer + 23.5 s API module (no_expose) |
| robustness | relies on unification order avoiding bad conversions | mixed-vocabulary statements become type errors, so the slow path cannot come back |
| upstream impact | none | needs the API in `CondensedModuleDerivedPushpull.lean`. The 61 files using `moduleObjectDerivedPullback`, several of which `unfold`/`delta` it, would have to stop mixing vocabularies (ignored here, as requested) |

**Recommendation.** If the vocabulary of these statements may change, the opaque wrapper is the
cleaner long-term design. Make it opaque, keep `moduleObjectDerivedPullback_eq`, and provide
`moduleObjectDerivedPullbackComp/Id` with assoc/unit lemmas in the defining module. If the
statements must keep `leftDerivedUpperStarComp`, use the Report 2 repair.
