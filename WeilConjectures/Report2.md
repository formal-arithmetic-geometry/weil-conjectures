# Report 2 — Repairing `Reproducer.lean` with the original statement preserved

Follows `DiagnoseGuide2.md`. **Outcome: solved.** Both formerly failing theorems,
`repro_exact_elab_timeout` and `repro_congr_kernel_timeout`, now compile with their **original,
unchanged statements** under ordinary kernel checking, in about 3 s of kernel time each, with no
`sorry`, no `HEq`, no checker options and standard axioms. The repaired file is
`WeilConjectures/ReproducerFixed.lean` (new file; `Reproducer.lean` itself is untouched).
Experiments live in the session scratchpad under `repair/` (sources, logs, the `run.sh` runner).

## Environment

| item | value |
|---|---|
| Lean / Mathlib | 4.33.1 (commit 819816b2e0a3) / v4.33.1 |
| revision | `slopmaster2` at `55376e1a604f504c0e4a670a051e87c9ac9acb5b` |
| machine | 24 cores, 94 GB RAM, shared; load average **35–65** during all runs |
| options | `-DElab.async=false -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dbackward.isDefEq.respectTransparency=false -DmaxSynthPendingDepth=3 -Dwarn.sorry=false -Dlinter.style.longLine=false`; profiler runs add `-Dprofiler=true -Dprofiler.threshold=300/500` |
| command | `timeout 2400 time lake env lean <options> <file>`, one process at a time |

## The original statement (unchanged)

The statement block of `repro_exact_elab_timeout` (and the identical one of
`repro_congr_kernel_timeout`) is byte-identical between `Reproducer.lean` and
`ReproducerFixed.lean` (checked with `diff`). The elaborated declared types are also identical:
compared against a sorried copy of the original statement in the same file, they are `==`
(alpha-equivalent), contain no `mdata`, give 0 structural differences, and have the same
universe parameters `[u]`. They are not `Expr.equal`, but the only difference is hygienic binder
names, which the kernel ignores.

## Baseline (this round)

| file | result | wall s | user s | peak RSS |
|---|---|---|---|---|
| original `repro_exact_elab_timeout` (prefix + theorem) | elaboration timeout (`isDefEq`/`whnf`) | 50.7 | 46.7 | 2.17 GB |
| original full `Reproducer.lean` (round 1) | 2 errors (elab timeout + kernel timeout) | ~152 | — | 3.7 GB (kernel variant) |
| cheap control `repro_have_ok` (prefix + theorem, sorried goal) | ok | 26.7 | 23.3 | 2.06 GB |
| normalized-statement control X6 (statement changed) | ok | 22.8 | 20.0 | 1.99 GB |

## Experiments

All with ordinary kernel checking. "Exact replaced by sorry" variants are diagnostic only.

| id | change (proof body only) | elaboration | kernel | wall / user / RSS | finding |
|---|---|---|---|---|---|
| Y1 | new abstract **component-shaped** lemma `dncSectionSquareCoherenceComp` (proved from `dncSectionSquareCoherenceVars` while everything is a variable); in the theorem `simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, eqToIso.hom, NatTrans.comp_app, eqToHom_app, Functor.map_comp, Category.assoc]` on the **goal only**, then `exact h2` | 2.3 s | **timeout (121 s)** | 157 / 135 / 3.70 GB | cost transfer |
| Y1a | as Y1, final `exact` replaced by `sorry` | 2.0 s | **timeout (108 s)** | 130 / 120 / 3.74 GB | the **goal-side `simp` proof alone** is the kernel hotspot. Most lemmas in the set are `rfl` lemmas; `simp` uses them definitionally, so the kernel must re-verify, for example, `(α ≫ β).app X ≡ α.app X ≫ β.app X` by conversion inside the *concrete* derived categories. The abstract lemma needs the same steps and checks in about 1 s |
| Y2 | as Y1 but `repeat' first \| rw [Iso.trans_hom] \| …` (explicit `Eq` steps) | **timeout** (`isDefEq` in a `rw`) | – | 35.4 / 30.8 / 2.04 GB | keyed matching / motive checking of generic projection lemmas against the mixed-spelling concrete goal is expensive in the elaborator |
| Y3a | two shape-specific abstract lemmas (`(α.symm ≪≫ eqToIso p ≪≫ β).hom.app X = …`, `((α.app X).symm ≪≫ eqToIso p ≪≫ β.app X).hom = …`), one `rw` per occurrence | 1st `rw` ok (5.2 s), 2nd **timeout** | – | 37.5 / 32.5 / 2.04 GB | rewriting the concrete goal keeps provoking cross-spelling conversions; branch stopped |
| **Y4** | two abstract **side lemmas** `dncLHS_components`, `dncRHS_components` (whole LHS / RHS shape = component form, proved by `simp` on variables), chained with no rewriting: `refine Eq.trans ?_ (Eq.trans h2 ?_)`, then `apply dncLHS_components`, then `symm; apply dncRHS_components`; `h2` comes from the component lemma | **2.2 s** | **6.5 s total** (whole file) | 30.0 / 26.6 / 2.06 GB | **works** |
| Y4a | Y4 with the RHS step sorried | 2.3 s | 6.7 s | 30.3 / 26.7 / 2.06 GB | the LHS step on its own costs nothing measurable |

Not repeated (per the guide's stop list): `congr 1`, global `simp at h2 ⊢`, bare `L(f)`
re-spelling, Iso-level transport back from the normalized theorem.

## Final candidate

**Statement preserved: yes.** Changed/added code (relative to `Reproducer.lean`):

```lean
-- (1) after `dncSectionSquareCoherenceVars`: its component form, proved on variables
theorem dncSectionSquareCoherenceComp … (same binders and hypotheses) … :
    Li'.map (cbba.inv.app C) ≫ Li'.map (eqToHom (Functor.congr_obj hP C)) ≫
        Li'.map (ca'b.hom.app C) ≫ ci'a'.inv.app (Lb.obj C) ≫
          eqToHom (Functor.congr_obj hQ (Lb.obj C)) ≫ e'.hom.app (Lb.obj C) =
      ci'bb.inv.app (La.obj C) ≫ eqToHom (Functor.congr_obj hR (La.obj C)) ≫
        cbi.hom.app (La.obj C) ≫ Lb.map (cia.inv.app C) ≫
          Lb.map (eqToHom (Functor.congr_obj hS C)) ≫ Lb.map (e.hom.app C) := by
  have h := dncSectionSquareCoherenceVars hP hQ hR hS hT₁ … C A₁ CR₁ A₂ CL₁ U₁ CL₂ A₃ CR₂ U₂
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, eqToIso.hom,
    NatTrans.comp_app, eqToHom_app, Functor.map_comp, Category.assoc] using h

-- (2) composite-to-component identities for the two sides, on variables (eqToIso proofs are
--     arbitrary `p q s`, so they unify with whatever proof the goal contains)
theorem dncLHS_components … (cbba : P₁ ≅ La ⋙ Lbb) (ca'b : P₂ ≅ Lb ⋙ La') (ci'a' : Q₁ ≅ La' ⋙ Li')
    (e' : I' ≅ 𝟭 _) (C : 𝒟B) (p : P₁.obj C = P₂.obj C) (q : Q₁.obj (Lb.obj C) = I'.obj (Lb.obj C)) :
    Li'.map ((cbba.app C).symm ≪≫ eqToIso p ≪≫ ca'b.app C).hom ≫
        ((ci'a'.app (Lb.obj C)).symm ≪≫ eqToIso q ≪≫ e'.app (Lb.obj C)).hom =
      Li'.map (cbba.inv.app C) ≫ Li'.map (eqToHom p) ≫ Li'.map (ca'b.hom.app C) ≫
        ci'a'.inv.app (Lb.obj C) ≫ eqToHom q ≫ e'.hom.app (Lb.obj C) := by simp
theorem dncRHS_components … (analogous, for `(ci'bb.symm ≪≫ eqToIso hR ≪≫ cbi).hom.app _ ≫ Lb.map (…).hom`)

-- (3) in both repro theorems: `have h := dncSectionSquareCoherenceComp` (same named arguments
--     as before) and the ending
  refine Eq.trans ?_ (Eq.trans h2 ?_)
  · apply dncLHS_components
  · symm
    apply dncRHS_components
```

`diff Reproducer.lean ReproducerFixed.lean`: +69 lines of helper lemmas, plus in each of the two
theorems one `have` line changed and the proof ending replaced (`exact h2` → 4 lines;
`· congr 1 · congr 1` → 3 lines), plus the two docstrings updated.

### Why it avoids the costly conversion

* Previously, `h2`'s type (with functor variables instantiated by name, spelled `mODP`) had to be
  converted to the goal (whose hidden `F`/`G` come from the compositors' types, spelled `L(f)`).
  The hotspot was the composite natural isomorphism under `NatTrans.app` at path `type.2.5`.
* Now the composite-to-components step is a single application of an abstract lemma whose
  **variables are assigned by unification from the goal's own subterms** (`apply`, which also
  gives the Meta unifier its args-first heuristic because metavariables are present). The
  composite in the lemma instance is therefore built from exactly the goal's pieces, and no
  mixed-spelling composite is compared under a projection.
* The remaining mismatches between the lemma instances, `h2` and the goal sit only in
  **component form**, so `NatTrans.app`/`Iso.inv`/`Functor.map` are applied to single upstream
  compositors (stuck leaves), or in object/functor positions. Structural diff after the repair,
  grouped by outermost enclosing heads:
  * `dncLHS_components` instance vs goal: 68 pairs.
  * `dncRHS_components` instance vs goal: 3629 pairs. Of these, 3581 are inside the `Eq`'s type
    argument (`Quiver.Hom (…).obj (…).obj`: object spellings `(F ⋙ G).obj X` vs `G.obj (F.obj X)`,
    which the positional diff aligns crudely and walks into the large `DerivedCategory`
    instance terms). The remaining ~116 are at `CategoryStruct.comp` argument positions: 6 under
    `NatTrans.app`, 16 under `Functor.map`, 19 under `Iso.hom`, and the 3 proof-only pairs.
  * Every leaf-level pair is a functor-spelling pair (`mODP f` vs `L(f)`) under a single
    compositor, the case found cheap in round 1 (as in `repro_have_ok`).
* The kernel cost confirms it: about 3 s per repro theorem instead of a 100 s+ timeout.

What remains hypothesis: the exact kernel reduction path behind the original cost. The repair
was found by measurement, not by tracing the C++ kernel.

## Validation

* **Ordinary kernel:** no `debug.skipKernelTC`, default `maxHeartbeats`, `Elab.async=false`.
  0 errors.
* **Axioms:** `#print axioms` on `repro_exact_elab_timeout`, `dncSectionSquareCoherenceComp`,
  `dncLHS_components`, `dncRHS_components` gives `[propext, Classical.choice, Quot.sound]`.
* **No `sorry` / `HEq` / checker options** in the new code (grep). `repro_have_ok` keeps its
  pre-existing intentional `sorry` (it is the cheap control and was not touched). `HEq` was
  used only in round-1 diagnostics in scratch.
* **Repeated timings** of the full repaired file (all 3 theorems + all helpers):

  | run | wall s | user s | sys s | peak RSS |
  |---|---|---|---|---|
  | 1 | 53.6 | 44.9 | 4.3 | 2.07 GB |
  | 2 | 50.9 | 46.6 | 3.0 | 2.08 GB |
  | 3 | 49.8 | 44.1 | 4.1 | 2.07 GB |
  | profiled | 47.5 | 43.8 | 2.1 | 2.08 GB |

  Profiled breakdown: elaboration 3.8 s total, kernel 11.8 s total. Per-declaration kernel times
  over 300 ms: 0.97 s and 0.88 s (helpers), and 2.87 s, 3.08 s, 2.94 s (the three repro
  theorems). The rest is import/initialization. Compared with the original full file (about
  152 s wall, 3.7 GB, 2 errors), the remaining cost is spread normally over all declarations,
  not concentrated in a transferred helper. Peak RSS equals the cheap control (about 2.06 GB).
  The ~20 s per-file gap to the single-theorem controls corresponds to the two additional full
  theorems in the file.
* **Downstream:** nothing in the repository references `repro_*` or
  `dncSectionSquareCoherenceVars`/`…Comp` outside the two reproducer files, so there is no
  consumer to rebuild. No shared API was modified.

## Open issues / notes

* The pattern generalizes. When an abstract coherence lemma is instantiated with functors written
  in one spelling (`moduleObjectDerivedPullback`) while the concrete compositors are typed in
  another (`L(f)`), do not ask the kernel to convert composite isomorphisms under
  `NatTrans.app`/`Functor.map`. Provide component-form versions of the coherence lemma, plus
  abstract composite-to-component lemmas applied by unification against the goal. Rewriting the
  concrete goal with `simp` (rfl lemmas are checked by conversion) or with generic `rw` was
  expensive in every variant.
* The side lemmas are specific to this LHS/RHS shape. For other coherence statements of the same
  family, analogous shape lemmas (or one generic "`(α.symm ≪≫ eqToIso p ≪≫ β).hom.app X` =
  components" lemma applied via `Eq.trans` rather than `rw`) should be written. That generic
  `Eq.trans` route was not separately tested here.
* Timings are from a heavily loaded shared machine. Compare relative numbers only.
