# Lean 4 Kernel Performance Repair: Execution Guide for a Local Coding Agent

**Target:** `WeilConjectures/Reproducer.lean`  
**Initial environment to verify:** Lean / Mathlib 4.33.1; repository branch `slopmaster2`, revision `55376e1a60`  
**Primary objective:** Make the **original theorem statement** elaborate and pass ordinary Lean kernel checking, without the pathological conversion time or memory growth.  
**Secondary objective:** Leave behind a maintainable proof and useful, reproducible diagnostics, not merely a faster scratch experiment.

This is an **execution plan, not a verified patch**. Inspect the actual source declarations, local diagnostic reports, scratch files, and toolchain before filling in any schematic Lean code. You may consult online Lean/Mathlib documentation, version-matched upstream source, and issue discussions when they genuinely help answer a specific question. Do not substitute web information for measurements on the local project.

## 0. Non-negotiable rules

1. **Preserve the original theorem statement.** Keep its name, parameters, and declared type, including the original `leftDerivedUpperStarComp` / `leftDerivedUpperStarId` vocabulary. Do not silently replace these with `dncComp` / `dncId` in the final theorem. A separate theorem using the normalized API may be useful as a control or helper, but it is not the target repair.
2. **Use normal kernel validation.** No new `sorry`, `sorryAx`, axioms, `debug.skipKernelTC=true`, disabled checking, weakened checker settings, or heartbeat escalation as a final workaround. A diagnostic-only placeholder is acceptable in an isolated scratch file and must be removed from the final patch.
3. **`HEq` is permitted for diagnosis, not for the final repair.** Controlled `HEq` probes (including self-versus-cross comparisons) may isolate the costly conversion. Do **not** introduce `HEq` into committed theorem statements, new helper APIs, final proof terms, or the repair's transport mechanism. Prefer ordinary `Eq`, abstract component lemmas, exact parameter alignment, `calc`, and bounded congruence. Existing upstream definitions outside this patch are not in scope for this restriction.
4. **Keep a clean baseline.** Work in a dedicated worktree or `scratchpad/repair/`. Save each meaningful variant, its Lean source, command, full log, performance data, and short conclusion. Only merge a fully checked candidate.
5. **Test one hypothesis at a time.** Do not launch many Lean processes in parallel on an already busy shared machine. A fast elaboration followed by an equally expensive kernel check is **cost transfer**, not a fix.
6. **Do not start with library-wide changes.** Avoid editing `NatTrans.app`, `CategoryStruct.comp`, `Functor.map`, instance priorities, or the kernel itself unless higher-level experiments have ruled out a practical source-level boundary. Avoid `opaque` / `@[no_expose]` as default remedies.
7. **Report failures honestly.** If no candidate preserves the original statement with acceptable performance, retain the best checked partial result and identify the remaining smallest expensive expression/conversion. Never present a statement-changing workaround as complete success.

## 1. Established diagnosis and unresolved mechanism

Do not restart broad diagnosis unless a new variant produces materially different evidence.

### Observations already established

- `exact h2` leads to an **elaboration** timeout; `congr 1` makes elaboration easier but moves the expensive check into the **kernel**. Turning `Elab.async` on/off was not decisive.
- A structural comparison of `type h2` with the goal found **88 minimal differences**, **85** of which are spelling mismatches between `moduleObjectDerivedPullback Λ f` (abbreviated below as `mODP`) and `(f)^*⟦Λ⟧.leftDerivedFunctor` (abbreviated as `L(f)`). The other three were proof-only differences. Individual functor-pair comparisons took approximately **6–15 ms**.
- The worst conversion is the **first factor of the RHS**, at diagnostic path `type.2.5`: the `.hom.app X` of a composite natural isomorphism. Its individual `NatTrans.app` arguments compare cheaply, yet the complete application is costly: approximately **338 seconds / 3.74 GB RSS** in one Meta comparison, and roughly **108 seconds** before a deterministic kernel timeout in the corresponding cross-expression check.
- In the local environment, `NatTrans.app`, `Iso.hom`, `CategoryStruct.comp`, and `Functor.map` were observed to have `abbrev` kernel reducibility hints. The hypothesis that reductions descend through derived-category composition into localization machinery is **plausible but not yet confirmed by instrumented kernel tracing**.
- A normalized variant using `dncComp` / `dncId` typed in the `mODP` vocabulary **does pass ordinary kernel checking**, at approximately **30.4 s wall / 22.8 s user / 2.03 GB peak RSS** for the full file. However, that variant **changes the theorem statement**.
- Directly transporting that normalized theorem back to the original statement timed out. Rewriting the outer isomorphisms left mixed implicit source/target functors under `.app`. Expanding all concrete composite components using `simp` moved the cost into the kernel. Metavariable-driven `apply` improved elaboration but not kernel checking.
- Historical benchmarks were single runs on a heavily loaded shared machine. Treat their numbers as order-of-magnitude evidence rather than precise comparative benchmarks.

### Working interpretation

The slow operation is not a single elementary conversion `mODP f ≡ L(f)`. It is a **cross-representation conversion buried inside a dependent composite and then beneath a structure projection**. The practical goal is to prevent that particular comparison from arising during checking of the original theorem.

**Do not claim** that a particular C++ unfolding path is confirmed unless it is actually traced on the version-matched kernel.

## 2. Establish a trustworthy local baseline

1. Record `git rev-parse HEAD`, `lake env lean --version`, the actual Mathlib revision, `lakefile` options, hardware, machine load, and the commands used.
2. Copy the exact original theorem statement into the experiment notes. Distinguish *changing its proof body* from *changing its elaborated type*. The former is allowed; the latter is not the target repair.
3. Re-run three representative controls only: the original failing theorem, a cheap control stopping before the final conversion, and the previously successful normalized-statement variant if its scratch source still exists.
4. Use synchronous checking for phase localization and ordinary kernel checking for every candidate. Collect wall, user CPU, system CPU, peak RSS, elaboration time, per-declaration kernel times, and generated `_proof_n` costs.
5. Keep traced and untraced timings separate. Repeat only promising variants under comparable load, ideally at least three times.

The direct `lake env lean` invocation may require manually passing the project's relevant `leanOptions`:

```text
pp.unicode.fun=true
relaxedAutoImplicit=false
backward.isDefEq.respectTransparency=false
maxSynthPendingDepth=3
warn.sorry=false
```

Illustrative invocation; replace the target and supply all applicable options in the format accepted by the actual local toolchain:

```bash
TIME_BIN=/run/current-system/sw/bin/time
[ -x "$TIME_BIN" ] || TIME_BIN=/usr/bin/time

timeout 240 "$TIME_BIN" -v lake env lean \
  -DElab.async=false \
  -Ddebug.skipKernelTC=false \
  -Dtrace.profiler=true \
  -Dtrace.profiler.threshold=500 \
  -Dpp.unicode.fun=true \
  -DrelaxedAutoImplicit=false \
  -Dbackward.isDefEq.respectTransparency=false \
  -DmaxSynthPendingDepth=3 \
  -Dwarn.sorry=false \
  scratchpad/repair/candidate.lean \
  > scratchpad/repair/candidate.log 2>&1
```

For clean whole-file comparisons, rerun without profiler/diagnostic tracing. If a control times out, preserve where the time was spent rather than raising limits indefinitely.

## 3. Preferred repair: normalize composite components at the abstract level

**Central idea:** Prove component-expansion identities while functors, natural transformations, and natural isomorphisms are still **abstract parameters**. Then build a component-level coherence theorem and **instantiate it directly into the original goal**. Do not first prove the modified-statement result and attempt to cast it back afterward.

This is fundamentally different from unfolding a giant, already-instantiated derived-category expression with `simp at h2 ⊢`.

### Step A — Capture the exact expensive RHS expression

Locate the original theorem's first RHS factor, whose approximate shape is:

```lean
((leftDerivedUpperStarComp Λ i' bb).symm ≪≫
  eqToIso hR ≪≫
  leftDerivedUpperStarComp Λ b i).hom.app (La.obj C)
```

**This is a structural sketch, not guaranteed verbatim source.** Extract the exact expression, parentheses, relevant `eqToIso` type, source/target functors, object argument, and elaborated implicit arguments from `Reproducer.lean`.

Record for both the helper theorem and original goal:

- the exact composite isomorphism and its orientation;
- the implicit `F`, `G` arguments of the `NatTrans.app` at the hotspot;
- the displayed and actual expressions for each `.hom.app` or `.inv.app` leaf;
- whether the object `La.obj C` itself has multiple spellings;
- a structural diff at the smallest problematic position.

**Stop condition:** Do not write a bridge against a pretty-printed approximation of the type. Use the actual elaborated binder and application types.

### Step B — Prove generic component identities before concrete instantiation

Introduce compatible abstract isomorphisms `a`, `b`, `c` between abstract functors and prove an equality of their composite's component with a composite of their individual components.

**Schematic only; derive the universe parameters, typeclass assumptions, exact associativity, and correct Mathlib lemma names locally:**

```lean
private theorem isoTriple_hom_app_components
    (a : F ≅ G) (b : G ≅ H) (c : H ≅ I) (X : C) :
    (a ≪≫ b ≪≫ c).hom.app X =
      (a.hom.app X ≫ b.hom.app X) ≫ c.hom.app X := by
  -- Prove only with generic Iso/NatTrans/component lemmas
  -- and category associativity, before supplying concrete functors.
  ...
```

Also add specialized generic identities for a `.symm` factor and `eqToIso` where required by the actual expression. Carefully preserve arrow directions and parenthesization. Avoid deriving the generic lemma by first constructing the fully concrete composition.

Compile each generic lemma on its own with normal kernel checking. Record the time of any generated auxiliary declarations. Prefer a simple ordinary `Eq` statement that exposes the desired component form.

### Step C — Build a component-shaped coherence lemma

Create a scratch variant of the generic `dncSectionSquareCoherenceVars` theorem whose **conclusion itself is component-shaped**. Rather than a whole `((a ≪≫ b ≪≫ c).hom.app X)` as a single opaque-looking subexpression, state the corresponding composition in terms of leaves such as:

```lean
-- Schematic only: orientations, objects, and transports must
-- be determined from the actual theorem.
a.hom.app X ≫ b.hom.app X ≫ c.hom.app X
```

Requirements:

- Preserve the genuine coherence hypotheses, including associativity, units, map/cancellation hypotheses, and any required `eqToHom` transports.
- Prefer proving the component statement from generic coherence data **before** supplying the heavyweight concrete derived functors or isomorphisms.
- Keep the source/target functors, indices, and object arguments coherent at every leaf.
- Avoid making a new helper whose conclusion itself requires the original costly cross-representation `NatTrans.app` conversion.
- Compare the **actual instantiated type** of the component lemma against the original target. The difference must shrink toward inexpensive leaves rather than merely migrate into a theorem parameter.

Do not rewrite the production theorem or its API yet. The first deliverable is a fast, normally kernel-checked, abstract component lemma.

### Step D — Prove the original theorem directly

Keep the original statement intact. In its proof:

1. Instantiate the abstract component-coherence theorem using the functors and isomorphisms **as selected by the original goal**, not the normalized statement from the successful control.
2. Use the generic composite-to-components identity **at the proper outer level**, before a large concrete conversion is demanded.
3. Prefer a small `calc` chain or carefully localized rewrite over a global `simp` of both a helper theorem and the goal.
4. For each remaining leaf, check that both sides refer to the same upstream compositor. Where they do, ordinary `Eq` or a cheap, precisely typed rewrite may suffice.
5. Restore the whole equality using ordinary `Eq` transitivity, congruence, and category lemmas. Ensure the last `exact` is not secretly the same expensive cross-representation `.app` conversion.
6. Check the original declaration and every helper with the ordinary kernel. If the profiler still reports the hotspot at `type.2.5`, this branch has not succeeded.

### Two bounded subexperiments

**Component-factor experiment:** Check only the abstract normalization lemma and its instantiation at the exact original RHS first factor. Measure the conversion and proof-checking cost independently.

**Component-coherence experiment:** Change only the generic lemma's conclusion to component form, instantiate it, and recompute the structural diff before attempting the entire theorem.

Do not undertake a large refactor without one of these producing affirmative evidence.

## 4. Alternative repair: align implicit functor representations from the original goal

If the component route does not bridge back cheaply, start from the **original consumer type**, not the normalized helper's output.

1. Extract the true implicit `F`/`G` of the original `NatTrans.app` and the source/target types of the adjacent `Iso.hom` expressions.
2. Construct a generic helper whose dependent binders and component statement use the **same representation throughout**. Alignment must include explicit `.map`/`.obj` occurrences, identity and composition isomorphisms, and any functor-valued arguments—not just a few binder variables.
3. Test a type-only control before a proof-body experiment. Then reconstruct the theorem directly from the existing coherence primitives, without taking the normalized-statement theorem as the final proof term.
4. If changing everything to bare `L(f)` reproduces the previously observed `.map` statement-elaboration timeout, stop that branch and return to a regular-definition boundary or component lemma. Do not continue globally unfolding the wrapper.
5. Introduce a regular `def` as an interface only when both sides of the expensive check genuinely share that named head and comparing its arguments is cheap. Naming a term without aligning the two compared types is not sufficient.
6. At any unavoidable transition between `mODP` and the upstream form, place the comparison **above expensive projections** or at simple, individually measurable leaves.

**Success criterion:** The original declaration has the same elaborated type as before; its crucial hidden source/target arguments match structurally or are connected through a measured cheap proof, and kernel checking finishes without cost transfer.

## 5. Fallback: ordinary `Eq` bridges at cheap leaves only

Once the component proof is nearly finished, a small number of corresponding leaves may differ syntactically because one uses `dncComp` and the other uses `leftDerivedUpperStarComp`. Test ordinary equalities only at these **individual leaves**.

```lean
-- Schematic only. First verify the two terms can inhabit
-- the same equality type, and test the kernel cost separately.
private theorem comp_app_leaf_bridge (...) :
    (dncComp Λ f g).hom.app K =
      (leftDerivedUpperStarComp Λ f g).hom.app K := by
  rfl
```

Conditions:

- Keep the experiment restricted to an **uncomposed upstream isomorphism leaf**. Do not replace it with a full `Iso.trans` chain.
- Verify the ordinary `Eq` type is well-formed; its endpoint hom-types may involve dependent functor choices.
- If this `rfl` becomes expensive, abandon it. It is not a small bridge in the kernel's eyes.
- If a leaf cannot be expressed as an ordinary `Eq` without a major conversion, select consistent abstract functor parameters or change the component boundary instead.
- Use `rw`, `congrArg`, or `Eq.trans` only with individually checked, inexpensive leaf equalities. Total helper cost matters.

**Do not turn this fallback into a final `HEq`-based transport.** `HEq` remains available in isolated diagnostics to explain why ordinary `Eq` cannot be formed or which conversion is costly, but not as a committed proof mechanism.

## 6. Optional diagnostics and late-stage alternatives

Use these only when an earlier experiment points to the exact need.

### A. Controlled structural rewrite

A functor-level ordinary equality between `mODP` and `L(f)` may let a targeted rewrite align implicit arguments. Test **one RHS subexpression** first; do not assume `simp only` will repair all 85 differences.

Record the before/after structural diff, elaboration cost of the rewrite, kernel cost of the resulting proof term, and whether the original costly `.app` comparison actually disappears.

If needed, localize with `rw (occs := .pos [...])` or `conv`, using occurrence indices determined from actual source. Repeated wide rewrites that merely move the cost are not progress.

### B. A named proposition as an exact dependent-binder interface

If profiling identifies a slow conversion between the **actual type of a supplied argument** and the **expected binder domain** of a large generic constructor, extract that domain from the elaborated application. Consider a plain regular `def` naming the proposition, used consistently by both producer and consumer:

```lean
-- Schematic; derive parameters from the real expected binder type.
def SectionComponentCompatibility (params : ...) : Prop :=
  ...
```

The key is **the same regular-definition head at the expensive comparison**, not merely another local `have` or an `abbrev` wrapper. Check all helper declarations and the original caller. Do not use this route without evidence of a binder-domain bottleneck.

### C. `HEq` controls (diagnostic-only)

If an apparent conversion is still hard to locate, controlled probes may be useful:

- `HEq a a`, `HEq b b`: self-check/typing controls;
- `HEq a b` with reflexivity: cross-expression conversion;
- the proposition type with a diagnostic placeholder: cost of checking the proposition itself;
- a separate equality of `type(a)` and `type(b)` when this makes sense.

Run each expensive probe separately and record per-check CPU/RSS. A cross-expression timeout with fast self-checks supports a bad conversion hypothesis; it does **not** tell you which final repair to adopt. **Never paste diagnostic `HEq` proofs, placeholders, or their helper declarations into the final source patch.**

### D. Exact-kernel-path investigation

Only after high-level options fail, inspect version-matched Lean kernel/Meta implementation and, if necessary, use bounded C++ tracing of definitional equality, lazy delta reduction, projections, and proof irrelevance. Record depth, duration, heads, arity, and the smallest slow argument pair. Avoid unbounded logging, which can itself distort CPU and memory results.

An online implementation or newer Lean release may suggest a hypothesis, but any conclusion about this project must be verified on its actual toolchain. A toolchain upgrade is a separate experiment, not an assumed repair.

## 7. Failure signals and stop conditions

| Symptom | Interpretation / action |
|---|---|
| Final `exact` or `change` stalls | Likely the original whole-expression definitional equality. Rebuild a higher-level component equality; do not increase heartbeat. |
| `congr 1` elaborates quickly but kernel times out | Known cost transfer. Do not repeat. |
| Broad `simp` succeeds but kernel times out | Another cost transfer. Stop whole-expression rewriting. |
| Rewriting outer isomorphisms leaves mixed implicit `F`/`G` | The old transport failure is reproduced. Extract hidden arguments and repair them structurally. |
| Generic abstract lemma is fast, concrete instantiation slow | Locate the bad argument/domain and move the abstraction boundary earlier. |
| Bare `L(f)` form times out around `.map`/`.obj` during statement elaboration | Reproduces the failed representation strategy. Restore the regular wrapper where appropriate. |
| New helper consumes minutes of kernel time | The cost moved. Measure combined cost and redesign the interface. |
| A leaf equality is ill-typed because endpoints differ | Do not force it; align abstract parameters or use a different ordinary-`Eq` component statement. Diagnostic `HEq` may help characterize it. |
| Same negative variant repeatedly exceeds set CPU/RSS limits | Preserve the counterexample and move to a different structural hypothesis. |
| Only the modified-statement control passes | Useful partial evidence, **not** completion of the primary task. |

Use explicit time/RSS ceilings for experiments. Keep the evidence for a failed branch rather than rerunning the same costly conversion under ever-larger limits.

## 8. Acceptance and release checklist

The work is complete only if all apply:

- [ ] **Original theorem statement preserved**, including its intended parameters and upstream compositor expressions; compare the actual elaborated declaration type when possible, not only pretty-printing.
- [ ] The proof and all newly introduced helpers compile with **ordinary kernel checking** (`debug.skipKernelTC=false`).
- [ ] No new `sorry`, `sorryAx`, diagnostic axiom, or checker weakening exists in the final patch.
- [ ] **No `HEq` in the final repair code or newly added proof/helper API.** All diagnostic `HEq` probes stay in scratch files and are not imported by production declarations.
- [ ] `#print axioms` on critical declarations shows no unexpected new dependencies; the previously observed normal set was `[propext, Classical.choice, Quot.sound]`.
- [ ] Whole-file timing includes every new helper and generated `_proof_n`, not only the final theorem. Verify that CPU and RSS improvement is real, not transferred to another declaration or imported module.
- [ ] Compare the candidate with both the cheap baseline and normalized-statement positive control; repeat the best candidate at least three times when the machine load permits.
- [ ] Check at least one real downstream use of the unchanged theorem; rebuild affected consumers if shared APIs were modified.
- [ ] Deliver a minimal source diff, reproduction commands, logs, and a concise explanation of *which conversion was avoided*.

If preserving the original theorem remains unsolved, do not merge a statement-changing control as though it satisfied these criteria. Report the smallest remaining bottleneck and the best verified partial alternative.

## 9. Required final report

```text
Environment
  Lean / Mathlib / git revision / effective options / machine load

Baseline
  original failure / cheap control / normalized-statement control
  wall / user CPU / system CPU / peak RSS / kernel hotspots

Diagnosis
  confirmed 88 differences (85 functor spellings)
  first RHS factor (type.2.5)
  measured facts vs hypotheses about kernel reductions

Experiments
  variant, exact change, compiled or failed, failure phase
  elaboration / all kernel declarations / CPU / RSS
  structural diff before/after
  eliminated conversion or transferred cost?
  if diagnostic HEq was used, explain its evidence and verify its removal

Final candidate
  is the original theorem statement preserved? yes/no
  changed files and minimal source diff
  proof architecture and how it avoids the costly conversion

Validation
  ordinary kernel / no new axioms / no final HEq / no sorry
  repeated timings / downstream build

Open issues
  smallest remaining costly pair and next discriminating experiment
```

## 10. Execution order and decision rule

1. **First:** Capture the exact original RHS hotspot; prove abstract composite-component identities; build a component-shaped generic coherence theorem; instantiate it **directly against the unchanged original statement**.
2. **Second:** If necessary, align all dependent functor representations using the actual original consumer type, rather than rewriting only some isomorphisms or binder variables.
3. **Third:** Use measured cheap ordinary `Eq` leaf bridges and localized rewriting, or a regular-definition proposition boundary **only where profiling shows the relevant conversion**.
4. **Finally:** Use controlled `HEq` diagnostics or bounded kernel tracing to resolve a remaining uncertainty, but **never ship `HEq` as part of the repair**.

**Go/no-go rule:** A variant is a viable repair only when the original theorem's type is unchanged, the complete proof passes ordinary kernel checking, all helpers are accounted for, and the pathological CPU/RSS cost has been eliminated rather than relocated.
