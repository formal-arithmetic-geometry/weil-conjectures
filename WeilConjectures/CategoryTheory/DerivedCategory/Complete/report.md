# Kernel timeout of `DerivedCategory.derivedCompletionCone` — diagnostic report

*Status: in progress. Sections are appended as evidence comes in.*

## 0. The question

In `WeilConjectures/CategoryTheory/DerivedCategory/Complete/Defs.lean`, the declaration

```lean
noncomputable def DerivedCategory.derivedCompletionCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) :=
  sorry
```

does not compile, **even with the value replaced by `sorry`**. Since `sorry` carries no
mathematical content, whatever is expensive lives entirely in the *declared type*
(or in the act of adding a declaration with that type to the environment).

## 1. Environment

```text
Lean            : leanprover/lean4 v4.33.1
mathlib         : v4.33.1
branch          : OE-coefficient-derived-category @ b4385e0b
machine         : linux 6.18.40
lean invocation : lake env lean -D backward.isDefEq.respectTransparency=false
                                -D maxSynthPendingDepth=3 …
```

(The `backward.isDefEq.respectTransparency=false` option is load-bearing for this
repository; a bare `lake env lean` gives spurious transparency errors.)

## 2. Phase 1 — elaboration or kernel?

| # | Experiment | Wall time |
|---|---|---|
| B | `Defs.lean` exactly as committed (imports + `#check` of the target type, no `def`) | **5.1 s** |
| E1 | add `def … : Cone (quotPowFunctor J I ⋙ tensorLeft K) := sorry` | **> 600 s** (killed) |
| E2 | same, with `set_option debug.skipKernelTC true` | **17.7 s** |

Reading of the table:

* B → E2 is the cost of *elaborating* the declaration: ≈ **12 s**. That includes
  synthesising `MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat R)))` and
  building the full type expression. Slow, but finite and not the blocker.
* E2 → E1 is the cost of **kernel checking alone**: it goes from 12 s to more than
  10 minutes.

**Conclusion 1. The blocker is the kernel, not the elaborator, not typeclass search.**

A corollary worth stating explicitly, because it is what the previous round of work was
about: `abbrev` vs `@[reducible] def` *is* a real distinction for the kernel (it changes
the reducibility hint), but no elaborator-side transparency knob can help here — the
elaborator is already done after 12 s.

## 3. Why the standard playbook only partly applies here

The playbook in this folder was written for the derived-tensor case, where the shape was

```text
Kernel.check(value)                       fast
Kernel.isDefEq(inferredType, declaredType) slow
```

i.e. two *independently elaborated* expressions that had to be reconciled. That shape
cannot be the story here: the value is `sorryAx T` with **the very same `T`** that is
declared, so `inferredType` and `declaredType` are pointer-identical and `isDefEq`
should be free.

So the interesting question is different, and needs a different instrument:

> **Why is `Kernel.check` of a single, already-elaborated type expression slow?**

Sections below build an instrument for exactly that: kernel-checking *subterms* of the
declared type and timing them, rather than tracing `isDefEq` pairs.

## 4. A better instrument for this case

Two purpose-built probes are used instead of the playbook's `isDefEq`-pair tracing.

### 4.1 Move the type into value position

```lean
noncomputable def E7 (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) : Type (u + 2) :=
  Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K)
```

Now the declared type is the trivial `Type (u + 2)` and the *value* is the expression we
care about. `Kernel.check(value)` is then exactly "kernel-typecheck this type expression",
with no confounding final conversion. If this is slow, the cost is intrinsic to
typechecking the expression; if it is fast while the original is slow, the cost is in how
the declaration is added, not in the expression.

### 4.2 Subterm timing of `Kernel.check`

`Kernel.check env lctx e` on an application `f a₀ … aₙ` does more than check the pieces:
after inferring each `aᵢ`'s type it must prove that type definitionally equal to the
corresponding domain of `f`'s (whnf'd) type. Those conversions are invisible to
`sizeWithoutSharing` and to unfold histograms, but they are directly measurable:

* time `Kernel.check` on each argument `aᵢ` separately — this is the *intrinsic* cost of
  the argument;
* time `Kernel.check` on every prefix `f a₀ … a_{k-1}` for `k = 0 … n+1` — the increment
  from prefix `k` to prefix `k+1` is the cost of checking `a_k` **plus** the conversion of
  its inferred type against the expected domain;
* recurse into whichever argument dominates.

Running the probe needs the declaration in the environment without the kernel having
accepted it, which `set_option debug.skipKernelTC true` provides; the type is then opened
with `Meta.forallTelescope` so that its free variables live in a real `LocalContext` that
`Kernel.check` accepts.

The probe source is in
`scratchpad/kernelperf/probe.lean` (reproduced in the appendix of this report).

## 5. Phase 2 — which ingredient of the type is expensive?

All of the following are `… := sorry`, so only the type matters. Times include the
≈ 5 s fixed cost of loading the imports.

| # | Declared type | Wall time |
|---|---|---|
| E5a | `Cone F` for an abstract `F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat R))` | 6.5 s |
| E5b | `Cone (DerivedCategory.quotPowFunctor J I)` | (same run) |
| E5c | `Cone (DerivedCategory.quotPowFunctor J I ⋙ 𝟭 _)` | (same run) |
| E1 | `Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K)` | > 600 s |

E5a/E5b/E5c are all in one 6.5 s file. So:

* `Cone` applied to a functor into `DerivedCategory (Sheaf J (ModuleCat R))` is cheap;
* the tower `DerivedCategory.quotPowFunctor J I` — constant sheaf, `singleFunctor`,
  `Ideal.quotPowFunctor` — is cheap;
* `Functor.comp` (`⋙`) is cheap, even with this category on both sides.

**Conclusion 2. The entire cost is attached to `tensorLeft K`, i.e. to the
`MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat R)))` instance expression that
appears inside its type.**

## 6. The term is small — this is not a term-size problem

Measured on the elaborated type (`debug.skipKernelTC` + reading `ConstantInfo.type`):

| declaration | distinct subterms (size **with** sharing) | `sizeWithoutSharing` |
|---|---|---|
| `Cone (quotPowFunctor J I ⋙ tensorLeft K)` | **337** | 6 217 |
| `Cone F` (abstract `F`), control | 269 | 2 427 |

So the pathological type is a 337-node DAG, only ~70 nodes bigger than a control that
kernel-checks in milliseconds, and it takes the kernel more than ten minutes.

**Conclusion 3. There is no term blow-up.** The kernel is not drowning in a huge
expression; it is entering an expensive *reduction* on a small one. Anything that only
shrinks terms (more sharing, fewer implicit arguments) will not help.

## 7. What the type actually is

`#print` with `pp.explicit` on the (kernel-skipped) declaration gives, for the body:

```text
@Cone.{0, u+1, 0, u+2} (Opposite ℕ) (Category.opposite …)
  (@DerivedCategory Sh catSh abSh hasDerivedSh)
  (@instCategoryDerivedCategory Sh catSh abSh hasDerivedSh)
  (@Functor.comp … (@DerivedCategory.quotPowFunctor C inst inst₁ J R inst₂ I)
     (@tensorLeft
        (@DerivedCategory Sh catSh abSh hasDerivedSh)
        (@instCategoryDerivedCategory Sh catSh abSh hasDerivedSh)
        (@DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
           Sh catSh abSh ⟨IsGrothendieckAbelian⟩ hasDerivedSh
           (@GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall …
              (@ModuleCat.monoidalCategory R _)
              (@ModuleCat.MonoidalCategory.instBraidedCategory R _)     -- ⟵ (α)
              (@ModuleCat.instMonoidalClosed R _))
           (@GrothendieckTopology.monoidalClosed_sheaf_of_essentiallySmall …
              (@ModuleCat.monoidalCategory R _)
              (@ModuleCat.MonoidalCategory.symmetricCategory R _)       -- ⟵ (β)
              (@ModuleCat.instMonoidalClosed R _))
           ⟨MonoidalPreadditive⟩
           (@GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall …
              (@ModuleCat.monoidalCategory R _)
              (@ModuleCat.MonoidalCategory.instBraidedCategory R _)     -- ⟵ (α)
              (@ModuleCat.instMonoidalClosed R _))
           ⟨Qh.HasDerivedMonoidalCategory⟩)
        K))
```

where `Sh = @Sheaf C inst J (ModuleCat R) _`.

Two things stand out and are the subject of the next sections.

1. The braiding arguments marked (α) and (β) are **not the same expression**.
   `monoidalCategory_sheaf_of_essentiallySmall` and `braidedCategory_sheaf_of_essentiallySmall`
   are stated over `[BraidedCategory A]` and received `ModuleCat.MonoidalCategory.instBraidedCategory`,
   while `monoidalClosed_sheaf_of_essentiallySmall` is stated over `[SymmetricCategory A]`
   (see `WeilConjectures/CategoryTheory/GrothendieckAbelian/Monoidal/TensorColimits.lean`,
   "the braiding is strengthened to a symmetry: Day's reflection theorem is stated for a
   symmetric ambient category") and received `ModuleCat.MonoidalCategory.symmetricCategory`.
   `MonoidalClosed C` carries `[MonoidalCategory C]` as a parameter, so the *type* of the
   (β) term is `@MonoidalClosed Sh catSh (monoidalCategory_sheaf_of_essentiallySmall … (SymmetricCategory.toBraidedCategory …) …)`
   whereas the position it is being passed into expects
   `@MonoidalClosed Sh catSh (monoidalCategory_sheaf_of_essentiallySmall … instBraidedCategory …)`.
   That is a same-head pair with one genuinely differing argument, which the kernel must
   reconcile.

2. `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory` is a shortcut instance
   whose body is literally `inferInstance`
   (`WeilConjectures/CategoryTheory/Monoidal/Instances/DerivedCategory.lean`), inside an
   `@[expose] public section`. Its body is therefore fully available to the kernel, and
   unfolding it exposes the whole K-flat derived-monoidal construction.

*Section 8 (subterm timing) pending — the probe of §4.2 is running.*

## 8. Phase 3 — splitting the kernel's work

Probe: add the declaration with `debug.skipKernelTC true`, then replay each kernel step by
hand (`Kernel.check` / `Kernel.isDefEq`), logging to a file handle — note that plain
`IO.println` inside `run_cmd` is captured by Lean's frontend and only surfaces when the
command finishes, which is useless for a step that never finishes.

```text
1. Kernel.check(declared type)          3 ms      ok
2. Kernel.check(value)                  3 ms      ok
   inferred type structurally equal to declared type?   false
3. Kernel.isDefEq(inferred, declared)   > 10 min  (never observed to finish)
```

Independent confirmations of the same split:

| # | Declaration | Wall time |
|---|---|---|
| E16 | `axiom E16 (K) : Cone (quotPowFunctor J I ⋙ tensorLeft K)` — kernel checks **only the type**, there is no value and no final conversion | **6.7 s** |
| E7 | `def E7 (K) : Type (u+2) := Cone (quotPowFunctor J I ⋙ tensorLeft K)` — the same expression in **value** position, trivial declared type | **5.3 s** |
| E1 | `def (K) : Cone (quotPowFunctor J I ⋙ tensorLeft K) := sorry` | > 600 s |
| E17 | `def E17 (K) (c : Cone (quotPowFunctor J I ⋙ tensorLeft K)) : ℕ := 0` — same type, only as a hypothesis | > 400 s |
| E13 | same as E1 but with `[monD : MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat R)))]` as a **hypothesis** instead of the concrete instance | **18 s** |

**Conclusion 4.** Neither the type nor the value is hard for the kernel. The declaration is
slow only when the kernel has to prove the *inferred* type of the value definitionally
equal to the *declared* type — and those two are **not** the same expression, even though
the value is `sorry`.

## 9. Why the two types differ: nested-proof abstraction

The reason is a Lean elaboration step, not anything mathematical.

Before `Lean.addDecl`, every definition's **value** is passed through
`Lean.Meta.abstractNestedProofs` (`Lean/Elab/PreDefinition/Basic.lean:120`,
`Lean/Meta/AbstractNestedProofs.lean`): each non-trivial *proof* occurring inside the value
is lifted into an auxiliary theorem `Foo._proof_k` and replaced by a reference to it. This
pass also rewrites the proofs nested inside the *types* it meets on the way
(`abstractProof … (postprocessType := visit)`), and it has a module-wide cache, so a proof
already abstracted for an earlier declaration is reused under that declaration's name.

The declaration's **declared type** is *not* passed through this pass.

Here the value is `fun … K => sorryAx (Cone (quotPowFunctor J I ⋙ tensorLeft K)) …`, so the
type occurs inside the value, gets its proofs abstracted, and the inferred type comes back
different from the declared one. A structural diff of the two (probe `e19.lean`) reports
**36 minimal differing positions, every single one a proof**:

```text
inferred (from the value)                     declared (from the source)
────────────────────────────────────────────  ──────────────────────────────────────────────────────
DerivedCategory.quotPowFunctor._proof_1   ↔   GrothendieckTopology.hasSheafify_of_essentiallySmall
DerivedCategory.quotPowFunctor._proof_2   ↔   GrothendieckTopology.isGrothendieckAbelian_sheaf_of_essentiallySmall
DCC._proof_1                              ↔   instIsGrothendieckAbelianModuleCat
DCC._proof_3                              ↔   CategoryTheory.Sheaf.monoidalPreadditive
DCC._proof_8                              ↔   DerivedCategory.hasDerivedMonoidalCategory
```

(The `quotPowFunctor._proof_*` names come from the abstraction cache: the very same proofs
were already lifted when `DerivedCategory.quotPowFunctor`, a few lines earlier in the same
file, was elaborated.)

## 10. Why 36 proof mismatches cost more than ten minutes

The proofs themselves are irrelevant — that is the point of proof irrelevance. But to *use*
proof irrelevance on a pair `p₁ =?= p₂` the kernel must first prove

```text
type(p₁)  =?=  type(p₂)
```

and here those propositions are not closed, self-contained statements: they are things like

```text
MonoidalPreadditive (Sheaf J (ModuleCat R))            -- needs the MonoidalCategory instance
Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso …)   -- needs Qh, hence HasDerivedCategory
IsGrothendieckAbelian (Sheaf J (ModuleCat R))          -- needs the abelian structure
```

whose own instance arguments are **data-valued** terms
(`monoidalCategory_sheaf_of_essentiallySmall …`,
`HasDerivedCategory.ofIsGrothendieckAbelian …`,
`monoidalCategoryOfMonoidalClosedBraidedCategory …`) that are *themselves* parameterised by
the proofs being compared. So each proof-irrelevance step hands the kernel another pair of
large instance expressions differing in further proof positions, and the descent fans out
over all 36 sites. E12 (below) did not merely time out: it was **OOM-killed after 8 m 24 s**,
which is what a fan-out of this shape looks like from the outside.

This is exactly the situation §22 of the playbook warns about: the proof bodies cost
nothing, and essentially all of the runtime is spent proving the *propositions* equal.

## 11. Hypotheses ruled out

| Hypothesis | Test | Verdict |
|---|---|---|
| Elaboration / typeclass search is the bottleneck | `debug.skipKernelTC` ⇒ 17.7 s | **ruled out** |
| The type is too big / loses sharing | 337 distinct subterms, 6 217 unshared | **ruled out** |
| `Cone`, `Functor.comp`, or the `quotPow` tower are expensive | E5a/E5b/E5c all fast | **ruled out** |
| The expression is intrinsically hard for the kernel | `Kernel.check` on it = 3 ms (E7, E16) | **ruled out** |
| `abbrev` vs `@[reducible] def` on the outer head | the elaborator is already finished; the mismatch is between two *closed* terms | **not applicable here** |
| The braided-vs-symmetric instance mismatch (§7(1)) is the cause | E12: supply `MonoidalClosed (Sheaf J (ModuleCat R))` as an opaque local instance at the *same* monoidal structure, killing that mismatch | **not sufficient** — still OOM-killed at 8 m 24 s |
| The concrete `MonoidalCategory (DerivedCategory …)` instance term matters | E13: replace it by a hypothesis ⇒ 18 s | **confirmed relevant** — it is the source of the proof-laden instance arguments |

## 12. Confirming the diagnosis, and the fix

Two experiments follow directly from §9–§10.

### 12.1 Remove the nested proofs from the value (control)

If the diagnosis is right, a value that contains no proofs at all leaves nothing for
`abstractNestedProofs` to lift, so the inferred type comes back *identical* to the
declared one and the conversion is free:

```lean
axiom E21ax (K : …) : Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K)

noncomputable def E21 (K : …) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := E21ax J I K
```

**5.2 s** — i.e. free. Exactly the same declared type as E1 (> 600 s); the only change is a
value with nothing to abstract. This is a control, not a fix (a real value will contain
proofs), but it pins the mechanism down.

### 12.2 Put an abstraction boundary on the diagram (the fix)

Name the diagram, so that the *declared type* contains a constant applied to small
arguments instead of an instance expression stuffed with proofs:

```lean
noncomputable def DerivedCategory.completionDiagram
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K

noncomputable def DerivedCategory.derivedCompletionCone (K : …) :
    Cone (DerivedCategory.completionDiagram J I K) := …
```

The monoidal instance — and every proof inside it — is now in the *body* of
`completionDiagram`, where it is checked once and never re-compared.

| # | Declaration | Wall time |
|---|---|---|
| E20 | `… : Cone (completionDiagram J I K) := sorry` | **17 s** (≈ the `skipKernelTC` cost of E2, i.e. kernel cost ≈ 0) |
| E22 | `completionDiagram` + `derivedCompletionCone := sorry` + `derivedComplete` + `derivedComplete_iff` + `derivedComplete_iff_isIso_lift` — **the entire remaining API** | **5.3 s** |
| E23 | `completionDiagram` + `derivedCompletionCone` with **the real intended term** `((tensorLeft K).mapCone ((singleFunctor _ 0).mapCone (Sheaf.quotPowCone J I))).extend ((ρ_ K).inv ≫ K ◁ εSingleFunctorZero _)` | **9.5 s** |

So the construction the file actually wants — not just a `sorry` — compiles in under ten
seconds once the diagram is named.

Downstream declarations then mention `completionDiagram J I K`; a
`lemma completionDiagram_eq : completionDiagram J I K = quotPowFunctor J I ⋙ tensorLeft K := rfl`
(or a `@[simp]` unfolding lemma) recovers the old form where a proof needs it, at exactly
one place instead of in every type.

## 13. Why the usual remedies were never going to work here

* **`abbrev` → `@[reducible] def`.** The two are genuinely different to the kernel (the
  reducibility hint changes, and the previous round of work in this repository was right
  about that). But it is a *reduction-strategy* knob, and it helps when the kernel is
  choosing to unfold a same-head application instead of comparing arguments. Here the
  kernel never gets a chance to make a bad unfolding choice at the top: the two sides it is
  given are already 36-way different, and every difference is a proof that must go through
  proof irrelevance. No hint on the outer head changes that.
* **`@[no_expose]`.** A barrier stops the kernel from *looking inside* a body. It cannot
  help when the expensive work is comparing two proposition *types* whose instance
  arguments are already different expressions — and if placed high enough to matter it
  would make the conversion fail rather than succeed (case B of §19 of the playbook).
* **Instance priorities.** Both sides are closed terms produced long before any new
  synthesis would happen; changing priorities cannot rewrite them (§20 of the playbook).
* **Sharing one instance with `letI`.** Tested in spirit by E12 (§11): aligning the
  braided/symmetric instance mismatch did not help, because that mismatch is not the one
  driving the descent.
* **Smaller terms.** §6: the term is 337 nodes.

The one remedy the playbook lists that *does* apply is the first one in its §1 list — **a
better abstraction boundary** — and §26's advice to ask what the *smallest expensive kernel
comparison* is. Here that comparison is "the same type, with proofs abstracted, against
itself", and the boundary removes it by keeping the proof-laden instance expression out of
the declared type altogether.

## 14. Recommendation

1. Introduce `DerivedCategory.completionDiagram J I K` (or whatever name fits the file's
   conventions) for `quotPowFunctor J I ⋙ tensorLeft K`, and state
   `derivedCompletionCone`, `derivedComplete`, `derivedComplete_iff` and
   `derivedComplete_iff_isIso_lift` in terms of it. Verified: 5.3 s for the whole block
   with `sorry`, 9.5 s with the real term.
2. As a general rule for this branch: **a declared type should not contain a
   `MonoidalCategory (DerivedCategory …)` instance expression in the open.** Any definition
   whose type does will pay the same cost, because the elaborated instance carries
   `HasSheafify`, `IsGrothendieckAbelian`, `MonoidalPreadditive` and
   `Qh.HasDerivedMonoidalCategory` proofs that `abstractNestedProofs` will rewrite on the
   value side. The `Aux` section at the top of `Defs.lean` already applies this discipline
   for `εSingleFunctorZero` ("keeps the definitional unfolding … out of the concrete
   sheaf-theoretic terms below, where checking it is prohibitively expensive") — the same
   discipline simply needs to be extended to the diagram.
3. If a future declaration of this shape is slow again, the quickest triage is the three
   lines of §8: `axiom` with the same type (does the type alone check?), the same
   expression as a value at type `Type _` (is the expression hard?), and the structural
   diff of `Kernel.check(value)` against the declared type (how many positions differ, and
   are they proofs?).

## 15. What is confirmed / ruled out / still open

```text
Confirmed:
  - the cost is 100% kernel, ~0% elaborator (E1/E2)
  - the cost is 100% in Kernel.isDefEq(inferred, declared); Kernel.check of both
    the type and the value is 3 ms (E18)
  - inferred ≠ declared because abstractNestedProofs rewrites the proofs inside the
    value but not inside the declared type; 36 differing positions, all proofs (E19)
  - naming the diagram removes the problem entirely, for `sorry` and for the real
    term (E20, E22, E23)
  - a proof-free value also removes it (E21) — control confirming the mechanism

Ruled out:
  - term-size / sharing blow-up (§6)
  - `Cone`, `⋙`, the `quotPow` tower (E5)
  - the braided-vs-symmetric instance mismatch as the driver (E12)
  - anything the elaborator-side transparency knobs can reach (§13)

Still open (not needed for the fix, but worth knowing):
  - the exact shape of the fan-out inside proof irrelevance. Pinning it down would need
    a kernel build instrumented at `type_checker::is_def_eq_core` / the proof-irrelevance
    branch, as in §23 of the playbook. The OOM in E12 suggests the descent is
    super-linear rather than merely deep.
  - whether Lean should skip `abstractNestedProofs` for the type argument of `sorryAx`
    (it already skips proofs that *contain* `sorry`); that would have made the `sorry`
    placeholder cheap, though not the real term.
```

## Appendix A. Reproduction

All experiments are self-contained files consisting of `Defs.lean` as committed, plus one
appended snippet, run as

```bash
lake env lean -D backward.isDefEq.respectTransparency=false -D maxSynthPendingDepth=3 \
              -D relaxedAutoImplicit=false -D warn.sorry=false <file>
```

(`backward.isDefEq.respectTransparency=false` comes from `lakefile.toml` and is
load-bearing; a bare `lake env lean` reports spurious transparency errors.)

Scripts and snippets live in this session's scratchpad
(`…/scratchpad/kernelperf/`): `run.sh`, `exp2.sh`, `e1.lean` … `e24.lean`,
`probe.lean`.

## Appendix B. The two probes

**B.1 Kernel step timing** (`e18.lean`). Note the file-handle logging: `IO.println` inside
`run_cmd` is captured by Lean's frontend and is not visible until the command returns,
which is exactly the case that never happens here.

```lean
def say18 (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk logPath IO.FS.Mode.append
  h.putStrLn s; h.flush

set_option debug.skipKernelTC true in
noncomputable def DCC (K : …) : Cone (quotPowFunctor J I ⋙ tensorLeft K) := sorry

set_option debug.skipKernelTC false in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let some (.defnInfo dv) := env.find? ``DCC | throwError "missing"
  -- 1. the declared type on its own
  say18 "-- Kernel.check(type)"; let t0 ← IO.monoMsNow
  let _ := (Kernel.check env default dv.type).toOption.isSome
  say18 s!"   {(← IO.monoMsNow) - t0} ms"
  -- 2. the value on its own
  say18 "-- Kernel.check(value)"; let t2 ← IO.monoMsNow
  let inf := (Kernel.check env default dv.value).toOption
  say18 s!"   {(← IO.monoMsNow) - t2} ms"
  -- 3. the conversion that the real `addDecl` performs
  if let some i := inf then
    say18 s!"-- structurally equal? {Expr.equal i dv.type}"
    let t4 ← IO.monoMsNow
    let r := (Kernel.isDefEq env default i dv.type).toOption
    say18 s!"-- isDefEq {r} in {(← IO.monoMsNow) - t4} ms"
```

**B.2 Structural diff of inferred vs declared** (`e19.lean`). This is the instrument that
actually answered the question; it needs no kernel build.

```lean
/-- minimal differing subterm pairs, with a path -/
partial def diffs (path : String) (a b : Expr) : Array (String × Expr × Expr) :=
  if a.equal b then #[]
  else match a, b with
  | .app .., .app .. =>
    let fa := a.getAppFn; let fb := b.getAppFn
    let aa := a.getAppArgs; let ab := b.getAppArgs
    if fa.equal fb && aa.size == ab.size then Id.run do
      let mut acc := #[]
      for h : i in [0:aa.size] do acc := acc ++ diffs s!"{path}.{i}" aa[i]! ab[i]!
      return acc
    else #[(path, a, b)]
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ =>
      diffs (path ++ ".dom") d₁ d₂ ++ diffs (path ++ ".bod") b₁ b₂
  | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ =>
      diffs (path ++ ".dom") d₁ d₂ ++ diffs (path ++ ".bod") b₁ b₂
  | .mdata _ x, y => diffs path x y
  | x, .mdata _ y => diffs path x y
  | .proj _ _ x, .proj _ _ y => diffs (path ++ ".p") x y
  | _, _ => #[(path, a, b)]
```

Run it on `Kernel.check(dv.value)` against `dv.type`. A declaration that is healthy
returns `#[]`.

**B.3 Subterm timing of `Kernel.check`** (`probe.lean`). Times `Kernel.check` on each
argument of an application and on every prefix `f a₀ … a_{k-1}`, then descends into the
dominant argument; the body is opened with `Meta.forallTelescope` so the free variables
live in a `LocalContext` that `Kernel.check` accepts. It is what established that
`Kernel.check` of the type is 3 ms; keep it for the next timeout, where the split may fall
on the other side.

## 16. Outcome of implementing the fix

`Defs.lean` now compiles. `lake build WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`
takes **7.9 s**, with the real term for `derivedCompletionCone` and with the whole API
(`derivedCompletionDiagram`, `derivedCompletionCone`, `derivedCompletionCone_pt`,
`derivedComplete`, `derivedComplete_iff`, `derivedComplete_iff_isIso_lift`) live.

Three things were learned while implementing it.

### 16.1 The control completes the argument

| # | Declaration | Wall time |
|---|---|---|
| E24 | the **real** term, stated over `quotPowFunctor J I ⋙ tensorLeft K` (no boundary) | **timeout at 7 min** |
| E23 | the **real** term, stated over `derivedCompletionDiagram J I K` | **9.5 s** |

So the win is the boundary, not the switch from `sorry` to a real value.

### 16.2 An unfolding lemma re-creates the problem

The obvious convenience lemma

```lean
lemma derivedCompletionDiagram_def (K : …) :
    derivedCompletionDiagram J I K = quotPowFunctor J I ⋙ tensorLeft K := rfl
```

**does not compile**: `(kernel) deterministic timeout` after 3 min 18 s. This is not a
surprise once §9 is understood, but it is worth stating because the lemma looks free:

* `derivedCompletionDiagram` is a `def`, so `abstractNestedProofs` ran on *its* body — the
  stored body contains `_proof_k` constants;
* the right-hand side of the lemma is elaborated afresh here, with the raw proofs;
* `rfl` therefore asks the kernel for exactly the 36-way proof-position reconciliation of
  §9, one delta step down.

(Incidentally this also shows where the boundary is safe and where it is not. Lemmas are
otherwise fine — `abstractNestedProofs` returns immediately when the value is itself a
proof — which is why `derivedCompletionCone_pt`, `derivedComplete_iff` and
`derivedComplete_iff_isIso_lift` cost nothing. It is puncturing the boundary *in a type*
that is expensive, not being a lemma.)

Consequence for the file: there is deliberately no unfolding lemma, and downstream
statements should be phrased in terms of `derivedCompletionDiagram`.

### 16.3 The `sorry`-ed flat-resolution instance was not needed

The working state carried

```lean
instance : Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} R) := sorry
```

but `#synth` finds `ModuleCat.hasFunctorialFlatResolution R` without it, and from there
`DerivedCategory.hasDerivedMonoidalCategory` and
`DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory` resolve as well. It has
been removed; `Defs.lean` now contains no `sorry` of its own. (`derivedCompletionCone` still
reports `sorryAx` in `#print axioms`, from
`GrothendieckTopology.monoidalClosed_sheaf_of_essentiallySmall` upstream — Day's reflection
theorem for sheaves is still to be formalised, as its own docstring says. That is
pre-existing and unrelated.)
