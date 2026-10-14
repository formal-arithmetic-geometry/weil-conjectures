## What changed

Replaced the proof of `ModuleCat.exists_raw_transport` with a direct construction.
For `U := ModuleCat.restrictScalars eB.toRingHom`, take `E := U.mapDerivedCategory`.
The canonical `mapDerivedCategoryFactorsh` and `mapHomotopyCategoryFactors` isomorphisms,
whiskered by the quotient and `DerivedCategory.Qh`, compose to the required `q`.
The proof adds a proof-only import of
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. The supplied termwise
isomorphism is unused because the existential conclusion is unconditional.
The import visibility change is recorded in
`coord/changes/derived-extension-ring-equiv-raw-transport-import.md`.

## Proved and sorry left

The declaration `ModuleCat.exists_raw_transport` is proved. No `sorry` remains in the
item and no new declarations were added.

## No longer needed

No imports or nodes were removed. The hypotheses `L₀`, `L`, `ε₀`, `ε`, `h₀`, `h`, `eR`,
and `hRB`, and the input isomorphism `t`, are not needed by the formal conclusion, but
remain in the unchanged public statement.

## Where the brief, the DAG or earlier work was wrong

The planned derived-counit transport is stronger than needed for this statement: its
conclusion only asks for an existential restriction functor and localization
factorization, and the exact-functor API supplies these canonically without using the
counit data or compatibility isomorphism.

## Earlier second reading (a previous round; superseded)

The restriction functor is exact, so Mathlib's derived-category exact-functor construction
supplies `E`; the two factorization isomorphisms compose with the required orientation.
No target statement or unit route is changed.

## Second reading by K3

1. Compared the delivered module with the repository version byte-for-byte at all existing
   declarations. The public statement is unchanged, including the original quotient over `R` in
   the unused `π` let-binding. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles successfully and contains no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The proof constructs the exact
   restriction functor and composes the two Mathlib factorization isomorphisms. Verdict: pass.
3. The item has no split-off statements or new declarations. The existing node statement is
   unchanged and the proof origin and proof steps match the Lean proof. Verdict: pass.
4. The direct Mathlib route is shorter than the planned counit transport and uses only a
   proof-only import of `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`; no removable
   imports or proof dependencies were found. Verdict: pass.
5. The unit route is preserved: this lemma still realizes the transported localization
   factorization step, with the termwise isomorphism unused because the conclusion is
   unconditional. Verdict: pass.

Changed in this reading: restored the repository's original `π` statement after detecting that
the worker version had accidentally changed it from the quotient over `R` to the quotient over
`B`; adjusted only local proof types to avoid using that unused binding. No declarations or
nodes were added.
