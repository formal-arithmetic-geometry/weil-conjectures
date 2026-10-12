## What changed

Added `Sheaf.CategoryTheory.Sites.OverPullbackAdjunctionMono`, whose intermediate theorem packages the extension-by-zero adjunction and its preservation of monomorphisms. The target module now applies Mathlib's adjunction criterion for preservation of injectives.

## Proved and sorry left

The target theorem `CategoryTheory.overPullback_preservesInjectiveObjects` is proved by a complete application of `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`. The new intermediate theorem `CategoryTheory.overPullback_extensionByZero` remains `sorry` and is recorded by node `new-over-pullback-adjunction-mono`.

## No longer needed

No imports from the original target module were removed. The abandoned experimental monomorphism-only module was not retained and has no DAG node.

## Where the brief, the DAG or earlier work was wrong

The original proof plan assumes a direct sheaf-pullback construction for arbitrary Grothendieck topologies, but Mathlib's explicit `sheafPullback` requires left Kan extension instances unavailable under the target's hypotheses. The intermediate theorem states the construction abstractly so the injectivity argument compiles without adding assumptions.

## New nodes

`new-over-pullback-adjunction-mono`: extension-by-zero left adjunction preserving monomorphisms, stated in `Sheaf.CategoryTheory.Sites.OverPullbackAdjunctionMono`.

## Second reading by P3

1. I compared `OverPullbackPreservesInjectives.lean` with the repository version. The target
   signature and documentation are unchanged; only its proof and a private import changed.
   The intermediate declaration's JSON now records the category and both `HasSheafify`
   assumptions appearing in Lean. Verdict: pass.
2. I compiled both delivered modules with `lcompile.py --all`; they compile without errors.
   The target has no `sorry`; the sole remaining `sorry` is the named public theorem
   `CategoryTheory.overPullback_extensionByZero`, with source, proof description, and DAG node.
   No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. The intermediate statement is the exact adjunction-and-monomorphism package consumed by the
   target and is strictly smaller than the target. It is not present in the repository or
   Mathlib under another name (checked with `rg`). Verdict: pass.
4. The target follows Mathlib's
   `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`; no old proof
   dependency was removed. Verdict: pass.
5. The target node uses `new-over-pullback-adjunction-mono`, and the new node's Lean statement,
   module, declaration, source, and proof metadata agree. The unit route retains the
   extension-by-zero step. Verdict: pass.

I corrected the new node's statement metadata to include the explicit Lean assumptions and
recorded this second reading.
