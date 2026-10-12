## What changed

Repaired D1 by removing both degree-restricted split modules and their new nodes. The item now proves `AlgebraicGeometry.Scheme.nonempty_sheafH_extDerivedIso` directly in every nonnegative degree, with its existing signature unchanged.

The proof constructs the termwise additive isomorphism from Hom out of the constant integer sheaf to global sections. It checks the differential and complex-morphism compatibility explicitly, transports to cohomology using Mathlib's left homology data, and computes Ext using the chosen injective resolution. Naturality is proved on cocycle representatives using `extMk_surjective` and `extMk_comp_mk₀`, then combined with the natural injective-resolution model for classical right derived functors. Finally it uses the existing bounded-below/unbounded derived-functor compatibility and the single-complex comparison. Every helper is private and fully proved; no mathematical comparison is postponed.

Added the proof-only imports `Mathlib.CategoryTheory.Abelian.Injective.Ext` and `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`. Existing public imports, definitions, and statements are unchanged. The preflight conservatively treats the additional scope commands for private helpers as an interface change; `coord/changes/etale-sheafH-comparison-proof-scopes.md` records these commands and their effect on users. The node's proof and dependencies now describe this completed injective-resolution argument. The unit's route is preserved.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.nonempty_sheafH_extDerivedIso`, the item's one original sorry. No sorry remains in the delivered module; none is added elsewhere. The positive and zero case declarations are removed, rather than retained as unresolved comparisons. The full proof applies without excluding degree zero, the zero sheaf, or the empty scheme.

Local compilation, the delivery axiom probe (only `propext`, `Classical.choice` and `Quot.sound` allowed), and server compilation passed. The delivery tool records the final preflight outcome.

## No longer needed

Removed the proof imports and sandbox modules `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparisonPositive` and `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparisonZero`. Retracted the corresponding proposed nodes `lem-weil-pbc-sheafH-ext-derived-comparison-positive` and `lem-weil-pbc-sheafH-ext-derived-comparison-zero`. No remaining declaration depends on them.

The original dependencies `def-weil-pbc-constant-sheaf`, `lem-weil-pbc-ext-via-injective-resolution` and `lem-sp-derived-functor-single-identification` are still used. No original planned dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

D1 is repaired: the earlier degree split merely specialized the full unresolved comparison, and its case analysis established none of the comparison mathematics. The earlier second-reading claims that this was a substantive reduction were incorrect and have been removed from this report. The replacement constructs the comparison and proves its naturality in Lean, with no split nodes and no remaining sorry.

The preflight scope-command detector classified the added namespace-local `open` and `variable` commands as changing what importers see. A change record documents this conservative classification; no existing public declaration or instance changes.

The earlier search conclusion that no complete packaged theorem was available did not prevent a proof: Mathlib's Ext/cohomology-class API and the source's right-derived-functor comparison provide both sides, and the termwise and naturality glue can be proved locally. The local literature checkout is absent on this machine; I read the cited Stacks statements at https://stacks.math.columbia.edu/tag/015A, https://stacks.math.columbia.edu/tag/05TI and https://stacks.math.columbia.edu/tag/06XR and checked the imported Lean APIs against the recorded argument. No source, statement, definition or unit-route correction was needed.

## Second reading by M1

1. Compared the delivered module with the repository version. The existing theorem
   signature and all existing declaration statements are byte-for-byte unchanged;
   only proof imports, private helpers, and the proof body differ. Verdict: pass.
2. Compiled the module locally with `lcompile.py`; it succeeds with no `sorry`,
   forbidden declarations, or compiler errors. The completed theorem uses only the
   permitted foundational axioms in the delivery probe. Verdict: pass.
3. No statement was split off in this delivery, so there are no new theorem claims
   to validate or search for upstream duplicates. The removed degree-specific modules
   were redundant specializations of the original target. Verdict: pass.
4. Checked the direct injective-resolution route, proof-only imports, and pruning.
   The route retains the unit's required derived-functor and Ext dependencies; the
   old positive/zero split imports and nodes are no longer needed. Verdict: pass.
5. Compared the node's `proof`, `proof_deps`, and `proof_origin` with the Lean proof;
   they describe the explicit sections, cohomology, Ext naturality, and derived
   comparison actually used. The unit `realized` route remains intact. Verdict: pass.

Changed during second reading: no Lean declarations or DAG statements; appended this
review record only.
