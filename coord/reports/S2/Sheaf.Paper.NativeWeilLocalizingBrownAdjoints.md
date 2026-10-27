## What changed

Proved both existing theorems in `Sheaf.Paper.NativeWeilLocalizingBrownAdjoints` without changing any public signature, definition, attribute or public import. Added proved private helpers for pullback constructibility, both integer Frobenius directions, representative independence, bounded forgetting, generator smallness, restriction of coproduct preservation and the ordinary solution-set Brown assembly. The same native chosen compactification is base-changed literally. The Weil restriction preserves coproducts by the natural forgetting comparison and reflection of colimits. Updated the existing node's proof to record these implementations.

Added private imports of the native induction comparison, derived coproduct existence, Mathlib triangulated Yoneda, additive Yoneda limits and Noetherian schemes. No other modules were edited. No consumer adaptation or definition-change record is needed.

Resumed rework validation on 2026-10-25: the original library path is present again and its quarantined path is absent. Compared the retained packet with that current source: all existing statements, definitions and public imports are preserved. The server single-file compile passes (21.9 seconds), using the native induction comparison delivery in the private overlay. The retained proof closes the two holes still present in the current library source; this is not a no-op restoration.


The resumed delivery attempt exited 75 after the built-in 50-minute priority-slot wait: all six priority delivery slots were occupied. No commit was pushed. The zero-hole compiling packet is retained for delivery; no launcher files or slot settings were changed.

## Proved and sorry left

Closed 2 of 2 holes: `AlgebraicGeometry.nativeWeil_localizing_hulls` and `AlgebraicGeometry.nativeWeil_localizing_brown_adjoints`, both attached to `lem-sf-native-weil-localizing-brown-adjoints`. Added zero holes and split off zero statements. The item contains no remaining `sorry`. These are proofs from the recorded dependency declarations; the native comparison, constructible realization and geometric compact-support theorem remain separate dependencies, some still admitted in their own modules.

## No longer needed

Removed direct private imports of `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`, `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`, `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory` and `Mathlib.CategoryTheory.Triangulated.Pretriangulated`. The K-injective and derived local-smallness instances are available through the retained interfaces and are still used.

The item does not use the colimit-computation assertion of `lem-kun-grothendieck-derived-coproducts`; it only needs existence, provided by the already proved `lem-grothendieck-derived-has-coproducts`. Replaced that direct DAG edge and removed its obsolete tool-use entry. This does not withdraw any source module or claim the colimit theorem is unnecessary to other consumers. All other original proof dependencies and the unit route remain. The additional induction-comparison clauses (integer exchange and kappa) are unnecessary here; its heart properties, actual comparison and triangulation clauses are used.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The hull theorem does not assume quasi-separatedness whereas the comparison interface requires it. It follows from local finite type over a field via local Noetherianity, and is proved locally in the proof. Base change and the realization's bundled Over object need explicit structural instances for Lean elaboration.

The generic Brown route uses no compactness and produces adjoints only on the stated hulls. Generator essential smallness comes from the realization's targetSmall field. The existing coproduct-existence node is used as a general tool in place of the stronger colimit-computation node; its theorem is already proved. The source framework's existing constructible-pullback lemma handles the inverse Frobenius direction, so no new mathematics or node is required.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
