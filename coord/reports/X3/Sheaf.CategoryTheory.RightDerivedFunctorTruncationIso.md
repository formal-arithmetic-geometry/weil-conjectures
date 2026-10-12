## What changed

Closed `CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι` using the existing
`DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app` theorem and the established
negative-vanishing theorem for `rightDerivedFunctorPlus`. Added the required PlusDevissage import.

## Proved and sorry left

Proved: `CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι`.

Sorry left: `CategoryTheory.Functor.mono_homologyFunctor_rightDerivedFunctorPlus_map` and
`CategoryTheory.Functor.epi_homologyFunctor_rightDerivedFunctorPlus_map`.

## No longer needed

No DAG nodes were bypassed beyond the direct PlusDevissage route for the truncation corollary.
The proof does not use the cone/long-exact-sequence dependencies listed for the mono and epi helpers.

## Where the brief, the DAG or earlier work was wrong

The existing source already provides a general bounded-below truncation criterion for triangulated
functors preserving the lower cohomological bound, so the planned bespoke cone proof is unnecessary
for the truncation corollary. The mono and epi helper proofs still require the planned cone argument.

## Second reading by X3

1. Compared the delivered module with the repository version. Existing declaration signatures and definitions are unchanged; the delivery adds only the proof of `isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι`, removes the unused proof-only `Sheaf.CategoryTheory.KInjectiveBridge` import, and adds the existing `PlusDevissage` import.
2. Compiled the module with `lcompile.py`; it compiles cleanly. The only remaining sorries are the two named mono/epi split declarations and the existing truncation-independent helper holes are absent. No forbidden declarations or hollow definitions were introduced.
3. The truncation statement is unchanged and true. Its proof uses the existing `DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app` criterion and the established negative-vanishing theorem; no new statement was added and no Mathlib or library duplicate was introduced.
4. The direct PlusDevissage route is shorter than the planned cone argument and preserves the unit route. The unused K-injective bridge import was pruned; all remaining imports are needed for signatures or the proof. The node proof and `proof_deps` were updated to match the two existing split helpers and the negative-vanishing theorem.
5. The DAG node's proof, dependencies, and origin now agree with the Lean proof. No unit realization was changed.

Changed: proved `CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι`, pruned `Sheaf.CategoryTheory.KInjectiveBridge`, added the proof-only `WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage` import, and synchronized the existing truncation-isomorphism node.
