## What changed

Proved `AlgebraicGeometry.exists_reduced_generic_fibre_map_core` in
`Sheaf.AlgebraicGeometry.ReducedGenericFibreMapCore`, retaining its current signature,
including S1's already-landed induced-algebra equality `haE`.

Constructed the scalar square, pullback lift, reduction lift, and fibre lift explicitly.
Added two proved private helpers: reducedness of an affine generic fibre, and dominance
of a compatible lift. The first reuses the existing private proof in
`Sheaf.AlgebraicGeometry.GenericFibreDominantField` (it cannot be imported by name).
The second uses the existing proved universal-homeomorphism API for purely inseparable
fields and surjective closed immersions. The lift's composite with the comparison
homeomorphism is the original dominant field point; density transfers back, and the
reduced generic fibre upgrades dominance to scheme-theoretic dominance.

Added proof-only imports of `Mathlib.AlgebraicGeometry.FunctionField`,
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`.
Updated the owned DAG node's proof, proof_deps, and proof_origin to this route.
The unit `sk-prop-normal-form` has no realized nodes or steps bypassed by this change.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_reduced_generic_fibre_map_core`
(node `lem-sbc-reduced-generic-fibre-field-embedding-core-map`).

Both private helpers, `reduced_generic_fibre` and
`reduced_generic_fibre_lift_dominant`, are fully proved.
No `sorry` remains in the item, and none is added elsewhere. No decomposition.
No data is chosen from an unproved existence statement.

## No longer needed

No pre-existing imports, nodes, or modules are removed. The former tensor-product
injectivity and nilradical-kernel calculation are not needed: universal homeomorphisms
and reducedness suffice. That former plan named no proof dependencies, so there are
no named modules to prune. No new intermediate modules are delivered.

## Where the brief, the DAG or earlier work was wrong

At the initial read the source allowed arbitrary `aE`, contrary to the node's intended
induced algebra structure. The current shared baseline incorporates S1's repair
(record `coord/changes/exists_reduced_generic_fibre_map_core.md`), including its caller
adaptation. This delivery follows that repaired signature exactly and requires no
further interface change or forced adaptation.

The shortest route uses topological dominance, the purely inseparable comparison
homeomorphism, and reducedness of the generic fibre. The original node's tensor and
reduction argument is replaced below the unit level. Searches: leanfinder for dominant
reduced purely inseparable base change, loogle for IsSchemeTheoreticallyDominant,
msearch grep plus repository/Mathlib rg. Existing API was sufficient.

## Second reading by T4

1. Compared the sole delivered module with the repository version. The existing
   public theorem signature is byte for byte identical, including S1's `haE`.
   There are no definition or public-import changes, no forced adaptations, and
   only `proof`, `proof_deps`, and `proof_origin` differ in the existing node.
   Verdict: unchanged interface.
2. Compiled the module locally with `lcompile.py`, without errors or warnings.
   A scratch copy with `#print axioms` for `reduced_generic_fibre`,
   `reduced_generic_fibre_lift_dominant`, and
   `AlgebraicGeometry.exists_reduced_generic_fibre_map_core` shows only
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There is no `sorry`, forbidden declaration, or hollow definition. The maps
   are constructed by pullback and closed-immersion lifts; no arbitrary witness
   is taken from an unproved existence theorem. Verdict: genuine proof, one
   original hole closed and zero holes added.
3. No statements are split off and no new nodes are added. Read both proved
   private helpers and the purely inseparable universal-homeomorphism instance.
   The identity extension and characteristic zero work without extra assumptions.
   The reducedness helper also allows an empty generic fibre, where localization
   is the zero ring. A dominant field point excludes an empty original fibre;
   the homeomorphism comparisons preserve this. Verdict: no new open obligations.
4. Searched the repository and Mathlib for generic-fibre reducedness and reviewed
   the existing private helper in `GenericFibreDominantField`; it is unavailable
   by name, so the local proved copy is justified. The three added imports provide
   respectively the fraction-field API, the reduced nilradical subscheme instance,
   and the purely inseparable universal-homeomorphism instance. The proof takes
   the direct topological route and uses no open Sheaf lemmas. All original public
   imports support the statement. The old node has no `proof_deps`, so there are
   no old dependencies or modules to prune. Read `sk-prop-normal-form.json`:
   its realized statement and both step lists are empty, and this below-unit
   construction bypasses none of its normal-form or slicing steps. Verdict: route
   and pruning report complete.
5. Matched the node's steps to the constructed lifts, comparison pullbacks,
   dominance transfer, and localization argument. The cited purely inseparable,
   surjective closed-immersion, and function-field nodes supply those ingredients.
   Found and repaired one citation mismatch: the localization-preserves-reduced
   node states localization at a prime, while Lean uses an arbitrary multiplicative
   set. Removed that `proof_deps` entry and wrote the elementary denominator proof
   explicitly in a separate step. The node's statement and Lean record stay
   unchanged; `proof_origin` describes the actual route. Verdict: DAG now agrees.

Second reading changed only the DAG localization citation and this report;
no Lean proof repair was needed. The removed citation was newly introduced by
this delivery, so it prunes no baseline node or module.
