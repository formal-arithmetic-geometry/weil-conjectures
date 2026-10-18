## What changed

Proved the sole theorem of `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint` with its signature and visibility unchanged. A proved private helper constructs the underived adjunction for every ring A, without requiring finiteness or commutativity. It forms the actual kernel of the open restriction unit, identifies it with a closed pushforward by the existing supported-sheaf equivalence, and proves the Hom bijection and its naturality. Exactness follows from the two adjunctions. The existing unbounded derived-adjunction theorem and exact-derived comparison finish the assigned result.

Added proof imports of `WeilConjectures.SixFunctors.OpenClosed.Supported`, `WeilConjectures.SixFunctors.OpenClosed.Vanishing`, and `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`. Updated the item node's proof, proof_deps and proof_origin to describe this implementation. No definitions, existing signatures, public imports or consumers were changed.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion` (node `lem-exc-closed-ambient`). Added 0 holes; no sorry remains in the delivered module. The helper `closedLowerStar_isLeftAdjoint` is fully proved. This is a proof, not a decomposition.

The complete file compiled cleanly on the server (7.8 seconds), and compiled again after removing unused proof imports. `#print axioms` for the assigned theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`; no sorry axiom is reachable. All three added proof imports pass import_direction.py. The theorem covers empty closed subschemes, the whole ambient scheme, nonreduced closed subschemes and arbitrary unbounded complexes: the kernel and adjunction argument introduces no excluded case.

## No longer needed

Removed direct proof imports `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` and `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`. The latter's particular theorem requires commutative coefficients; the generic Grothendieck K-injective machinery already available through the derived API handles arbitrary rings.

Removed proof dependencies `def-weil-pbc-constant-sheaf`, `def-weil-sheaf-of-modules-category`, `lemma-openclosed-stalk-lowerstar`, `prop-weil-pbc-geometric-stalks-exact`, `lemma-weil-pbc-geometric-stalk-conservative`, `lem-weil-pbc-open-immersion-etale`, `def-weil-size-convention`, `lem-weil-pbc-ring-sheaves-grothendieck`, `lem-weil-pbc-kinjective-total-derived`, and `lem-weil-pbc-kinjective-hom-derived`. The ringed-site module construction and scalar-action gluing are unnecessary because the existing support theorem accepts ModuleCat A directly. The separate stalk proof of exactness is unnecessary because the constructed underived adjunction proves finite-colimit preservation. Generic K-injective and derived-adjunction APIs replace the bespoke existence and Hom calculation. Explicit Lean universes supply the size convention.

Removed obsolete top-level tool_uses approvals for `lemma-openclosed-stalk-lowerstar`, `prop-weil-pbc-geometric-stalks-exact`, `lemma-weil-pbc-geometric-stalk-conservative`, `lem-weil-pbc-ring-sheaves-grothendieck`, `lem-weil-pbc-kinjective-total-derived`, `lem-weil-pbc-kinjective-hom-derived`. Remaining approvals retain their original order.

The proof does not import `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`: its supported-sheaf conclusion (node `lem-kun-04ca`, retained as the mathematical support-equivalence dependency) is used through the stronger, already proved arbitrary-coefficient API in `WeilConjectures.SixFunctors.OpenClosed.Supported` and `UpperLowerStar.ClosedImmersion`. No claim is made that these shared nodes or their transitive imports become globally unreachable.

The unit's realized statement/steps lists are empty for this node, and the proof retains both blueprint paragraphs: supported kernel adjunction followed by unbounded K-injective derivation. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's scalar-action extension and separate stalk exactness proof are valid but unnecessary given the stronger arbitrary-coefficient support API now in the source library. Its long derived Hom argument is already implemented by `Adjunction.mapDerivedCategoryRightDerivedAdjunction`. No mathematical statement was disputed or changed. One compile request exhausted the script's busy/unreachable-server retry budget; rerunning succeeded, so this did not block the work.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
