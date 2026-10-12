## What changed

Proved `AlgebraicGeometry.etaleModuleRingIsoAdjunction` with its original signature.
The linearity criterion yields a natural hom equivalence by faithful uniqueness.
Mathlib pushforward comparisons construct the scalar-change equivalence, and the
ring adjunct identity identifies the transported right adjoint. Both requested
comparison formulas follow from these constructions. Updated the existing DAG
proof to describe the implemented argument; the unit route is unchanged.

Removed the unused public import of
`Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures` and replaced it with
the direct public import of `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
which supplies the types and adjunction in the statement. The old redundant private
import of that module was removed. No definitions or statements were changed.

## Proved and sorry left

Closed the single hole in `AlgebraicGeometry.etaleModuleRingIsoAdjunction`
(node `lem-weil-pbc-etale-module-ring-iso-adjunction`). No holes remain in the item,
and no holes or declarations were added elsewhere. This is a proof, not a decomposition.
The local file compiles cleanly with the default heartbeat limit. The constructions
choose only uniquely determined morphisms: faithfulness fixes each linear lift.

## No longer needed

Removed the import of `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
(node `lem-weil-pbc-etale-inverse-image-algebraic-structures`) from this module.
Its inverse-image algebraic lifting theorem and proof dependencies are not used:
the required ring adjunction, abelian adjunction and linearity criterion are inputs.
The direct-image and sheaf-of-modules definition nodes remain needed. No other
planned nodes are pruned; no claim is made that other import paths cease reaching
the removed module.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's claimed obstruction was not a mathematical obstruction.
The identity site functor has Mathlib's continuity instance, supplied explicitly
with the small Grothendieck topology. Explicit parameters on pushforwardComp
avoid expensive metavariable inference. The ring-isomorphism scalar equivalence
is constructed from pushforwardComp, pushforwardCongr and pushforwardId, so it
does not require an additional site equivalence theorem. The source construction
was checked in sites-modules.tex, change of rings and adjoint pull/push sections
(Tags 03D3 and 03D7), against the unchanged hypotheses.

## Second reading by E1

1. Compared the delivered module with `sheaf-dag`; the theorem signature is byte-for-byte unchanged. The DAG proof and proof dependencies match the implemented three-step transport argument. Verdict: pass.

2. Compiled the module with `lcompile.py`; it compiles cleanly. An axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry`, forbidden declarations, or overlong lines. Verdict: pass.

3. Checked the proof against the existing ring and abelian adjunction declarations and Mathlib pushforward comparisons; no new statements or split-off holes were introduced. The constructed hom equivalence uses faithful underlying sheaf functors, so its choices are uniquely determined. Verdict: pass.

4. The proof follows the unit route through the direct-image and sheaf-of-modules declarations. The redundant inverse-image algebraic-structures import is pruned; the direct definitions import is proof-only. Verdict: pass.

5. The node's `proof`, `proof_deps`, and `proof_origin` agree with the code, and the unit record remains unchanged. Verdict: pass.

Changed the import classification and added `coord/changes/EtaleModuleRingIsoAdjunction-imports.md`; no declarations or statements were changed.
