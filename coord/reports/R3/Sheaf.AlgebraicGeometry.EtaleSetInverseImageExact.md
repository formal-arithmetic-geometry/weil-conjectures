## What changed

Proved `AlgebraicGeometry.etaleSetInverseImage_exact` in
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageExact`, preserving its entire signature.
Construct the Mathlib sheaf adjunction, install its left-adjoint instance, and assemble
continuity, an adjunction witness, finite-limit preservation, and finite-colimit preservation.
Finite-limit preservation uses the existing flat Kan-extension instance and left exact
sheafification, with `AB5OfSize.{u, u + 1}` for `Type (u + 1)` supplied by universe lowering.
Replaced the proof import of `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
with `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types`; public imports are unchanged.
Updated the item's DAG proof and dependency list to this direct set-valued route.

The source argument is [Stacks 03Q1(2)](https://stacks.math.columbia.edu/tag/03Q1),
which applies [00X6](https://stacks.math.columbia.edu/tag/00X6); finite-limit preservation
uses [00WJ](https://stacks.math.columbia.edu/tag/00WJ), and colimit preservation uses
[0038](https://stacks.math.columbia.edu/tag/0038).
Searches: LeanFinder for continuous flat sheaf pullback found the constructed adjunction
and generic finite-limit instances; Loogle confirmed `Adjunction.leftAdjoint_preservesColimits`.
Source searches found the large-category `preservesFiniteLimits_op_lan_of_flat` and the
already proved continuity/flatness instances. The initial proof using the algebraic-structures
result compiled; the shorter direct proof also compiled after removing that import.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.etaleSetInverseImage_exact`
(node `lem-weil-pbc-sets-etale-inverse-image-exact`). No holes remain in the item.
No holes added, no intermediate statements split off, and no definitions changed.
The final proof compiles without warnings. The delivery dry run also runs the axiom probe.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
and the proof dependency `lem-weil-pbc-etale-inverse-image-algebraic-structures`.
This item's proof therefore does not need the abelian/ring lifts, their operation-transport
and unit-compatibility results, or their modules
`Sheaf.AlgebraicGeometry.EtaleInverseImageAbelianLift` and
`Sheaf.AlgebraicGeometry.EtaleInverseImageRingLift`. They may still be needed elsewhere;
this is pruning of this item's route, not a claim that all other callers disappear.
Removed `def-weil-pbc-sites-and-cohomology` from proof dependencies: the theorem concludes
with the four explicit properties and has no additional site-morphism structure to construct.
Its statement dependencies remain unchanged.
An explicit proof import of `WeilConjectures.Mathlib.CategoryTheory.Functor.Flat` was tried
and removed after compilation confirmed it is already available through the retained public
source import. No other original imports were removed.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement found. The original plan routed set-valued finite-limit preservation
through the much larger theorem transporting abelian-group and ring structures. That route
is unnecessary: its set-valued finite-limit argument is already available directly as proved
instances. The proof follows the same continuity, left-exact inverse image, and left-adjoint
colimit argument of Stacks 03Q1(2)/00X6. The item is not a node realizing the statement or
steps of its unit `sk-thm-iff`, so this simplification does not bypass a unit-level step.
No new nodes, statement corrections, or change records.

## Second reading by R3

1. **Visible changes and statements.** I compared the delivered module with the repository
version. The theorem signature and all public imports are byte-for-byte unchanged; only the
proof-only import and proof body changed. The DAG edit changes only stage-3-owned proof fields.
Verdict: pass.

2. **Compilation and trust.** The delivered module compiles with `lcompile.py` without errors
or warnings. An axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for
`AlgebraicGeometry.etaleSetInverseImage_exact`; there are no `sorry`, `axiom`, `unsafe`,
`opaque`, `implemented_by`, or `extern` declarations. Verdict: pass.

3. **Statements and split-offs.** No statements were split off and no holes remain. The
existing Mathlib adjunction, the continuous étale base-change instance, representable
flatness, and the large-universe AB5 instance together imply exactly the four conjuncts in
the original theorem. No duplicate library or Mathlib statement was introduced. Verdict: pass.

4. **Route and pruning.** The proof takes the direct set-valued sheaf-pullback route:
`sheafAdjunctionContinuous`, the flat Kan-extension finite-limit instance, and left-adjoint
finite-colimit preservation. This is shorter than transporting algebraic and ring structures,
and the removed proof import and dependency are genuinely unused. The unit `sk-thm-iff` is
not bypassed because this item does not realize its statement or step. Verdict: pass.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` describe the
delivered proof and retain the source route; no new node or change record is required. Verdict:
pass.

Changed after reading: added this review record only; no Lean proof repair was necessary.
