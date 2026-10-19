## What changed

Proved both original theorems in `Sheaf.SixFunctors.FiniteDualityClosedComparison`, preserving every public signature, definition, public import and existing instance registration. Added proof imports of `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`, `WeilConjectures.SixFunctors.OpenClosed.Supported` and `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.

The proof constructs the sheaf-level closed right adjoint, derives it and uses uniqueness of right adjoints to establish the bounded-below lift. For invertibility, open/closed orthogonality shows that the pro-etale exceptional right adjoint kills every derived open direct image. Apply that triangulated functor to the transported etale support triangle: its third object vanishes, so the image of the etale counit is invertible. The specified transpose is a composite of this map, the mapped inverse canonical comparison and an invertible exceptional unit. The counit equation follows from inverse transposition. Naturality follows from the canonical Plus mate's naturality transported along arbitrary lifts, followed by injectivity of inverse transposition.

The private helpers implement parts of this node's argument, contain no holes and do not change the public interface. The local left-adjoint instance handles the named `Etale.rightDerivedLowerStar` wrapper. Backward elaboration transparency is relaxed locally for the definitionally equal wrappers; all terms are checked normally by Lean. The unused-variable linter is disabled locally for proofs whose signatures include hypotheses stronger than needed. All added options are scoped to individual declarations, preserving the original file-level commands.

Updated the existing node's proof, proof dependencies and proof origin to this argument. Removed its obsolete tool-use approvals while retaining the order of all others. No definitions or statements were repaired, no consumer adaptations were needed and no new modules or nodes were added.

## Proved and sorry left

Closed 2 of 2 original holes, both under node `lem-weil-finite-duality-closed-comparison`:

- `AlgebraicGeometry.isIso_finiteDualityClosedComparisonDelta_proof`.
- `AlgebraicGeometry.finiteDualityClosedComparison`.

There are zero `sorry` declarations left in the delivered module. Added zero holes; split off zero statements. This is a proof from existing library declarations, including the canonical Plus comparison and the etale support triangle. It is not a claim that all transitive dependencies are sorry-free.

The final module is validated by the required remote single-file compiler and delivery preflight.

## No longer needed

No original imports were removed: they are public imports used by the unchanged statements and constructions. Exploratory imports of `WeilConjectures.SixFunctors.OpenClosed.Vanishing` and `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory` were removed after compilation showed that the needed declarations are already publicly available through existing imports.

These planned proof dependencies were removed from this node:

- `def-weil-proper-morphism`: separatedness is retained in the statement but not needed by the proof.
- `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-noetherian-open-subscheme-noetherian`, `lem-weil-pbc-qcqs-morphism-permanence`: the existing signature already supplies all required qcqs instances.
- `lem-weil-pbc-comparison-pullback` (`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`): no open-unit comparison square is needed; the exceptional right adjoint kills every pro-etale open direct image, whatever its input.
- `lem-exc-proetale-support-triangle` (`Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle`), `lem-exc-proetale-derived-adjunction-triangle` (`Sheaf.AlgebraicGeometry.ProEtaleDerivedSupportAdjunction`), and `lem-exc-proetale-open-derived-image` (`Sheaf.AlgebraicGeometry.ProEtaleOpenDerivedImage`): applying the exceptional right adjoint to the etale triangle avoids a second support triangle and its normalization.
- `lem-exc-proetale-closed-essential-image` (`Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage`): the existing upstream closed exceptional adjunction and fully faithful derived pushforward suffice; no supported-image reconstruction is needed here.
- `lem-sf-triangle-morphism-iso`: no triangle morphism is constructed; instead, a distinguished triangle with zero third object makes its first arrow invertible.

The obsolete `tool_uses` entries corresponding to these dependencies were removed (except `def-weil-proper-morphism`, which had no entry). This records this proof's needs, not a claim that these modules are globally unreachable from all targets. In particular some remain transitive dependencies of the existing canonical-mate module.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement was found. The six-step plan is valid but longer than necessary below the unit level. The replacement retains the etale support triangle, the canonical comparison and the closed exceptional adjunction while avoiding TR3 completion, a second support triangle and an open-unit normalization square. Boundedness is proved directly from the derived sheaf adjunction rather than inferred from the support triangle. The unit record has no realized statement or step assigned to this node, and its route is unchanged.

Earlier saved work retained the complete proof with zero holes but had made the existing canonical-comparison instance local. Resuming review restored its original global registration, preserving availability to consumers. The server single-file compile passed; the final delivery checks validate the restored registration as well.

Resumption validation (2026-10-19): checked the retained proof against the current shared module and node. The only changed node fields are `proof`, `proof_deps`, `proof_origin` and removal of obsolete `tool_uses`. Repaired the saved parser errors by placing declaration-scoped options before their declaration docstrings. The corrected remote single-file compile passed in 11.1 seconds with zero warnings and zero holes. The delivery interface record is `coord/changes/FiniteDualityClosedComparisonProofInterface.md`.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
