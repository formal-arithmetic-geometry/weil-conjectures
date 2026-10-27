## What changed

The item keeps its theorem statement and locality-isomorphism construction unchanged.
Validation: the complete parent proof compiled cleanly on the server (35.8 seconds),
including both private categorical helpers and the final specialization. The new definition
and projection-square statement also compiled cleanly (46.2 and 45.3 seconds). The final
import-only cleanup passed lcompile --all for all three modules, with no errors or warnings.
Its proof establishes the composite-counit clause by Mathlib conjugateEquiv_counit and
Adjunction.comp_counit_app. A private, proved categorical calculation transposes both
maps, uses counit naturality and the sum-extension fold identity, and reduces the tensor
clause to the normalized inverse-projection square.

TensorMateInverseProjection packages the exact inverse-projection composite already
written in the item as a natural transformation in the source object. This is a real
construction from the existing inverse projection, signed symmetries and exact-pullback
comparison, with no new choice or theorem supplying data.

EtalePrecompProjection states the geometric square from step 3 of the original plan.
It contains no exceptional right adjoints, no dualizing objects and no tensor mates.
The item uses it for every source object, and combines it with the independent fold-counit
identity from isIso_etaleSumExtensionTensorComparison. This is a decomposition into a
strict part of the argument, with a complete categorical assembly proof.

## Proved and sorry left

Original hole: AlgebraicGeometry.Etale.tensorMateEtalePrecomp
(lem-asd-tensor-mate-etale-precomp). Its complete proof is supplied, conditional on the
new projection-square theorem and the existing dependencies. The composite-counit clause
is proved without a new hole. The private conjugate_composite_counit and
tensor_mate_calculation are proved without sorry.

One hole is added: AlgebraicGeometry.Etale.etalePrecompProjection
(lem-asd-etale-precomp-projection). Its entire proof is exactly `by sorry`, with its
source and complete proof in words in the docstring and node. No holes remain in the item.
No holes are added in definitions. Counts: one original hole closed, one split off;
net zero holes closed. This is a decomposition, not a claim of a net proof gain.

## No longer needed

Removed proof-only imports (the new projection-square module supplies the assembly API):

- Sheaf.AlgebraicGeometry.ShriekTensorComposition
- Sheaf.AlgebraicGeometry.ProperProjectionFormula
- Mathlib.AlgebraicGeometry.Morphisms.Proper
- Mathlib.AlgebraicGeometry.Noetherian
- Mathlib.Topology.Defs.Filter
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
- WeilConjectures.Compactification.NagataCompactification
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

No unit route is bypassed and no module is withdrawn. The original geometric steps are
retained by the new projection-square node: compact-support projection composition and
comparison, graph-normalized support/projection compatibility, and etale normalization.
The proper and open projection invertibility arguments need not be repeated: the item
already uses the proved isIso_projectionMap_of_finite for the whole projection.

All seven old top-level tool_uses approvals are removed from the item: the open projection,
finite-type-over-Noetherian, proper projection, shriek composition, support-map compatibility,
general ringed-topos tensor pullback, and unbounded compact-support comparisons. The geometric
ones needed by the new square remain explicitly named in that node's proof_deps; this is not
an assertion that those modules are globally unused. The parent now takes the combined square.

The general ringed-topos tensor-pullback theorem is not used directly by the new assembly:
the concrete etale tensor-pullback comparison and its fold identity already occur in
EtaleSumExtensionTensor. Its public API remains unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or source discrepancy was found. The original seven-step proof is
mathematically sound. Its step 3 combines existing projection-composition and graph-support
statements with substantial normalization and tensor-convention transport; no existing
single declaration states that combined square. That precise interface is the remaining
new theorem. It is not the item under another name: the exceptional-adjunction and
mate/counit arguments are fully proved separately in the item.

Edge cases checked mathematically: u is identity, the empty source, K or M is zero,
and the zero coefficient ring. Each square reduces to the corresponding naturality or
zero-map equation. No nonempty, nonzero, smoothness, boundedness or Tor-amplitude assumption
is introduced. New statements keep all universes and use ordinary unbounded categories.

Searches used LeanFinder, Loogle, LeanSearch and local rg. Mathlib supplied the conjugate
counit calculation but no geometric compact-support square. Existing ShriekTensorComposition
and EtaleSupportMapCompatibility are reused in the remaining step's proof plan.

## New nodes

- def-asd-tensor-mate-inverse-projection: owns the constructed natural transformation in
  Sheaf.SmoothPurity.TensorMateInverseProjection; no sorry.
- lem-asd-etale-precomp-projection: owns the coefficient-first normalized projection
  square in Sheaf.SmoothPurity.EtalePrecompProjection; one sorry, strictly the geometric
  part of original step 3.

No existing definition, public signature or source-library declaration is changed, so no
change record or forced consumer adaptation is required.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
