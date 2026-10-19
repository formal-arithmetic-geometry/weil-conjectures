## What changed

Replaced the original `sorry` in
`AlgebraicGeometry.Scheme.finiteReductionReconstructionCompleted` by a complete Lean
proof. The normalized Koszul/Roos comparison gives an invertible completion map.
Adjunction naturality shows that finite reduction of this map composed with the
specified reconstruction counit is the identity, so that counit is invertible.
The same adjunction proves the requested naturality square. Product preservation
comes from a bounded strict-perfect tensor model and `finiteProjectiveTensorProducts`.
The existing statement, definitions, visibility and public imports are unchanged.

Added four modules, with one node each:

- `CompletedKoszulModelRoosComparison` states the separate, unit-preserving Koszul
  reconstruction comparison for arbitrary K-flat representatives and Roos triples.
- `CompletedReductionStrictPerfectModel` is proved from the existing
  `PerfectProjection.resolution_exists` and the tensor-model comparison. It converts
  the coefficient hypotheses field by field without changing the ring or ideal.
- `CompletedReductionTensorModelComparison` is proved by tensoring the given
  coefficient realization with K-flat test complexes, using the existing derived
  tensor structure and representative comparisons. The ordinary comparison and
  universal scalar-extension counit identify the other endpoint. Fully faithful
  whiskering through the K-flat localization descends the natural isomorphism.
- `CompletedReductionOrdinaryTensorComparison` is proved using change-of-rings
  cancellation, the left unitor, symmetry, and the degree-zero total-tensor
  comparison. Its private naturality helper is also proved.

The interrupted attempt's tensor-model proof is now validated, including the
explicit functor-identity rewrites. `lcompile.py --all` compiled all five delivered
modules cleanly: Koszul/Roos comparison 9.7 s, ordinary comparison 13.8 s, tensor
comparison 23.9 s, strict-perfect model 4.3 s, main item 6.3 s. No library build,
local Lake command, launcher edit, or compilation-limit increase was used.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finiteReductionReconstructionCompleted`
(node `lem-weil-pbc-finite-reduction-reconstruction`). The item has zero holes.

Three new intermediate theorems are proved, with no holes:

- `AlgebraicGeometry.Scheme.completedReductionStrictPerfectModel`
  (`lem-weil-pbc-completed-reduction-strict-perfect-model`).
- `AlgebraicGeometry.Scheme.completedReductionTensorModelComparison`
  (`lem-weil-pbc-completed-reduction-tensor-model-comparison`).
- `AlgebraicGeometry.Scheme.completedReductionOrdinaryTensorComparison`
  (`lem-weil-pbc-completed-reduction-ordinary-tensor-comparison`).

One added hole remains:
`AlgebraicGeometry.Scheme.completedKoszulModelRoosComparison`
(`lem-weil-pbc-completed-koszul-model-roos-comparison`). Its entire public theorem
proof is `:= by sorry`. This is the separate Koszul reconstruction result of
source order 1248, expressed for the completed-coefficient interface used here,
including its prescribed unit. It assumes no completeness and asserts no
finite-reduction counit isomorphism or product-preservation result. Its docstring
and node contain the source and full proof in words. No hole occurs in a definition,
private declaration, or partial delivered proof.

Counts: one original hole closed; one new hole added; net zero. This delivery is a
decomposition through a separate source result, not a claim that all mathematical
proof obligations in its import closure have been discharged. The open statement
was checked on empty generator lists, zero quotients, zero rings and empty schemes;
it imposes no proper-ideal, positive-rank or nonempty-site hypothesis.

## No longer needed

Removed these five direct proof-only imports from the original main module:

- `Sheaf.Paper.AdicCoefficientDatum`: already supplied by the public interfaces.
- `Sheaf.Paper.CompletedConstantSheafReduction`: used through the helper modules.
- `Sheaf.Paper.FiniteProjectiveTensorProducts`: still used, publicly supplied by
  `CompletedReductionStrictPerfectModel`; only the direct import is redundant.
- `Sheaf.Paper.KoszulReconstruction`: its representative comparison is isolated in
  the Koszul/Roos helper, which retains this proof-plan import.
- `Sheaf.Paper.PbcRoosTriangle`: the extra cohomology/Milnor sequence is unused.

`prop-weil-pbc-roos-triangle` / `Sheaf.Paper.PbcRoosTriangle` is no longer a separate
proof dependency of this item: `CompletedSequentialDerivedLimit` already includes
its distinguished Roos triangle. This does not assert that no other target needs
that module. No existing module is withdrawn, and no unit statement or unit proof
step is bypassed. The constant-sheaf, Koszul and finite-projective tensor results
remain needed transitively. The coefficient-resolution existence obligation is
supplied by the existing `PerfectProjection.resolution_exists`, rather than a new
unproved existence theorem.

## Where the brief, the DAG or earlier work was wrong

The older `koszulReconstruction` theorem does not directly specialize to this
interface. It takes `AdicCoefficientDatum A`, with A in the scheme universe,
`CompletedAdicModules`, and a total right-derived-limit functor. This item uses A
in the next universe, `ProEtaleAdicCoefficientDatum`, `adicDatumModules`, an explicit
Koszul fibre, and an arbitrary Roos triple. The coefficient and unit comparisons
must be retained; ignoring them would not identify the specified counit.

`finiteProjectiveTensorProducts` applies to a supplied bounded complex with
splittings. It does not identify that tensor functor with the chosen finite scalar
extension/restriction. The existing resolution-existence theorem supplies the
coefficient complex; the two proved tensor comparisons supply the functor identity.

The resumed session verified the retained work against current sources and first
ran the required dry run. It stopped at the split-off-hole gate, before compilation
or pushing. The old report's service failures and unverified tensor candidate are
superseded by the successful five-module compilation above. Continued searches
found the proved `noetherian_koszul_augmentation_pro_zero`, which supplies the
algebraic pro-zero step of Koszul reconstruction. Its use here still requires
transport to the actual completed sheaf tensors and normalized quotient units.
A scratch proof verifies the derived-adjunction normalization on homotopy
representatives; it is not counted as a delivered theorem. No scratch file is part
of the delivery.

LeanFinder, LeanSearch, Loogle and ripgrep searches of Mathlib and both library roots
found cancellation, localization and ordinary completion tools, but no theorem
already giving this completed-sheaf Roos comparison. Searches are recorded in the
new nodes and sandbox search log. No existing statement is weakened or disputed.

## New nodes

`lem-weil-pbc-completed-koszul-model-roos-comparison`, module
`Sheaf.Paper.CompletedKoszulModelRoosComparison`: the source's unit-preserving
Koszul reconstruction comparison on an arbitrary model, independent of
completeness. Open; this is the one remaining added hole.

`lem-weil-pbc-completed-reduction-strict-perfect-model`, module
`Sheaf.Paper.CompletedReductionStrictPerfectModel`: the source's bounded
finite-projective coefficient model, proved using the existing resolution theorem
and tensor comparison.

`lem-weil-pbc-completed-reduction-tensor-model-comparison`, module
`Sheaf.Paper.CompletedReductionTensorModelComparison`: the source's identification
of tensor with a specified perfect quotient model and derived finite scalar
reduction. Proved by the existing representative tensor comparisons and K-flat
localization.

`lem-weil-pbc-completed-reduction-ordinary-tensor-comparison`, module
`Sheaf.Paper.CompletedReductionOrdinaryTensorComparison`: the ordinary scalar
cancellation and degree-zero total-tensor comparison, proved before deriving.

The main node and all four new nodes record the implemented proof route and
actual dependencies. No change record is needed: existing statements, definitions,
public imports and visibility are unchanged, and no other existing module is edited.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
