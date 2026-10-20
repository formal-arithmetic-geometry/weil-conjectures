## What changed

Replaced the sole `sorry` of `Sheaf.Paper.FiniteReductionReconstructionCompleted` by a
complete adjunction argument and product-preservation argument. The counit is shown to
be the inverse of reduced completion using the evaluation identity. Its naturality is
proved from the two naturality laws of the adjunction hom equivalence. Product
preservation is transported along a natural isomorphism, so the map proved invertible
is the specified canonical comparison.

The two mathematical comparisons needed by this proof are stated separately, with
complete source proofs in words and new DAG nodes. The first compares the explicit
Koszul fibre with any specified quotient Roos triple, preserving evaluations and the
normalized adjunction unit, without assuming completeness. The second realizes finite
reduction/restriction as tensor with a bounded finite-projective sheaf complex. These
are separate source results, rather than renamed copies of the assigned statement.
Their proofs remain unfinished; the main result is therefore a decomposition.

Also filled ten existing supporting holes in the unclaimed module
`Sheaf.Paper.AdicCoefficientDatumCompleted`. These prove the scalar map's limit property,
exact scalar restriction, existence of K-flat models, the normalized ordinary scalar
adjunction and its unit, the canonical model reduction
comparison, the strict tower laws and additivity, and the degreewise identity restriction
comparison. No existing signature, definition body, public import or target was changed.
The ordinary adjunction uses the existing sheafified
tensor/restriction adjunction, and sectionwise equality proves uniqueness of its unit.

Validation: `lcompile.py --all` compiled all four delivered Lean modules together.
The supporting module compiled in 37.7 seconds; the other modules took 3.4–5.2 seconds.
The delivery dry run passed. Its auxiliary-module axiom probe exceeded 60 seconds;
the delivery tool records that the merge reruns this probe. No complete axiom audit
of that auxiliary module is claimed here.

## Proved and sorry left

Assigned module: one original hole replaced by a compiling proof, with zero holes left
in that module:

- `AlgebraicGeometry.Scheme.finiteReductionReconstructionCompleted`.

This closes an upper hole by introducing two lower holes and is a decomposition,
not a claim of an axiom-free reconstruction theorem. The two added holes are:

- `AlgebraicGeometry.Scheme.completedKoszulRoosEvaluation` —
  `lem-weil-pbc-completed-koszul-roos-evaluation`.
- `AlgebraicGeometry.Scheme.completedFiniteQuotientTensorPresentation` —
  `lem-weil-pbc-completed-finite-quotient-tensor-presentation`.

Existing holes closed in `Sheaf.Paper.AdicCoefficientDatumCompleted`:

- `AlgebraicGeometry.Scheme.adicDatumScalar_exists`.
- `AlgebraicGeometry.Scheme.adicDatumOrdinaryUnit_exists`.
- `AlgebraicGeometry.Scheme.adicDatumOrdinaryAdjunction_exists`.
- `AlgebraicGeometry.Scheme.adicDatumModel_exists`.
- `AlgebraicGeometry.Scheme.adicDatumRestriction_exact`.
- `AlgebraicGeometry.Scheme.adicDatumOrdinaryTransition_id`.
- `AlgebraicGeometry.Scheme.adicDatumOrdinaryTransition_comp`.
- `AlgebraicGeometry.Scheme.adicDatumOrdinaryTower_additive`.
- `AlgebraicGeometry.Scheme.adicDatumModelComplexRestrictionIso_exists`.
- `AlgebraicGeometry.Scheme.adicDatumModelReductionComparison_isIso`.

The following ten pre-existing holes in that supporting module are unchanged. Their
docstrings carry `def-weil-pbc-adic-coefficient-datum`:

- `AlgebraicGeometry.Scheme.adicDatumQuotients_exists`.
- `AlgebraicGeometry.Scheme.adicDatumFiniteCoefficientIso_exists`.
- `AlgebraicGeometry.Scheme.adicDatumFiniteCoefficientIso_natural`.
- `AlgebraicGeometry.Scheme.adicDatumAdjunction_exists`.
- `AlgebraicGeometry.Scheme.adicDatumComplexCounit_isIso`.
- `AlgebraicGeometry.Scheme.adicDatumOrdinaryTransition_exists`.
- `AlgebraicGeometry.Scheme.adicDatumTowerDerived_exists`.
- `AlgebraicGeometry.Scheme.adicDatumBalance_exists`.
- `AlgebraicGeometry.Scheme.adicDatumExtension_kflat`.
- `AlgebraicGeometry.Scheme.adicDatumBalance_cocycle`.

Packet counts: eleven existing holes closed, two added, twelve remaining in delivered
files. The ten supporting closures add no new holes. The ledger, rather than these
file counts, determines the net in the pinned targets' import closure.

Edge cases checked mathematically: empty generator lists and I=0 give the identity
completion and tensor with the unit. I=A and zero quotients give the zero coefficient
category and zero finite-projective representative. No flatness of the finite quotient
or completeness of A is used. An arbitrary prescribed Roos triple is handled by a
triangle comparison, without choosing functorial triangle vertices.

## No longer needed

Removed direct proof imports from the assigned module:

- `Sheaf.Paper.AdicCoefficientDatum`: the statement imports already provide the actual
  completed datum used here; the older coefficient interface is not used by this proof.
- `Sheaf.Paper.CompletedConstantSheafReduction`: now used by the separate finite-projective
  presentation and Koszul comparison, not by the combining proof.
- `Sheaf.Paper.KoszulReconstruction`: its declared reconstruction theorem uses the older
  coefficient universe and completed-ring construction. The new evaluation comparison
  records the needed completed-interface result explicitly.
- `Sheaf.Paper.PbcRoosTriangle`: the input `CompletedSequentialDerivedLimit` already
  supplies the distinguished Roos triangle; the combining proof needs no further
  construction of it.

Correspondingly, the assigned node no longer directly uses
`prop-weil-pbc-koszul-reconstruction`, `prop-weil-pbc-roos-triangle`, or
`lem-weil-pbc-completed-constant-sheaf-reduction`. The constant-reduction node remains
needed by both new comparisons. The Koszul reconstruction argument itself is retained:
the new comparison uses the Noetherian augmentation and strict-tower derived-limit
inputs. `lem-weil-pbc-finite-projective-tensor-products` remains directly used.

No module is withdrawn and no global pruning is claimed. In particular, no upstream
source declaration, proof, attribute or public import is removed. Unit and chapter
records are unchanged.

## Where the brief, the DAG or earlier work was wrong

The stated proof dependencies exist, but their formal interfaces do not directly give
the current completed-datum comparisons. `koszulReconstruction` quantifies over an
`AdicCoefficientDatum` with coefficients in the scheme's lower universe and uses its
continuous-functions completed ring. The assigned theorem uses
`ProEtaleAdicCoefficientDatum`, coefficients one universe higher, and the actual limit
of constant finite quotient sheaves. An abstract reconstruction isomorphism alone also
does not supply the required compatibility with each evaluation and the chosen scalar
adjunction. This packet states that compatibility explicitly rather than identifying
the two interfaces by an unsupported definitional equality.

Similarly, the completed-constant reduction theorem constructs a finite-projective
representative, and finite-projective tensor preservation concerns a localization lift
of tensor with that representative. Their declarations do not already identify this
lift with `adicDatumReductionUnderlying`; the second new statement supplies precisely
that functor comparison.

A dependency audit also found the pre-existing cycle
`lem-pc-ring-hom-extension-differential` →
`lem-pc-ring-hom-extension-differential-adjacent` →
`lem-pc-ring-hom-extension-differential`. Both nodes were already reachable from the
assigned node before this packet. Neither new comparison node lies on a cycle.
This is reported for maintainer follow-up; no unrelated DAG repair is included.

The auxiliary module was unclaimed in the shared claim records at both checks.
Its public interfaces and definition bodies are preserved; the additional edits
complete existing supporting proofs.

No statement is disputed. No target or source-library exception is requested.
No maintainer `tool_uses` approvals were edited.

## New nodes

`lem-weil-pbc-completed-koszul-roos-evaluation` states the evaluation-preserving
comparison before completeness. Its source is the Koszul reconstruction paragraph of
the current finite-reduction proof. Its proof uses the existing Noetherian augmentation
with pro-zero cone, exact constant/flat completed scalar extension, strict-tower derived
limits and the normalized scalar adjunction. It includes the comparison for any input
Roos triple. This is the missing lower reconstruction result; it contains neither the
finite-reduction counit assertion nor the product-preservation assertion.

`lem-weil-pbc-completed-finite-quotient-tensor-presentation` states a bounded
finite-projective presentation and natural functor isomorphism for a single finite
quotient, independently of any complete object or inverse tower. Its source is the
bounded representative and tensor paragraph of the current finite-reduction proof.
The completed-constant reduction theorem supplies the representative, and scalar tensor
cancellation and universal derived comparisons give the functor isomorphism.

Both node files record LeanSearch, LeanFinder/Loogle and Mathlib source searches.
Their declaration signatures are copied verbatim. The assigned node's proof,
`proof_deps` and `proof_origin` follow the combining Lean proof. There is no definition
or statement change record because all existing signatures and definition data are
preserved; the supporting module changes only theorem proofs, proved private helpers,
private proof imports and scoped elaboration options.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
