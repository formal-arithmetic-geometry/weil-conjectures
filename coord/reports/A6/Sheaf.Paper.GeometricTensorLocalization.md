## What changed

Replaced the proof hole of
`WeilConjectures.SemilinearSections.semilinearGeometryTensor` in
`Sheaf.Paper.GeometricTensorLocalization` by a complete proof from two smaller
statements. Private proved helpers construct the system tensor comparison and,
separately, every level comparison from the ordinary data. They use the existing
signed-total isomorphism and naturality API, cochain tensor rigidity, and
`tensorComparisonDescent`; cancelling invertible factors supplies the required
`TensorComparisonModel.derived` equation. Equality of the ordinary parts transfers
the pure-tensor normalization and the ordinary evaluation equation. The new
evaluation lemma supplies the remaining field of `GeometryTensor`.

Added proof-only imports of `Sheaf.Paper.GeometricOrdinaryTensor`,
`Sheaf.Paper.GeometricTensorEvaluation`,
`Sheaf.Paper.TensorPullbackRepresentativeDescent`,
`Sheaf.Algebra.Homology.CochainTensorModelRigidity`, and `import all` of
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback` for its signed-total naturality helpers.
The original structure, theorem signature, universes and public imports are unchanged.
No existing module besides the assigned item is changed. Updated only the proof-route
fields of its node, and added nodes for the two helper modules.

The final three-file compile passed: ordinary helper 4.7 s, evaluation helper 3.5 s,
and item 36.1 s. All delivered Lean files are below the 60-second limit.

## Proved and sorry left

Closed the one original syntactic hole, by a decomposition:
`WeilConjectures.SemilinearSections.semilinearGeometryTensor`.
Its proof from the two helper statements and the existing proved constructor is complete.
There are zero `sorry` bodies left in the item module.

Added two holes, each exactly the body of one named public theorem:

- `WeilConjectures.SemilinearSections.geometricOrdinaryTensor_exists`, node
  `lem-coef-semilinear-geometric-ordinary-tensor`, in
  `Sheaf.Paper.GeometricOrdinaryTensor`.
- `WeilConjectures.SemilinearSections.geometricTensorEvaluation`, node
  `lem-coef-semilinear-geometric-tensor-evaluation`, in
  `Sheaf.Paper.GeometricTensorEvaluation`.

Thus this delivery is a decomposition: one upper hole closed, two strictly smaller
obligations added, net holes closed minus added = -1, and no claim of an unconditional
proof of the original theorem. No definition contains a hole. The ordinary helper
has no derived tensor models as parameters and constructs no derived comparison.
The evaluation helper assumes the four already normalized comparisons and proves
only their compatibility; it does not construct any of those comparisons.

Edge cases checked in reading the statements: no nonempty-site or nonzero-ring
hypothesis is introduced; the zero complexes satisfy the preservation clauses;
level zero uses the supplied transition family without a predecessor; the same
independent object, morphism and coefficient universes are retained throughout.
The evaluation conclusion uses the specified geometryPullEvaluation and both
specified tensorEvaluation models, so it permits no sign twist or substitution of
an unrelated derived comparison. Equality is not inferred from derived evaluations.

## No longer needed

No imports removed, no modules withdrawn, and no whole module or node is claimed
pruned. The old direct proof-dependency list is replaced by the two new steps and
the signed-total comparison, representative descent and cochain-rigidity nodes.

`def-coef-semilinear-geometry-derived` is not directly used in the assembly proof;
its interface remains available through the unchanged ordinary realization import.
`def-coef-semilinear-system-models` remains a statement dependency.
`lem-weil-pbc-ringed-topos-kflat-pullback` is needed in the new lower obligations,
and `lem-weil-pbc-site-derived-tensor-descent` remains below the existing proved
constructor and rigidity machinery. They are not globally pruned.

## Where the brief, the DAG or earlier work was wrong

No false original statement or unit-route error found. The original plan was usable,
but its signed-total and localization steps can reuse existing generic APIs.
The general constructor in `ExactTensorModelConstructionIndependent` imports
`OpenOperationModels`, which reaches this item through `SemilinearDerivedSections`
and the geometric existence modules. Importing it here would create a source cycle.
`SemilinearTensorEvaluation` contains a private constructor proof with acyclic
imports, but that private theorem is absent from the available build artifact.
The item therefore includes its needed ordinary-to-derived proof as private helpers,
using the currently available lower APIs. No existing module is changed and no new
public constructor or constructor hole is added. Restriction to representatives is
proved fully faithful by cochain tensor rigidity, rather than repeating the older
resolution argument of that private constructor.

The available ordinary inverse-image tensor theorem
`RingedTopoiInverseImageTensorComparison.exists_inverseImageTensorComparison` is
stated with equal site-object, site-morphism and coefficient universes. It cannot
simply be applied at the independent universes of this item. The new ordinary
obligation records the same balanced-pairing construction with coefficient-sized
generalized sections, as well as the horizontal system assembly and K-flat clauses.
The existing exact-derived tensor-square result instead assumes its canonical
monoidal structures; it does not directly prove compatibility for the independently
specified tensor models in this interface.

## New nodes

`lem-coef-semilinear-geometric-ordinary-tensor` is the ordinary portion of steps 1--2
of the assigned plan: natural pure-tensor comparisons on levels and systems, the
ordinary evaluation square, and preservation of flat-term K-flat complexes. Its
source is Stacks 03EL and 0G7E, applied to the normalized ordinary realization of
Zheng Construction 4.1. It constructs no derived tensor data.

`lem-coef-semilinear-geometric-tensor-evaluation` is only the coherence portion of
step 3: total-summand compatibility from the given ordinary square, substitution
of the four representative equations, and faithful restriction to resolving pairs.
Its source is the signed-total construction in Stacks 07A4 and localization in
06YY. It assumes the comparisons and their models, rather than restating their
existence. Both nodes inherit the item's chapter and unit and carry complete
statements, proof plans, source citations, Lean attachments and three search kinds.
No change record is needed because no existing interface is changed.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
