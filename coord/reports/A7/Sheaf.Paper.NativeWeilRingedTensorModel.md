## What changed

Replaced the single hole in `Sheaf.Paper.NativeWeilRingedTensorModel` by an assembly
proof without changing its statement or public imports. Added a representative
data structure and four theorem modules. The native Hom comparison is proved for
the prescribed representative systems by rebasing the existing standard-sign
two-injective comparison. Native derived currying uses a private proof over an arbitrary abelian category,
then specializes its presented underived adjunction and product localization.
This avoids repeated reduction of the concrete native sheaf category. The main proof constructs the
closed adjunction from those bijections, proves its representative normalization,
and derives the required mate formula from evaluation compatibility by naturality
and the adjunction triangle identity.

The two remaining steps are geometric construction of the tensor presentation
and the evaluation square for already specified structures. They are separate,
strict parts of the argument: geometry constructs no native derived adjunction or
Hom comparison; evaluation constructs no tensor, symmetry, coherence or units.
The new presentation separates concrete tensor data from their equations in a
Prop structure: profiling showed that equality tests generated for one large
record consumed the compile budget. The fields and their meanings are preserved.
The main proof also keeps its large existential goal folded in a private
proposition during witness elimination, and uses generic proved helpers for
normalization transport and the adjunction-unit specialization. These avoid
expanding the concrete sheaf category during rewriting; no limits are raised.
No other existing module or definition is changed. The unit route is retained.

## Proved and sorry left

Original holes: 1, `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_ringed_tensor_model`.
Its body is now a complete assembly proof. This is a decomposition, not a complete
proof of the original mathematical result: two strictly smaller holes are added.
The delivery has two actual holes, both public theorem bodies exactly `:= by sorry`:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_geometry`,
  node `lem-sf-native-weil-tensor-geometry`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_evaluation`,
  node `lem-sf-native-weil-tensor-evaluation`.

The new theorems `native_hom_representative_exists` and
`native_weil_representative_currying` have complete proofs and no new holes.
`NativeTensorKFlat` and `NativeWeilTensorPresentation` are explicit definitions,
with no witness chosen from an unproved existence theorem and no hole in data.
The definition node is attached to the main `NativeWeilTensorPresentation`
structure; its statement also describes the K-flat definition and component
records/accessors in that module.
All private helpers are proved. Net syntactic change: one old hole closed, two
new holes added; no claim of net sorry reduction.

Edge cases checked: the acyclic-test condition includes the zero complex; all
uncurrying and evaluation formulas specialize to zero maps on zero inputs. The
row-sign conjugation is identity when n or p is zero, and the two signs cancel
also in characteristic two. The constructions impose no nonempty-site or
boundedness assumption.

Validation: all six modules compiled through the server lcompile.py checks.
The final main-module check passed in 9.9 seconds with no warnings, under default
heartbeats and the unchanged time limit. Profiling options were removed. Exact
comparison confirms the original theorem statement and public imports are
unchanged. The six node records have existing dependencies, correct proof-dependency
unions, and no path cycling back to a delivered node. Actual new hole count: two.

## No longer needed

No existing node or module is claimed globally pruned. The original three planned
dependencies (Frobenius action resolutions, ringed derived closed symmetric
monoidal structure, and ringed forget tensor descent) remain dependencies of the
geometric construction; their obligations have not been discarded. The main
module now uses the more precise presentation, Hom-comparison, currying and
evaluation lemmas. No existing public import is removed. No source-library
signature, attribute, public import or declaration is changed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan's ringed dependencies do not
directly supply a native tensor model normalized against arbitrary prescribed
Hom representatives in M. In particular the action-site statement alone is not
a ready-made native equivalence, and ringed tensor descent alone does not give
this prescribed Hom comparison. The present reduction makes those interfaces
explicit. The Hom comparison and derived currying portions are now actual Lean
proofs; the remaining geometric and evaluation arguments retain their original
sources and detailed proofs in words. Zero complexes and the empty-site case
need no new hypothesis. No target statement or unit realization was altered.

## New nodes

`def-sf-native-weil-tensor-presentation` defines the actual chain tensor,
acyclic-test K-flatness, underived adjunction, representative models and their
forgetting equations. It asserts no existence and contains no native derived
closed adjunction or Hom comparison.

`lem-sf-native-hom-representative-existence` proves normalized forgetting for
any prescribed native and ordinary Hom representative systems. It uses standard
sign models, generic K-injective descent and conjugation by row signs.

`lem-sf-native-weil-representative-currying` proves natural derived currying and
its homogeneous normalization from the presentation, by the generic chain
calculation and fully faithful precomposition with product localization. Its
node declares Grothendieck K-injective resolutions as a generic tool use; it
does not replace any step of the unit route.

`lem-sf-native-weil-tensor-geometry` leaves the original action-site tensor,
symmetry, coefficient units, tensor models and coherent forgetting construction
as one theorem, without the original native derived adjunction, Hom comparison
or mate requirement.

`lem-sf-native-weil-tensor-evaluation` leaves only the evaluation square for
specified normalized closed structures and specified comparisons. The component
and localization equations needed by its representative proof are fields of the
presentation. Its node declares native Hom precomposition under a source
quasi-isomorphism and K-injective target resolutions as generic tool uses. The
existing generic `evaluation_of_iso` transports the representative square to
arbitrary objects; the specialized ringed uncurrying theorem is a source for
the argument, rather than a native-category proof dependency. There are no change records because
no other existing module or node was changed.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
