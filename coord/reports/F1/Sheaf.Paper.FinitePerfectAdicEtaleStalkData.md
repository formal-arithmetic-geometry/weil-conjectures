## What changed

Replaced the single hole in `Sheaf.Paper.FinitePerfectAdicEtaleStalkData` by a complete
assembly proof. Its theorem and `FinitePerfectAdicEtaleStalkData` structure have their
original signatures. Three private proved helpers pull back model sieves, construct
connected open neighborhoods in locally Noetherian schemes, and build a point-indexed
connected etale model cover. The cover is empty when X is empty.

The proof chooses single-level descended data, uses the proved two-level refinement
argument to obtain scalar-extension isomorphisms, and composes a supplied stalk
trivialization with the recorded algebraic fibre comparison to produce transport.
There is no choice of a compatible family of trivializations or inverse-limit argument.

Added `FinitePerfectAdicEtaleLevelData`, `FinitePerfectAdicEtaleLevelDescent`,
`FinitePerfectAdicConstantModelsReduction`, and `FinitePerfectAdicStalkReduction` under
`Sheaf.Paper`. The last module proves the pairwise reduction by applying existing
finite-ring derived local constancy to both levels, pulling both models to an
intersection cover, selecting a member above the chosen point, applying both transport
maps there, and using constant-model scalar balancing.

The concrete exact functor `finitePerfectAdicEtaleStalk` moved verbatim to the data
module and is publicly reexported. The new algebraic universe lift is a real termwise
construction, with no existential witness chosen in a definition. The relocation
record is `coord/changes/finite-perfect-adic-etale-stalk-location.md`. No adopted source
module is changed. All original public imports of the item remain; its proof imports
are private.

Validation: the five delivery modules compiled in 10.4–17.4 seconds each, and the
unchanged direct importer `Sheaf.Paper.FinitePerfectAdicStalkModels` compiled in 11.6
seconds against the packet. Its check-only copy was then removed. The only warning was
an unused existential binder in a private helper; it was renamed `_v` before delivery.
The delivery tool performs the final compile and preflight.

## Proved and sorry left

Original holes: one. The body of
`AlgebraicGeometry.Scheme.finitePerfectAdic_etale_stalk_data` is now complete, but this
is a decomposition, not an unconditional proof: two strictly smaller holes are added.
There are no remaining holes in the item module, the data module, or the two-level
refinement module. Net holes closed minus added in this packet: 1 - 2 = -1.

The two new holes, each exactly `:= by sorry`, are:

- `AlgebraicGeometry.Scheme.finitePerfectAdic_etale_level_descent`, node
  `lem-weil-pbc-finite-perfect-adic-etale-level-descent`: one index, one given chart and
  point, no coefficient compatibility, cover-existence or adjacent-level conclusion.
- `AlgebraicGeometry.Scheme.finitePerfectAdic_constant_models_reduction`, node
  `lem-weil-pbc-finite-perfect-adic-constant-models-reduction`: two already supplied
  constant models on one nonempty chart, with no descended etale complex or local
  constancy assertion.

`AlgebraicGeometry.Scheme.finitePerfectAdic_stalk_reduction` has a complete Lean proof
from the latter obligation and existing finite-ring local constancy. The private cover
and pullback helpers also have complete proofs. Each remaining hole has a full proof
in words and source in its docstring and node.

Edge cases checked in the argument: the empty base uses an empty cover; a selected
point ensures the common chart for scalar balancing is nonempty; zero quotient rings
and zero complexes require no exclusion; no connectedness is assumed for single-level
descent. Constant-model balancing would be false on an empty chart without the point.

## No longer needed

No existing module or node is withdrawn, and no module is claimed globally pruned.
No original public import is removed. The new data module does not import
`ConstantRealizationDerivedScalarExtension`; only modules whose statements use its
scalar-extension functor import it publicly. The constant-model balancing module imports
the existing tower data directly and does not depend on the new descended-level record.

The original node's step descending actual consecutive arrows by full faithfulness is
not needed for this theorem: its conclusion asks only for pairwise scalar-extension
isomorphisms. These are obtained on a common nonempty local chart. The consumer still
constructs adjoint transposes and the normalized tower. Thus no separate descended-arrow
construction is added. The original comparison, stalk and tensor dependencies remain
needed within the two narrower obligations; their modules are not claimed pruned.
The main node now lists precisely the connected-cover, one-level-descent, two-level-
reduction and data nodes used by the proof.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requested more diagram structure than its Lean conclusion
needs. Pairwise constant-model balancing suffices, so descending consecutive arrows is
unnecessary here. This changes no unit-level route or target statement.

The listed finite-ring constructible-derived-origin dependency is currently quarantined
under `quarantine/Sheaf/Paper/FiniteRingConstructibleDerivedOrigin.lean` according to
`coord/rework.tsv`. Its archived declaration and obligation are preserved. Single-level
descent still cites that dependency in its proof plan; this packet neither withdraws nor
restores the archive and does not treat its absence as evidence of unused mathematics.

The terminal object of the small etale category is not definitionally the identity
chart. The cover proof explicitly pulls the sieve along their canonical isomorphism.

## New nodes

`def-weil-pbc-finite-perfect-adic-etale-level-data` records one descended quotient,
its small perfect algebraic fibre, an actual derived stalk comparison, and transport
for any supplied algebraic constant model. It also attaches the unchanged exact stalk
functor and the explicitly constructed exact algebraic universe lift. This node has no
existence theorem or hole.

`lem-weil-pbc-finite-perfect-adic-etale-level-descent` isolates the single-level
finite-coefficient descent and perfect-fibre construction from Stacks 09C6/09AL/09B1.
Its conclusion concerns one prescribed chart, point and index, without any adjacent
scalar-extension or cover-existence conclusion.

`lem-weil-pbc-finite-perfect-adic-constant-models-reduction` isolates local scalar
balancing of two already supplied constant models. Its proof plan is quotient scalar
transitivity, compatibility of constant realization, and reflection by a geometric stalk
on the specified nonempty chart. It has no level-descent content.

`lem-weil-pbc-finite-perfect-adic-stalk-reduction` attaches the proved two-level
refinement argument. It consumes two level records, uses existing finite-ring local
constancy, and invokes the local constant-model balancing obligation. The blueprint
ancestor, unit and source route are retained for all four nodes. Searches of the
blueprint, project library and three Mathlib search kinds found no exact replacement.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
