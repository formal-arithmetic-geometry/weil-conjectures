## What changed

Proved `AlgebraicGeometry.exists_flat_telescope_model_shift_gauge` from bounded-flat
normalization and its countable-sum/transition-cone extension. The existing theorem's
signature and public imports are unchanged. Added only proof imports to that module; the second reader removed the redundant
direct bounded-normalization import, available through the extension module.

The assembly proof compares the supplied left-derived counit with the recorded
K-flat counit using the universal property, proves its invertibility on flat
telescopes using `CochainComplex.kFlat_closure`, and uses shift compatibility to
prove invertibility on their translates. The gauge is the explicit ratio
`alpha_X` followed by the inverse counit. Its stage naturality is proved by
postcomposition with the invertible counit and cancellation. Its shift equation
is proved by postcomposition with the shifted counit, `NatTrans.shift_app_comm`,
the normalized comparison equation, and inverse cancellation. The supplied
pullback shift structure is retained throughout.

Added two modules, each with one intermediate theorem, and a real predicate for
bounded-flat homotopy representatives. The bounded theorem only normalizes
bounded-above flat stages. The extension theorem receives their comparison,
naturality, translated-unit isomorphism and shift square as inputs and extends
through sums and transition cones. Neither theorem restates the original gauge:
there is no original counit or source automorphism in either conclusion, and the
bounded assertion does not assert anything on unbounded telescopes.

Compilation is through the authorized `lcompile.py` only, single files or the
sandbox in import order. The main proof uses scoped 800000 heartbeats for
elaborating the dependent counit comparison, while retaining the 60-second wall
limit. No existing statement, definition, visibility or target was changed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_flat_telescope_model_shift_gauge`
(node `lem-sc-flat-telescope-model-shift-gauge`). No sorry remains in the item's module.

Added two holes, exactly `:= by sorry`, with sources and complete proof sketches:

- `AlgebraicGeometry.exists_bounded_flat_model_normalization`
  (`lem-sc-bounded-flat-model-normalization`, module
  `Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization`).
- `AlgebraicGeometry.exists_flat_telescope_comparison_of_bounded_normalization`
  (`lem-sc-flat-telescope-bounded-normalization-extension`, module
  `Sheaf.AlgebraicGeometry.FlatTelescopeBoundedNormalizationExtension`).

This is a decomposition, not a complete proof independent of new holes: one
upper hole closed, two strictly smaller argument steps left, net minus one hole
before the ledger's import-closure calculation. `boundedFlatShiftRepresentative`
is a real existential predicate, with no postponed construction or proof.

## No longer needed

No original dependency module or node is pruned from the target closure.
The K-flat closure theorem is used directly; stage-map refinement is retained
in the new extension node's proof, and canonical tensor/shift definitions remain
necessary for the comparisons. No original import was removed. The redundant newly added direct proof import
`Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization` was removed from the item;
the extension module publicly imports it. The original direct dependency nodes
`def-pc-scheme-derived-tensor-structure`, `def-sc-scheme-canonical-tensor-shift`, and
`lem-sc-flat-telescope-stage-map-refinement` move to the smaller steps and remain
in their transitive proof dependency closure; none is claimed pruned.

Removed redundant public imports of `DerivedPullback`, `SchemeCanonicalShiftUnitIso`,
`Mathlib.AlgebraicGeometry.Morphisms.Proper`, and `Mathlib.AlgebraicGeometry.Noetherian`
from the new extension module: its public bounded-normalization import already
supplies these. The bounded module uses `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`
instead of importing the unrelated telescope-stage definitions.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies supply the geometric K-flat models and canonical tensor
shifts; they do not already state the supplied-tensorator normalization calculation.
That calculation is explicitly the inherited agent expansion, not a theorem of
Stacks Tags 06YS or 06YJ. The two new theorem docstrings and nodes preserve that
source distinction. Tag 06YS was checked on its official page: it supplies flat
K-flat resolution models, rather than the gauge normalization. The local literature
paths recorded in SETUP are absent on this worker machine; no literature files or
project settings were changed. LeanSearch returned Internal Server Error, recorded
as unavailable rather than no match; successful LeanFinder, Loogle and Mathlib grep
searches are recorded in the sandbox search log.

The existing translated-unit shift and normalized telescope comparison theorems
cannot be imported as shortcuts: their import closures already reach this item,
as verified by `tools/import_direction.py may`. No circular import was introduced.
The initial trial was discarded before delivery. Only the two smaller steps and
the completed ratio assembly are delivered.

Edge cases checked against the new statements: zero complexes and zero towers,
empty schemes, bounds depending on the tower index, stages with zero transition
maps, and different presentations of a homotopy object. There is no uniform tower
bound, no nonzero assumption, and no claim of naturality for objects outside the
indicated classes. Presentation independence and cone normalization remain in the
extension step; they are not claimed to follow from mere existence of an unrelated
object isomorphism. The unit and chapter routes are unchanged. The overlay DAG closure check found the
pre-existing cycle `lem-pc-cycle-pullback-tower-comparison-stage3` ->
`new-tower-comparison-first` -> `lem-pc-cycle-pullback-tower-comparison-stage3`.
The same cycle is reached in the unmodified baseline. None of the four delivered
nodes has a return path to itself through its dependencies; no new cycle involving
these nodes was introduced. This inherited DAG issue is reported for the maintainer,
without editing either unrelated node.

## New nodes

`def-sc-bounded-flat-shift-representative` records the explicit bounded-above,
termwise-flat presentation predicate used to state the first intermediate step.
It is declared in `BoundedFlatModelNormalization.lean`, and introduces no hole.

`lem-sc-bounded-flat-model-normalization` is the bounded-stage and shifted-unit
part of steps 1--2 of the original model-gauge plan. It leaves the supplied
monoidal-unit/tensorator calculation on bounded-flat objects to a separate item.

`lem-sc-flat-telescope-bounded-normalization-extension` is the countable-sum,
transition-cone and presentation-independence part of steps 1 and 3, assuming
bounded normalization. Its input e is retained in its conclusion.

No change record or forced adaptation is needed: every existing signature and
public interface stays identical, and no other existing module is edited.

## Second reading by H3

1. **Unchanged interface: pass.** Diffed the existing item against the repository.
   Its entire theorem signature before `:= by` is byte-for-byte identical,
   including the supplied counit, left-derived hypothesis, shift instances,
   naturality restriction and shift equation. Its original public imports,
   declaration visibility and docstring are unchanged. The other two modules
   and three nodes are new; there is no existing definition or target change,
   and no forced adaptation or change record is required. Read the relevant
   existing telescope-presentation extraction and cone-counit correction records.

2. **Kernel/proof checks: pass as a decomposition.** Compiled all three modules
   with `lcompile.py` in dependency order. The original hole is closed by
   comparison of left-derived counits, K-flat closure, shift transport, and
   cancellation of invertible counits. No data are selected from a newly holed
   mere-existence theorem: the new definition is only an explicit Prop predicate,
   and the witnesses of the two new theorems are used inside a theorem proof.
   Exactly two named `:= by sorry` proofs remain, precisely those listed above;
   there is no sorry in a definition and no forbidden declaration or attribute.
   A scratch copy with `#print axioms` for all four declarations compiled: the
   three theorems use only `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`;
   the predicate uses only the three permitted axioms. The scratch copy was
   removed. This does not certify a sorry-free target: net one extra hole remains.

3. **Split statements and sources: pass.** Read each new signature against its
   docstring and node. The first step restricts to bounded-above flat objects;
   the second assumes their natural normalized comparisons and retains the
   supplied translated-unit isomorphism. Neither is the original automorphism
   assertion renamed. The extension does not claim agreement with every input
   beta on overlapping objects, a claim not present in its conclusion. Checked
   zero objects and zero towers, empty schemes, bounds varying with the stage,
   zero transitions, and proof-independence of representative predicates. An
   arbitrary incompatible e is not asserted to work: the bounded shift equation
   is an explicit hypothesis of the extension. Checked official Stacks
   [06YS](https://stacks.math.columbia.edu/tag/06YS) and
   [06YJ](https://stacks.math.columbia.edu/tag/06YJ): they supply flat resolutions
   and K-flat computation; supplied-tensorator normalization remains explicitly
   attributed to the inherited agent argument. Repeated LeanFinder with
   "natural comparison of derived tensor functors compatible with suspension on
   bounded above complexes", Loogle with `CategoryTheory.NatTrans.shift_app_comm`,
   and Mathlib grep with bounded-normalization/telescope-shift terminology;
   searched both source roots under lean with comparison/suspension terminology.
   Results are generic Tor, monoidal-complex and shift APIs, not these statements.
   Existing normalized telescope comparisons depend on this item, so cannot be
   used as shortcuts. Neither split hole admits a few-minute closure from those
   APIs; their named remaining work is kept visible rather than counted proved.

4. **Route and pruning: pass, with inherited bookkeeping gap.** Read the unit
   `sk-thm-picard-duality` and the original model-gauge plan. The bounded-stage,
   sum/cone and ratio route is retained, with no chapter or unit edit. The old
   direct proof dependencies that moved below the new nodes remain in their
   closure and are explicitly identified under No longer needed; no original
   module is pruned. Removed the redundant new bounded-normalization proof
   import from the item. All new imports used only by the planned proofs are
   ordinary `import`, not public imports. The repository unit's `realized`
   already has an empty statement list and an empty step list; this delivery
   preserves it and reports the inherited missing realization to the maintainer.

5. **DAG/Lean agreement: pass.** Compared the main node's counit-invertibility,
   ratio, naturality and shift-cancellation steps to the Lean proof, and all new
   statements to their node records. Each proof_deps is exactly the union of
   its proof-step uses. The existing node changes only `lean`, `proof`,
   `proof_deps` and `proof_origin`. New nodes record sources, agent origin,
   searches, creation, blueprint ancestry, chapter/unit and verbatim normalized
   Lean signatures. Added missing ordinary proof imports for the bounded-above
   K-flat lemma in the first split and K-flat closure/common tower refinement
   in the second, matching their recorded plans. Import-direction checks confirm
   these dependencies do not reach their importing new modules. The pre-existing
   unrelated DAG cycle reported above is not changed by this delivery.

Changes by the second reader: removed one redundant proof import and extra blank
line in the item; added the three missing planned dependency imports to the new
modules; clarified direct-versus-transitive dependency accounting and the inherited
unit realization gap in this report. No theorem signature, definition body or
mathematical proof body changed. Final delivery validation follows this reading.
