## What changed

Replaced the sole `sorry` in `Module.exists_noetherian_flat_closedFiber_model` by a complete
Lean assembly proof, preserving its signature and visibility. The proof constructs a directed
Noetherian model tower, obtains independent base-flatness and closed-fibre-flatness tails,
chooses a common upper bound using `exists_ge_ge`, and supplies all 27 structure-instance
binders and the five conclusion clauses from that stage.

Added `Sheaf.RingTheory.NoetherianLocalModelTower`, a genuine structure containing stage rings,
finite stage modules, compatible local transition and limit maps, elementwise colimit criteria,
transition localization/base-change comparisons, and the two limit module-localization
comparisons. It contains no flatness condition, no chosen witness, and no `sorry`.

Added separate modules for tower existence, base-flat stage existence, base-flatness
persistence, and closed-fibre flatness. Both base-flatness modules have complete proofs.
The stage-existence proof constructs ring and additive-group functors and cocones, proves
their colimit properties from the elementwise tower fields, handles the independent ring
and module universes with `ULift`, transports module structures and flatness through the
colimit comparisons, and applies the existing `RingTheory.exists_flat_stage`. Persistence
is proved by tensor base change, flatness of the localization algebra, tensor associativity,
and transport through the module transition equivalence. All private helpers are proved.

The two admitted statements isolate independent parts of the original argument. Tower
existence has neither flatness hypothesis; fibre descent has no base-flatness hypothesis or
conclusion. The main proof combines these parts by directedness. The item node records this
route; the base-flatness nodes record the proved categorical and tensor arguments.

## Proved and sorry left

Closed the original hole in `Module.exists_noetherian_flat_closedFiber_model`
(node `lem-weil-pbc-noetherian-flat-closed-fiber-model`). Its proof compiles without a local hole.
This is a decomposition, not a sorry-free proof of the mathematics: one original hole closed, two
strictly smaller holes added, net minus one hole in this delivery. Its axioms still include
the two admitted intermediate proofs and the existing dependencies of eventual flatness.

Every remaining hole in this delivery is the entire proof of a named public theorem:

- `Module.exists_noetherian_localModelTower` —
  `lem-weil-pbc-noetherian-local-model-tower-existence`.
- `Module.NoetherianLocalModelTower.eventually_fiberFlat` —
  `lem-weil-pbc-noetherian-local-model-tower-fiber-flat`.

`Module.NoetherianLocalModelTower.exists_baseFlat_stage` and
`Module.NoetherianLocalModelTower.eventually_baseFlat` are proved from existing library and
Mathlib declarations, with no added hole.

Each remaining hole has a source and a complete proof in words in its docstring and node. The tower definition
has no admitted data or proof. Edge cases checked in the statement design: the zero module is
allowed in all the new lemmas; each tail includes its first index; directedness, not a linear
order or a maximum operation, suffices; stage-module universe remains `t`; the stage rings
and index universe is `max u v w`. Neither stage algebra is asserted flat.

## No longer needed

No mathematical branch is pruned. Removed the two direct proof imports
`Sheaf.Paper.LimitTowerEssentiallyFinitePresentation` and
`Sheaf.RingTheory.ColimitEventuallyFlat` from the item's module. They remain imported by the
new existence and descent modules, respectively, so they are moved down rather than removed
from the target closure. All existing public imports are retained. During proof development, removed the unnecessary
new proof imports `Sheaf.RingTheory.Flat.LocalizationPreservesFlatness` from the base-tail
module, and the redundant `Mathlib.RingTheory.Flat.Stability` and
`Mathlib.Algebra.Category.Grp.FilteredColimits` from the base-stage module (their APIs are
already public imports of the required Mathlib modules). No extra DAG branch is claimed pruned.

The parent node's old proof dependencies are assigned to the appropriate lower arguments:
model construction uses the tower, finite-type/localization Noetherianity, filtered-colimit
representation, localization base change/composition, and localization-tensor compatibility;
base descent uses eventual flatness and base-change/localization persistence; fibre descent
uses quotient tensors, quotient Noetherianity, filtered-colimit equality and eventual flatness.
The definition and colimit infrastructure, and exactness used to prove localization
persistence, remain available through those lower dependencies. None is claimed globally
unreachable. The blueprint unit `sk-thm-p1` and all its realized statements and steps are
unchanged; this is entirely below its unit level.

## Where the brief, the DAG or earlier work was wrong

The tower dependency's theorem is stated for three rings in the same universe, whereas this
item permits different ring universes. The existence lemma explicitly records the required
`ULift` transport, with no change to the item's universe binders. The supplied tower and
eventual-flatness declarations do not themselves include the localization-module conversion,
composed top transition localization, quotient-system construction or flatness persistence.
Tower/quotient-system glue is isolated in the two remaining admitted nodes. The categorical
colimit transport and base-flatness persistence glue is proved in this delivery; no change
to an existing dependency is required.

The Stacks TeX source is absent in this read-only clone. Read the current official statements
and proofs at https://stacks.math.columbia.edu/tag/00R7 and
https://stacks.math.columbia.edu/tag/00R6. The source's nonzero assumption is used only after the
approximation stage, not in this model-construction theorem. Its final tensor equalities
require the localization corrections already present in this item's statement; those are
retained. LeanSearch returned Internal Server Error and is recorded as unavailable, not as
an unsuccessful search. LeanFinder, Loogle and Mathlib/source grep found no direct shortcut.

## New nodes

`def-weil-pbc-noetherian-local-model-tower`: the explicit compatible model-system data, in
`Sheaf.RingTheory.NoetherianLocalModelTower`. It packages the directed system without any
flatness conclusion or admitted construction.

`lem-weil-pbc-noetherian-local-model-tower-existence`: first paragraph of 00R7 plus Noetherianity
and transition/limit localization conversion, in `NoetherianLocalModelTowerExistence`.

`lem-weil-pbc-noetherian-local-model-tower-base-flat-stage`: proved application of 00R6
after construction of categorical colimits, in `NoetherianLocalModelTowerBaseFlatStage`.

`lem-weil-pbc-noetherian-local-model-tower-base-flat`: proved persistence from one base-flat
stage by tensor base change and a flat localization algebra, in `NoetherianLocalModelTowerBaseFlat`.

`lem-weil-pbc-noetherian-local-model-tower-fiber-flat`: quotient-system construction and the
second application of 00R6 followed by persistence, in `NoetherianLocalModelTowerFiberFlat`.

No existing interface is changed, no other group's module is adapted, and no change record
is needed. All six delivered Lean modules are checked together through `lcompile.py --all`.

## Second reading by W2

1. **Statements and interfaces.** Compared the delivered target module with the repository
   version. The theorem signature and all existing declarations are byte-for-byte unchanged;
   only the target proof and the explicitly documented new modules and nodes were added.
   The new tower and tail statements match their Lean declarations, retain the stated
   universe bounds, and add no hypotheses to the target.
2. **Proof checks.** Compiled all six delivered modules with `lcompile.py --all`; compilation
   succeeds. Sorries occur only in the two named split theorems
   `Module.exists_noetherian_localModelTower` and
   `Module.NoetherianLocalModelTower.eventually_fiberFlat`, each with a source, proof
   docstring, and matching node. No forbidden declarations or hollow definitions occur.
3. **New statements.** Searched the library and DAG for duplicate tower, base-tail, and
   fibre-tail declarations. The structure and four lemmas are new, strictly below the
   target, and their hypotheses and conclusions are exactly those required by the target
   reduction. The zero-module and directed-tail edge cases are covered by the statements.
4. **Pruning and route.** The target proof uses the tower existence, base-flat tail, and
   fibre-flat tail, then directedness; this agrees with the target node's proof and
   dependencies. The original direct proof-only imports were moved into the lower modules,
   and redundant proof imports were removed there. The unit `sk-thm-p1` route and its
   realized nodes are unchanged.
5. **DAG and report consistency.** Verified that each delivered node's Lean module,
   declaration, statement, proof steps, proof dependencies, source, and split status agree
   with the files. The report lists every closed and remaining hole and all imports moved or
   removed.

No further changes were required by this second reading.
