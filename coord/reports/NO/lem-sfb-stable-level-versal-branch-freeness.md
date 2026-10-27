## Worker report

The delivery states `AlgebraicGeometry.stable_level_versal_branch_freeness` in
`Sheaf.AlgebraicGeometry.StableLevelVersalBranchFreeness`. Its sole proof is `sorry`.
The chart definition node supplies the effective chart, the full frame functor,
and the actual normalized generic algebra. The fibre-curve definition node supplies
the concrete base-equality transport in its own module. All definitions have real
data; neither definition module contains postponed theorems or hollow constructions.

The previous worker's Q67 observation concerned stage 1: the current item is split
and its proof was reviewed, but it has no Lean record. A stage-2 statement is still
needed. This packet changes its Lean record and adds the chart and fibre-curve definition prerequisites to
`stmt_deps`; it preserves its statement, proof, and every other field.

The source read is Pikaart--de Jong, Sections 2.3.3 and 2.3.6, printed pp.10--11,
https://arxiv.org/pdf/alg-geom/9501003 . Section 2.3.6 describes the universal stable
family, node parameters, full level cover, normalization, formal quotient, and the
freeness input from Deligne Proposition 3.5. The node uses its equal-characteristic
version, so the actual coefficient ring here is Omega, rather than Witt vectors.
The theorem docstring retains all seven proof steps and every dependency in them.

Hypotheses and objects:

- The algebraically closed field is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`.
- The genus and its bound are `(g : ℕ) (hg : 2 ≤ g)`.
- The stable unpointed genus-g curve is the actual object
  `C : StablePointedModuli.Fiber (Spec (.of Ω)) g 0 (Over.mk (𝟙 _))`.
  This retains the family and all its automorphisms, rather than an isomorphism class.
  `StablePointedModuli.fiberCurve C` is its canonical underlying curve over Omega.
  Its `Aut` is exactly the group H of Omega-curve automorphisms; there are no markings
  to preserve, because their label set is `Fin 0`.
- The node count is `(d : ℕ)` and `hnodes`, asserting that the set of nonsmooth
  points has `encard = d`. Its predicate is failure of formal smoothness of the
  stalk ring map. This is precisely the underlying set of the complement of
  Mathlib's `Scheme.Hom.smoothLocus`: stable families are locally of finite
  presentation, so this uses the smooth locus, and does not substitute formal
  smoothness of an unrelated local algebra. Nodality is already in C's stability.
- The level conditions are `hprime : ℓ.Prime`, `hthree : 3 ≤ ℓ`, and
  `hinvertible : IsUnit (ℓ : Ω)`. In a field the last condition is exactly
  characteristic different from ell. No assumption concerns the order of H.

Each conclusion is in the existential `D : StableVersalLevel.Chart Ω g d ℓ C`
and the subsequent geometric stabilizer assertion:

- `Ring Ω g` is literally `MvPowerSeries (Fin (3 * g - 3)) Ω`.
  `base` is its affine spectrum with the structural Omega-map, and `closed` is
  `Spec.map` of `MvPowerSeries.constantCoeff`.
- `D.deformation` is an effective stable family in the recorded moduli fibre over
  that spectrum, and `D.special` identifies its actual special fibre with C.
- `D.formal` is `IsFormalChart`. For EVERY Omega-algebra R, nilpotent ideal I,
  stable family X/R and marking X_(R/I) ≅ C_(R/I), it gives a UNIQUE pair of a
  classifying Omega-map to Spec A and an isomorphism X ≅ a*D with that exact
  marking. The reduction equation makes the image of the maximal ideal nilpotent,
  so these are precisely maps to the adic formal base. The displayed isomorphism
  equation fixes its restriction, not only its isomorphism class. This tests all
  affine nilpotent thickenings, including arbitrary residue extensions.
- This marked description is the formal-quotient clause, with arrows retained.
  Over the residual gerbe a special-fibre object is etale locally C; its sheaf of
  identifications with C is its actual H-torsor (H is constant because Omega is
  algebraically closed and stable-curve Isom is finite unramified). Applying the
  marked universal property locally and its uniqueness to overlaps gives the
  equivariant formal-base map and its descent. Conversely pullback and descent
  along a torsor recover the family. The same uniqueness identifies arrows.
  Thus forgetting the marking gives [Spf A/H], including nontrivial torsors on
  nonlocal bases, and not a coarse orbit set or only rational Artinian tests.
- `D.baseAction` and `D.curveAction` are group homomorphisms from that actual H,
  acting by Omega-scheme automorphisms. `D.fixesClosed` fixes the closed section;
  `D.equivariant` makes the family projection equivariant; `D.specialAction`
  identifies the special-fibre action with the specified automorphism h itself.
  Fixing the maximal ideal also makes the induced ring action adically continuous.
- `D.nodeBound` allows `Fin.castLE` to name precisely the FIRST d parameters.
  `discriminant` is their product. `smoothOpen` is the actual principal open D(f),
  canonically Spec A[1/f]. `D.smoothLocus` tests every base change T → Spec A:
  its family is smooth iff its image lies in that open. It states the entire
  smooth-family inverse image, with no extra discriminant components.
- `D.cover`, `D.coverMap`, `D.finite`, and `D.etale` give the finite etale U-scheme E.
  `D.frame` is the actual module-sheaf isomorphism from constant rank 2g to
  `abelianLevelCohomology`, which is the recorded R^1 of the constant Z/ell sheaf.
  `D.represents` gives the unique map classifying EACH frame after EVERY base
  change to U. Its equation uses `abelianLevelBaseChange` and
  `Scheme.upperStarConstantSheafIso`. The intervening cartesian curve map is fixed
  by its first-projection equation. No pairing or symplectic condition occurs.
- `D.coverAction` covers the specified base action (`D.coverEquivariant`).
  `D.frameAction` makes the tautological frame equivariant for the family action
  and identity on constant labels, using those same canonical comparisons.
  This specifies the natural frame action; it is not an arbitrary cover action.
- `genericRing E` is the product of `E.residueField x` over ALL `genericPoints E`.
  For a finite etale scheme over this integral normal open, these are exactly the
  function fields of its generic components. `genericMap` is obtained from the
  structural map and global evaluations, with the canonical `ΓSpecIso`.
  `branchRing` is Mathlib `integralClosure` in that actual product, equipped with
  THIS diagonal base algebra, not the integral closure over a product of bases.
- `D.normalOpen`, `D.normalSquare`, and `D.normalGeneric` identify the restriction
  of Spec B with E over U and fix its generic inclusion exactly coordinate by
  coordinate. `D.normalAction`, `D.normalEquivariant`, and
  `D.extendsCoverAction` express extension of the natural action from E and A.
  These are scheme actions, equivalently the contravariant ring action on B.
- The remaining conclusion quantifies over every algebraically closed extension
  `K` and actual geometric point `b : Spec K ⟶ Spec B`. The equality with the
  scalar-extended `closed Ω g` restricts b to the geometric closed fibre.
  For EVERY `h : Aut (fiberCurve C)` the conclusion is
  `b ≫ (D.normalAction h).hom.left = b ↔ h = 1`.
  This is equality of geometric morphisms, not only equality of underlying points;
  it gives exactly stabilizer {1}, including the identity direction.
- The universe u is explicit throughout and includes the geometric-point fields
  of the project's scheme-size convention. Cohomology coefficients keep the
  existing `ULift.{u+1}` / `ModuleCat.{u+1}` encoding. No site universes are equated.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `StablePointedModuli`, its `Fiber`, `abelianLevelCohomology`,
  `abelianLevelConstant`, and `abelianLevelBaseChange`. These supply the actual
  stable family, genus, coefficient sheaves and canonical exchange maps.
- `Sheaf.AlgebraicGeometry.StableFiberCurve`:
  `StablePointedModuli.fiberCurve`, the canonical transport to the given fibre base.
  The new `def-sfb-stable-fiber-curve` definition node owns this existing declaration
  and is a statement dependency of both the item and chart. The finite-unramified
  theorem remains a proof dependency; it is not a statement prerequisite for this def.
- Mathlib `Field` (`Algebra.Field.Defs`), `AlgebraicGeometry.Scheme`
  (`AlgebraicGeometry.Scheme`), `IsFinite` and `IsIntegralHom`
  (`AlgebraicGeometry.Morphisms.Finite` and `.Integral`), `Etale`
  (`AlgebraicGeometry.Morphisms.Etale`), `MvPowerSeries`
  (`RingTheory.MvPowerSeries.Basic`), `AdicCompletion` and `IsAdicComplete`
  (`RingTheory.AdicCompletion.Basic` / `.Algebra`), and `integralClosure`
  (`RingTheory.IntegralClosure.Algebra.Basic`). Read the dependency node statements,
  their records, and these definitions/docstrings. Adic completion is background
  for interpreting the already complete power-series base as a formal scheme;
  it is imported without constructing a second completion notion.
- Supporting Mathlib maps are `Scheme.Γevaluation`, `Scheme.residueField`,
  `genericPoints`, `RingHom.pi`, and `Over.pullback`; none is replaced by a private copy.
- The main module imports the recorded proof modules
  `UnpointedStableCoarseProjective`, `SmoothCurveAbelianLevelRigidification`,
  `FiniteEtaleNormalGenericComponents`,
  and upstream `WeilConjectures.RingTheory.PowerSeriesNormalDomain` as proof imports.
  The finite-unramified proof module was withdrawn from the live source, so its
  import is omitted while its proof dependency and proof-plan citation are retained.
  The remaining unavailable proof modules are likewise not imported. The full proof
  remains in the docstring.

Edge cases checked before writing:

- d=0: `Fin 0` product is 1; its principal open is all Spec A.
- g=2 and the maximal possible node count: dimensions use natural `3*g-3`, and
  `nodeBound` is a conclusion, not an extra restriction on the input curve.
- No empty stable curve can enter, since the recorded stable-fibre definition
  includes connected nonempty geometric curves; empty test bases remain allowed
  by the formal and full-frame universal properties.
- Nilpotent pairs include I=0 and nonlocal R. Marking-preserving isomorphism
  uniqueness retains stack arrows and does not incorrectly quotient them away.
- ell=3 is allowed except in characteristic 3. Characteristics dividing |H| are
  allowed; no averaging, tame-stabilizer hypothesis, or symplectic frame is used.
- Disconnected E: the generic product ranges over every component. Nontrivial
  residue extensions in the geometric closed fibre and the identity h are retained.

Searches performed:

- `msearch.py` LeanSearch: "Effective formal deformation chart of a stable curve
  with full cohomology frames and integral closure in the generic fields". Eight
  results: general normal-closure, scheme normalization, and formal-unramified
  declarations, none giving the chart or theorem. An earlier attempt was rate
  limited; the successful search was repeated and its raw result is in the new node.
- `msearch.py` LeanFinder: "Stable curve formal deformation chart with full
  cohomology frame cover and normalized generic branches". Its raw results are in
  the new node; general affine-limit, etale, elliptic-reduction, formal-unramified
  and smoothness declarations do not define this chart. A separate theorem search returned general Galois actions.
- `msearch.py` Loogle: "MvPowerSeries, integralClosure": no matches.
- `msearch.py` Mathlib grep: `versal|stable.*curve|formal.*deformation` in
  AlgebraicGeometry. Results concern general scheme universal properties; no match.
- `rg` over BOTH `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `StableLevelVersal|versalBranch|formalStabilizer|VersalChart|DeformationChart`:
  only a proof-plan citation in `StableAbelianLevelNormalization.lean`.
- `tools/blueprint_refs.py search 'stable versal level chart'`: zero matches.
  Read related DAG nodes `lem-sfb-dm-effective-formal-stabilizer-chart` and
  `lem-sfb-nodal-deformation-smoothing-parameters`: they are proof/existence
  statements without Lean records, not existing definitions of the chart data.

The initial implementation and the ownership repair previously passed compilation
and dry runs (commits `206719b5600` and `384300ccab2`). The current validation is
recorded below; these historical results do not validate the changed imports.
There is no statement correction and no STATEMENT-DISPUTED claim.

## Dependency modules

Maintenance registered the original definition records on the server in commit
`4d5fb958975eab1f01940feb0741f286a2bb7c69`, assigning the maintainer-owned
`import_flags: ["unreachable"]` and leaving the Lean records absent. The unchanged
stage-2 gates now treat them as existing dependency nodes; this delivery supplies
only their Lean records and their previously authored modules:

- `def-sfb-stable-fiber-curve`: `Sheaf.AlgebraicGeometry.StableFiberCurve`, the
  canonical underlying curve transported along the fibre object's base equality.
  Its lean.note explains the withdrawn old declaration and the concrete replacement.
- `def-sfb-stable-versal-level-chart`: `Sheaf.AlgebraicGeometry.StableVersalLevelChart`,
  the complete chart definition described below. Its lean.note explains the missing
  base record and the interface supplied here.

This resolves the returned reachability finding through maintainer-owned DAG
metadata. The two definition statements, dependency lists and Lean sources are
unchanged. The earlier retry diagnostics below describe the previous base; run
`deliver2.py NO lem-sfb-stable-level-versal-branch-freeness --no-push` against the
current server base, retain both flags, and then use the normal delivery path.
No independent statement review is claimed by this maintenance repair.

Maintenance verification succeeded: `deliver2.py --no-push` built `526c50bbb35`,
checked all three Lean files and passed the unchanged server preflight. The full
effective landing DAG check also returned no findings. Nothing was pushed by
maintenance; the packet is ready for the next worker to deliver normally.

## New nodes (authored in the original packet)

`def-sfb-stable-versal-level-chart` defines
`AlgebraicGeometry.StableVersalLevel.Chart` and its concrete helper constructions
in `Sheaf.AlgebraicGeometry.StableVersalLevelChart`. Its source is Pikaart--de Jong
Sections 2.3.3 and 2.3.6, with the usual marked formal-deformation description.
Its node is self-contained: marked universality, actual actions, discriminant,
full frame representability with canonical base change, diagonal generic product,
actual integral closure, and the extension action. It asserts no existence and
builds in no freeness. The searches above, recorded with their raw Mathlib results,
found no existing definition. The existing general formal-chart and nodal-smoothing
DAG nodes assert theorems, rather than providing this missing definition.


`def-sfb-stable-fiber-curve` owns the concrete plain definition
`AlgebraicGeometry.StablePointedModuli.fiberCurve` in the delivered module
`Sheaf.AlgebraicGeometry.StableFiberCurve`. It transports the family's projection
using the base equality stored in the actual functor fibre; its signature quantifies
over arbitrary `S`, `g`, `r`, `T`, and `C`. Its body is exactly
`Over.mk (C.of.val.projection ≫ (eqToHom C.of.property).left)`.
It uses no choice or finite-unramified theorem. The source is Stacks 003T and 0E7A
and the already recorded actual fibre construction. The old module containing this
helper has been withdrawn, so an `existing: true` binding to it is no longer usable.
Current source searches found no definition to duplicate. This module restores the
same canonical construction under its own definition node, rather than restating
the withdrawn finite-unramified theorem.

## Returned delivery repair

The H2/H12 return on immutable head `4acdc99c5246` requested definition ownership
for the plain `fiberCurve` helper. The saved packet already adds
`def-sfb-stable-fiber-curve` to the item's `stmt_deps`, replaces
`lem-sfb-stable-isom-finite-unramified` by it in the chart's `stmt_deps`, and fixes
the chart's TeX citation. The finite-unramified theorem remains in the item's proof
plan. The main node differs from the current shared node only in `lean` and
`stmt_deps`; there is no change to its mathematical statement or proof plan.

The prescribed first dry run of the saved packet failed: the server no longer has
`StableIsomFiniteUnramified.olean`. The required `scompile.py --source` confirmed
`Module source unavailable: Sheaf.AlgebraicGeometry.StableIsomFiniteUnramified`.
The live return for NW records its removal from the global-build candidate. To
repair this diagnostic, the new definition node now delivers `StableFiberCurve`
with the same concrete construction, rather than recording an absent declaration
as existing. The chart publicly imports this owning module. The main module drops
only the unavailable proof-only import. Its theorem signature, the chart signature,
and every chart field are unchanged. This is an authorized missing-helper repair;
no dependency theorem or stronger hypothesis is introduced.

Repair searches (2026-10-22): the saved LeanSearch query "Underlying curve over the
specified base of an object in the stable pointed moduli fibre groupoid" returned
eight general pointed-object, Weierstrass, and fundamental-groupoid projections,
with no stable-moduli definition. Loogle queried
`CategoryTheory.Functor.Fiber, CategoryTheory.Over.mk` and returned zero hits.
Mathlib grep `fiberCurve|stable.*moduli` in AlgebraicGeometry returned zero hits.
The current `rg -n 'fiberCurve|def-sfb-stable-fiber-curve' lean/Sheaf
lean/WeilConjectures dag/nodes` finds only the withdrawn theorem's DAG record:
no live Lean source declares the helper. The successful previous search and this
changed source state are both retained in the definition node's search records.
Blueprint search "stable fibre curve" returned zero matches; ancestor lookup
returned `None`, retained in the new node.

Self-check: the new node's `lean.statement` is the exact delivered definition
signature. `C.of.val.projection ≫ (eqToHom C.of.property).left` gives precisely the
underlying curve over `T.left`, with every universe and variable bound. The source
dependency `StablePointedModuli.Fiber` is the core of the actual functor fibre.
The unpointed case has no labels, so its `Over T.left` automorphisms are exactly
those in the main theorem. This definition imposes no restriction on empty test
bases, genera, markings, or characteristics. The supplied independent review
already checked every mathematical clause and edge case of the chart and theorem;
the current repair changes definition ownership and import availability only.


Current repair validation: `scompile.py` compiled every delivered file separately
against the live published library with no diagnostics: `StableFiberCurve` (14.3 s),
`StableVersalLevelChart` (27.1 s), and `StableLevelVersalBranchFreeness` (7.6 s).
The concrete helper has no postponed theorem or proof dependency.

The repaired `deliver2.py --no-push` passed server preflight and compilation:
`OK (dry run): commit 208d2809aaf passes the preflight and compiles; nothing pushed`.
Self-check also confirmed all three recorded signatures appear verbatim, every
new definition-node citation matches `stmt_deps`, all Lean lines are at most
100 characters, and the main node changes only in `lean` and `stmt_deps`.


## Reachability return repair (2026-10-22)

The saved packet passed the prescribed initial server dry run as commit
`9756e002494`, with all three delivered modules compiling cleanly. The self-check
confirmed exact recorded signatures, JSON layout, and Lean line widths.

The immutable-head return `b3e3fe16864c` specifically requires the two new
definition nodes to satisfy the global reachability invariant. Traversing the
current shared DAG from `coord/new-targets.txt` and former targets, with the
validator's unsplit-node cutoff, shows that the item itself is outside that
reach; its two new prerequisites inherit that status. Both are already cited
directly in the item's `stmt_deps`, and the chart also cites the fibre-curve node.
Adding artificial mathematical dependency edges would misstate the DAG.

To implement the return's explicit alternative, both new definition nodes now
carry `import_flags: ["unreachable"]`. This metadata repair changes no definition,
theorem, source statement, or dependency. It is the exception to the usual new-node
field list specifically requested by the reachability return. The final dry run
will check whether the delivery field gate accepts that required metadata.

Validation of the reachability repair: `deliver2.py --no-push` compiled all
three modules, then the server preflight rejected exactly the two added flags:

- `new node def-sfb-stable-fiber-curve: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`
- `new node def-sfb-stable-versal-level-chart: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`

This is a delivery-gate conflict: the independent incremental DAG validation
requires the flags while stage-2 preflight forbids workers from delivering them.
The saved flag-free packet passes preflight but reproduces the returned DAG
defect. The sandbox retains the concrete metadata repair for the maintainer;
no tool was modified, no artificial dependency was added, and nothing was pushed.


## Reachability gate retry (2026-10-22)

The prescribed initial retry of the retained packet ran
`deliver2.py NO lem-sfb-stable-level-versal-branch-freeness --no-push`.
It checked all three delivered Lean modules on the server and reached preflight,
which again rejected exactly the two `import_flags` fields:

- `new node def-sfb-stable-fiber-curve: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`
- `new node def-sfb-stable-versal-level-chart: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`

The wrapper reported base `c5a6c5562` and that sheaf-dag has moved on; the
preflight diagnostics contain no Lean or other packet defect. Both definition
nodes are still absent from the current shared source. The retained reachability
repair is unchanged: both have `import_flags: ["unreachable"]`. Removing those
flags would restore the exact defect returned at immutable head `b3e3fe16864c`.
The launcher's explicit rule requires a gate conflict to be reported as BLOCKED,
without patching or working around the gate. Nothing was pushed.


## Retained-packet retry and self-check (2026-10-22)

This retry began by reading the retained report and running the prescribed
`deliver2.py NO lem-sfb-stable-level-versal-branch-freeness --no-push` against the
current live repository. The wrapper checked all three Lean modules on the server,
then exited 1 at stage-2 preflight with exactly two findings:

- `new node def-sfb-stable-fiber-curve: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`
- `new node def-sfb-stable-versal-level-chart: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`

The two new nodes remain absent from the current shared DAG. Comparing the item
with the current shared node shows differences only in `lean` and `stmt_deps`.
The sandbox self-check passed: every recorded Lean signature occurs verbatim in
its owning module, JSON uses indent 1 with ensure_ascii false and a final newline,
and all Lean lines have at most 100 characters. Both new nodes retain exactly
`import_flags: ["unreachable"]`, as requested by the immutable-head reachability
return. No mathematical statement, construction, or dependency changed this retry.

The current validator source confirms the conflict: `tools/check_dag.py` requires
unreachable flags for nodes outside target reach; `tools/stage2_delivery.py`
rejects fields outside `NEW_NODE_KEYS`, which excludes `import_flags`. There is no
authorized packet-only repair that both retains the returned reachability fix and
satisfies this field gate. Removing the flags repeats the returned defect; tool
changes and artificial dependency edges are prohibited. The retained repair is
ready for a maintainer-side gate/metadata correction. Nothing was pushed.


## Dispatcher retry: persistent delivery-gate conflict (2026-10-22)

The prescribed initial retained-packet dry run was repeated against the current
live base. All three delivered modules passed its server compilation step.
Stage-2 preflight then exited 1 with exactly the same two diagnostics:

- `new node def-sfb-stable-fiber-curve: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`
- `new node def-sfb-stable-versal-level-chart: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`

Self-check confirms both nodes are still new on the current shared base, both
retain the return-required `import_flags: ["unreachable"]`, every recorded Lean
signature occurs verbatim in its owning module, all Lean lines meet the 100-character
limit, and the JSON layout is correct. The item differs from the shared base only
in `lean` and `stmt_deps`. No mathematical change is needed or justified by this
diagnostic. Removing the flags would undo the requested reachability repair.
The launcher explicitly forbids patching or working around a rejecting gate;
therefore this is an actual tool failure requiring maintainer-side reconciliation
of the field gate with incremental DAG validation. The repair is retained and
nothing was pushed.


## Final retained-packet retry (2026-10-22)

The prescribed first dry run of the saved packet was run again with
`deliver2.py NO lem-sfb-stable-level-versal-branch-freeness --no-push`.
It completed the server compilation step and exited 1 at preflight with exactly
the same two findings: each new definition node has `key(s) outside the rule:
import_flags (the maintainer’s fields come with the merge)`. Nothing was pushed.

The current shared base still lacks both new definition nodes. Self-check passed
for all three exact recorded signatures, indent-1 UTF-8 JSON with final newlines,
and Lean line widths. The item differs from the current base only in `lean` and
`stmt_deps`. Both new nodes retain `import_flags: ["unreachable"]`, implementing
the return on immutable head `b3e3fe16864c`. Reading the current validator sources
confirms that `tools/check_dag.py` requires these flags outside target reach,
while `tools/stage2_delivery.py` excludes them from `NEW_NODE_KEYS` and rejects
them. No authorized packet-only repair resolves these contradictory gates.
The repair remains retained for maintainer-side reconciliation; no tool was
modified and no artificial dependency was introduced.


## Current dispatcher retry (2026-10-22)

The required first dry run of the retained packet completed server checks of all
three Lean modules and failed stage-2 preflight with exactly two reasons:

- `new node def-sfb-stable-fiber-curve: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`
- `new node def-sfb-stable-versal-level-chart: key(s) outside the rule: import_flags
  (the maintainer's fields come with the merge)`

The sandbox self-check reconfirmed verbatim recorded signatures, indent-1 UTF-8
JSON with final newlines, and Lean lines at most 100 characters. Both nodes are
still absent on the current shared base; the item differs only in `lean` and
`stmt_deps`. The immutable-head return requires reachability repair, implemented
by the retained `import_flags: ["unreachable"]` on both new nodes.

Reading the current `tools/check_dag.py` lines 128–135 and
`tools/stage2_delivery.py` lines 513–517 and 544–546 confirms the incompatible
requirements: the former requires these flags outside target reach; the latter
rejects them as fields outside `NEW_NODE_KEYS`. The previous flag-free dry run
already reproduced the reachability defect. Removing the repair, inventing
dependency edges, or patching a tool would not be an authorized solution. This
retry therefore reports the concrete gate failure; the repaired packet is
retained for maintainer-side reconciliation. Nothing was pushed.

## Latest retained-packet gate check (2026-10-22)

The prescribed first dry run of this retry checked all three delivered Lean files
on the server, then exited 1 at stage-2 preflight with exactly two findings:
`new node def-sfb-stable-fiber-curve: key(s) outside the rule: import_flags`
and `new node def-sfb-stable-versal-level-chart: key(s) outside the rule:
import_flags`, both followed by `(the maintainer's fields come with the merge)`.
Nothing was pushed.

The current shared validator still requires `unreachable` in `import_flags` for
nodes outside target reach (`tools/check_dag.py`, lines 128–135); the current
stage-2 field gate still excludes `import_flags` from `NEW_NODE_KEYS` and rejects
it (`tools/stage2_delivery.py`, lines 513–517 and 544–546). Both new definition
nodes remain absent on the current shared base. The sandbox self-check passed
for indent-1 UTF-8 JSON with final newlines, all three verbatim Lean signatures,
and Lean lines at most 100 characters. The item differs from the current shared
node only in `lean` and `stmt_deps`.

The return-required flags are retained. Removing them would undo the immutable-head
reachability repair, and changing the gates or inventing dependency edges is not
authorized. This retry confirms the concrete tool conflict, with no mathematical
or Lean defect reported by the dry run.


## Verified delivery-gate failure (2026-10-22 10:00 UTC)

The prescribed initial retained-packet dry run completed its server Lean-file
checks, then exited 1 with `preflight FAILED (stage 2), 2 reason(s); do not push`.
Both reasons are `key(s) outside the rule: import_flags (the maintainer's fields
come with the merge)`, for `def-sfb-stable-fiber-curve` and
`def-sfb-stable-versal-level-chart`. Nothing was pushed.

The current shared validator still requires unreachable nodes to carry the flag
(`tools/check_dag.py`, reachability loop), while `NEW_NODE_KEYS` in
`tools/stage2_delivery.py` still excludes `import_flags`. Removing the flags would
undo the repair required at immutable head `b3e3fe16864c`. The launcher forbids
patching or working around a rejecting gate, so this is a concrete tool conflict.

The current-base self-check passed: both definition nodes are still new, the item
differs only in `lean` and `stmt_deps`, all recorded signatures occur verbatim in
the owning modules, JSON uses indent 1 with ensure_ascii false and a final newline,
and every Lean line is at most 100 characters. The two return-required flags and
all mathematical statements remain retained without changes.

## Current retained-packet repair check (2026-10-22)

The required first dry run again compiled the three delivered files on the server,
then exited 1 with exactly two preflight failures: `import_flags` is outside the
new-node field rule for `def-sfb-stable-fiber-curve` and
`def-sfb-stable-versal-level-chart`. The current return entry still identifies
immutable head `b3e3fe16864c` and requires those nodes to be reached or flagged.
Read-only inspection confirms `tools/check_dag.py` requires the flags outside
reach, while `tools/stage2_delivery.py` excludes them from `NEW_NODE_KEYS`.
The self-check passed exact Lean signatures, 100-character line widths, and
indent-1 JSON with a final newline. Both definition nodes remain new, and the
item differs from the current shared node only in `lean` and `stmt_deps`.
The concrete reachability repair remains in the sandbox. No tool was changed,
no artificial dependency was added, and nothing was pushed: the rejecting gate
requires maintainer-side reconciliation.

## Dispatcher gate confirmation (2026-10-22 10:05 UTC)

This retry began with the prescribed retained-packet `deliver2.py NO
lem-sfb-stable-level-versal-branch-freeness --no-push`. It checked all three
Lean files on the server and exited 1 at stage-2 preflight. Its two findings
reject `import_flags` on `def-sfb-stable-fiber-curve` and
`def-sfb-stable-versal-level-chart` as outside the new-node field rule.
Nothing was pushed.

Read-only inspection of the current shared tools confirms the conflict remains:
`tools/check_dag.py` requires the unreachable flag for nodes outside target reach,
whereas `tools/stage2_delivery.py` excludes `import_flags` from `NEW_NODE_KEYS`.
The return explicitly requires reachability or these flags, and earlier flag-free
validation reproduced the reachability failure. No tool patch or artificial
dependency is authorized. The retained metadata repair cannot pass this gate.

Current-base self-check passed: both definition nodes are still new; the item
differs only in `lean` and `stmt_deps`; all recorded signatures occur verbatim;
all JSON is indent 1, ensure_ascii false, with a final newline; all Lean lines
are at most 100 characters. The mathematical packet and required flags are retained.


## Retained repair validation (2026-10-22 10:07 UTC)

The prescribed first `deliver2.py NO
lem-sfb-stable-level-versal-branch-freeness --no-push` checked all three
Lean files on the server, then exited 1 with exactly two preflight findings:
`key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`
for `def-sfb-stable-fiber-curve` and `def-sfb-stable-versal-level-chart`.
Nothing was pushed.

Read-only inspection confirms `tools/check_dag.py` still requires unreachable
nodes to carry the flag, while `tools/stage2_delivery.py` excludes `import_flags`
from `NEW_NODE_KEYS`. The retained flags implement the immutable-head return
`b3e3fe16864c`; removing them undoes that repair. The launcher forbids editing
or bypassing the tools. This is a persistent delivery-gate conflict requiring
maintainer-side reconciliation.

Current-base self-check passed: both definition nodes remain new; the item
differs only in `lean` and `stmt_deps`; all three recorded signatures occur
verbatim in their owning modules; JSON has indent 1, ensure_ascii false, and
a final newline; all Lean lines have at most 100 characters. The mathematical
packet and the return-required flags remain retained.


## Retained-packet diagnostic (2026-10-22 10:14 UTC)

The prescribed initial `deliver2.py --no-push` checked all three Lean files,
then exited 1 with exactly two stage-2 preflight errors: `import_flags` is outside
the new-node field rule for `def-sfb-stable-fiber-curve` and
`def-sfb-stable-versal-level-chart`. Nothing was pushed.

Read-only inspection reconfirmed that `tools/check_dag.py` requires these
reachability flags while `tools/stage2_delivery.py` excludes them from
`NEW_NODE_KEYS`. Both nodes remain new on the current base; the item differs
only in `lean` and `stmt_deps`. Exact signatures, indent-1 UTF-8 JSON with final
newlines, and 100-character Lean line widths passed self-check. The required
metadata repair is retained; the conflicting delivery gate needs maintainer
repair. No tool or mathematical statement was changed.


## Current gate verification (2026-10-22 10:16 UTC)

The prescribed initial retained-packet dry run again exited 1 at server
preflight: both new definition nodes are rejected for `key(s) outside the rule:
import_flags (the maintainer's fields come with the merge)`. No push occurred.
Read-only inspection confirms the current reachability validator requires these
flags and the new-node field gate excludes them. Self-check passed for every
recorded signature, JSON layout, and Lean line width; the item differs from
the current shared node only in `lean` and `stmt_deps`. The return-required
flags remain retained. The tool conflict requires maintainer reconciliation;
no tool was modified or bypassed and no mathematical dependency was invented.


## Retained-packet preflight verification (2026-10-22 10:19 UTC)

The prescribed initial `deliver2.py NO
lem-sfb-stable-level-versal-branch-freeness --no-push` checked all three
Lean files on the server, then failed preflight with exactly two findings:
`key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`
for `def-sfb-stable-fiber-curve` and `def-sfb-stable-versal-level-chart`.
No push occurred.

Read-only inspection confirms that the current `tools/check_dag.py` reachability
loop requires `import_flags: ["unreachable"]` outside target reach, whereas
`tools/stage2_delivery.py` excludes `import_flags` from `NEW_NODE_KEYS` and rejects
it. Both definition nodes remain absent on the shared base. The item's current
base comparison changes only `lean` and `stmt_deps`. Self-check passed all three
verbatim recorded signatures, indent-1 UTF-8 JSON with final newlines, and
100-character Lean line widths. The reachability repair remains retained.
The conflicting field gate requires maintainer reconciliation; no permitted
packet-only repair was identified, and no tool or mathematical statement changed.


## Retained-packet dry run (2026-10-22 10:22 UTC)

The prescribed initial `deliver2.py NO lem-sfb-stable-level-versal-branch-freeness --no-push` checked all three Lean files on the server and exited 1 at preflight. Exactly two findings reject `import_flags` as outside the new-node field rule, one for each of `def-sfb-stable-fiber-curve` and `def-sfb-stable-versal-level-chart`. Nothing was pushed.

Read-only inspection reconfirmed the conflicting current gates: `tools/check_dag.py` requires flags outside target reach, while `tools/stage2_delivery.py` excludes `import_flags` from `NEW_NODE_KEYS`. The return-required metadata repair is retained. The current-base self-check passed exact recorded Lean signatures, indent-1 UTF-8 JSON with final newlines, 100-character line widths, and item changes restricted to `lean` and `stmt_deps`. Both definition nodes remain new on the shared base. No mathematical change or authorized packet-only repair resolves this gate conflict; no tool was edited or bypassed.


## Fresh retained-packet validation (2026-10-22)

The required initial `deliver2.py NO lem-sfb-stable-level-versal-branch-freeness
--no-push` checked all three Lean files on the server, then exited 1 with exactly
two stage-2 preflight errors: `key(s) outside the rule: import_flags (the
maintainer's fields come with the merge)` on `def-sfb-stable-fiber-curve` and
`def-sfb-stable-versal-level-chart`. Nothing was pushed.

The current shared source still lacks both definition nodes. Comparing the item
against the current shared node finds changes only in `lean` and `stmt_deps`.
All three recorded signatures occur verbatim in their modules; every Lean line
is at most 100 characters; all node JSON has indent 1, UTF-8 text and final
newlines. Both new nodes retain the return-required unreachable flags.

The current `tools/stage2_delivery.py` field gate excludes `import_flags` from
`NEW_NODE_KEYS` and rejects extra fields. The current `tools/check_dag.py` requires
`unreachable` in that field for nodes outside target reach, matching the return
on immutable head `b3e3fe16864c`. Removing the flags repeats the returned defect;
adding artificial dependencies or patching tools is prohibited. The concrete
metadata repair remains in the sandbox pending reconciliation of these gates.


## Successful retained-packet repair validation (2026-10-22)

The prescribed first dry run passed: `OK (dry run): commit 526c50bbb35
passes the preflight and compiles; nothing pushed`. All three delivered Lean
files passed the server compilation checks. The current base contains both
definition nodes with maintainer-assigned unreachable flags; their delivered
changes are only their Lean records. This resolves the reachability return
without a tool change or artificial dependency. The item changes only in `lean`
and `stmt_deps`. The retained-packet self-check passed every verbatim signature,
indent-1 UTF-8 JSON with final newlines, and the 100-character Lean line limit.
All mathematical statements and constructions are retained. Earlier gate-failure
entries above describe historical bases and are superseded by this successful
validation. The packet is delivered through the prescribed wrapper.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
