## Worker report

Existing declarations are used; no Lean module, definition node, dependency repair,
or statement correction is needed. The node's Lean record points to
`Sheaf.SixFunctors.ProperOpenProjectionMate`, with the two declarations
`AlgebraicGeometry.ProEtale.properOpenProjectionMate` and
`WeilConjectures.IntegralSystemRealization.properOpenProjectionMateSystems`.
The first signature is transcribed verbatim, including its explicit transport
factor. Its source was also checked against the live server with
`scompile.py --source Sheaf.SixFunctors.ProperOpenProjectionMate`.

The existing module is more general in its finite-coefficient parameters. We use
its specialization to the finite field and coefficient datum of this node, not
a change of that datum or of the node's statement. Both displayed equalities
have their two sides interchanged relative to this node; equality symmetry
changes neither their strength nor the morphisms compared.

Hypothesis and clause correspondence:

- The global datum is `F : WeilConjectures.FiniteFieldDatum`, with geometric field
  `F.k`. The system declaration binds `l`, `[Fact l.Prime]`, `l ≠ F.p`, `E`,
  `[Field E]`, `[Algebra ℚ_[l] E]` and `[FiniteDimensional ℚ_[l] E]` explicitly.
  The finite declaration specializes `Λ` to `Padic.coefficientExtensionRing l E n`
  for `1 ≤ n`. Its `Finite Λ` requirement follows from
  `Padic.finite_coefficientExtensionRing` in
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`. To use the displayed
  `Type (u+1)` coefficient convention one lifts this small coefficient ring;
  this is the standard module-sheaf size convention already used by the finite
  comparison interface. It does not change the coefficient ring or exclude a
  coefficient level.
- The square's `(U,V,W,Z,k₁,r,p,i)` is the existing signature's
  `(A,B,C,D,k,r,p,i)`. The system declaration has each scheme's `Over` structure,
  `LocallyOfFiniteType` and `QuasiCompact` structure morphism, and each arrow's
  `IsOver` instance. These are exactly finite-type schemes and morphisms over
  the fixed field. The finite theorem is applied to these same schemes.
- `[IsOpenImmersion k]`, `[IsOpenImmersion i]`, `[IsProper r]`, `[IsProper p]`
  are the four geometric properties. `h : k ≫ p = r ≫ i` is commutativity.
  There is no `IsPullback` hypothesis on this square in either theorem.
- The existing theorems require quasi-compact opens. These are consequences,
  not additional assumptions here: finite type over the Noetherian scheme
  `Spec F.k` makes all four schemes Noetherian. In particular `A` and `C`
  have Noetherian underlying spaces, and Mathlib's
  `AlgebraicGeometry.quasiCompact_of_noetherianSpace_source` gives
  `QuasiCompact k` and `QuasiCompact i`. This verifies every geometric premise
  of the existing identity for the node's inputs.
- In setting (a), `ProperOpenDerived Λ X` is the ordinary unbounded
  `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat Λ))`.
  `ProperOpenPull`, `ProperOpenPush` and `ProperOpenShriek` are respectively
  derived `upperStar`, derived `lowerStar`, and termwise exact open extension.
  These are the usual constant-module presentation of the ordinary operations;
  they are not a bounded constructible category. `ProperOpenTensor` is the
  published ordinary derived tensor. The actual pro-etale site is Mathlib's
  `Scheme.ProEt` with `ProEt.topology`.
- `properOpenProjection` is the published counit-defined
  `rightDerivedLowerStarProjectionMap`; `properOpenTensorIso` is the canonical
  open tensor map in the stated direction. `properOpenAdj` transports the
  canonical open adjunction to that same derived pullback. Thus the node's
  `π` and open `γ` are these exact maps, not arbitrary maps or isomorphisms.
- The fibre product is `pullback p i`, with `pullback.fst`, `pullback.snd`,
  and clopen lift `StrictTower.squareLift k r p i h`. The existing
  `properOpenAlpha` uses the canonical open base-change isomorphism, the
  clopen projection and the open/pullback compositors. `properOpenMate` is
  its proper-adjunction mate; `properOpenMateTensorMap` tensors its component
  with the identity of `N` and only inserts definitional composition casts.
- The finite map has exactly the node's open-adjunction normalization.
  Indeed, restrict its proper-adjunction mate to `i`, identify the restriction
  using the fibre product, factor `k=b s`, identify clopen extension and direct
  image, and apply the direct-image compositor. Open-unit normalization makes
  the base-change factor identity, and the clopen projection is identity on
  `s(U)`. Pasting the adjunctions leaves `S_r ε_r` following `η_r S_r`, hence
  identity by the triangle equation. Thus `λ P_i(properOpenMate)=1`. The open
  Hom bijection uniquely determines its adjunct to be `λ⁻¹`; consequently
  this is precisely the node's `Γ`. This is the comparison calculation in
  the node's Step 2 and existing module's Step 7, not an invertibility
  hypothesis on `Γ` or either projection map.
- The finite equality's left side is open `γ_i`, then `J_i(π_r)`, then
  `J_i S_r` applied to tensoring the pullback-square identification, then
  `Γ` at the resulting tensor input. The right side is `Γ_M ⊗ 1_N`, then
  `π_p`, then `S_p(γ_k)`. These are exactly the node's two routes, in Lean's
  left-to-right composition convention. The explicit
  `properOpenPullSquareIso` identifies `P_r P_i N` with `P_k P_p N`.
- In setting (b), `System l E X` abbreviates `coefficientSequenceDerived l E X`,
  the ordinary unbounded derived category of strict semilinear systems.
  `Operations.push`, `Operations.shriek`, `pull` and
  `(calculus l E X).systemClosed.tensor` are the recorded simultaneous
  operations on that category. Parameters `o` and `z : Realizations l E F o`
  supply the stipulated construction data, including their canonical maps
  and adjunctions; they are not extra assumptions on the input objects.
- The system theorem uses precisely `z.properOpen.gamma`. Its defining
  `ProperOpenCoherence.adjunct` field in
  `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` identifies
  its open adjunct with `(properOpenLambda ...).inv`. The definition of
  `properOpenLambda` in `Sheaf.SixFunctors.IntegralSystemOperations` is the
  exact composite requested: `cartesianConjugate`, `restrictFactor`, the
  clopen comparison, then direct-image composition. No alternate lift from
  finite-level morphisms is chosen.
- The system equality has the identical four factors and three factors,
  with the pullback-square transport written using
  `z.compositors.square` and the tensor bifunctor's `map`. It is an equality
  of morphisms in `System l E D` itself. There is no evaluation, scalar
  restriction, total inverse limit, normalization, boundedness,
  constructibility, finite Tor, or etale-origin premise on `M` or `N`.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorOperationDatum`,
  `WeilConjectures.SixFunctorOperationDatum`: fixes the overall context;
  this node uses its field and coefficient data, not its constructible domains.
- `def-weil-scheme-morphism-properties` is explicitly a convention record;
  the actual properties used are Mathlib `IsOpenImmersion`, `IsProper`,
  `LocallyOfFiniteType` and `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt` and its topology.
- `Sheaf.Paper.SemilinearDerivedSections`,
  `SemilinearSections.semilinearDerivedSections` and
  `SemilinearDerivedSectionsData`: ordinary derived system operations.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `Scheme.proEtaleConstantRingDerivedPullback`: the intrinsic constant-ring
  presentation of the ordinary pullback. The reused finite theorem uses the
  published equivalent constant-module-sheaf presentation instead of copying it.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`:
  canonical total K-flat tensor/pullback comparison, with independent site
  object and morphism universes.
- `Sheaf.SixFunctors.OpenTensorNormalization`,
  `SheafOfModules.openTensorNormalization`: normalized beta and open tensor
  maps for ordinary sites and ringed diagram sites, arbitrary unbounded inputs.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  `pullback.fst` and `pullback.snd`: the specified fibre-product geometry.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`,
  `IntegralSystemRealization.ProperOpenCoherence` and
  `integralCompactificationSystemRealization`: intrinsic system normalization.
  Only its unbounded operations and intrinsic-map clauses are used here.

The proof dependencies are already the imports and proof plan of the reused
module: the proper/open projection-mate theorem, Mathlib's adjunction mates
and mate pasting, Noetherian geometry, open normalization and the simultaneous
system calculus. No new postponed theorem or duplicate definition is introduced.

Edge cases: empty opens and empty schemes are allowed by the existing signatures
and clopen identity/zero construction. Identity opens and identity proper maps
use the normalized units and triangle identities. Level `n=1` is included;
`n=0` is outside the node's stated range. Arbitrary unbounded and zero input
complexes are included in both statements. Noncartesian squares are included;
no projection or proper/open isomorphism is inverted. The system identity is
intrinsic, so it does not assume faithfulness of evaluation on derived morphisms.

Searches actually made:

- `msearch.py leanfinder`: “Normalized proper open interchange commutes with the
  counit tensor projection maps on unbounded derived sheaves and semilinear
  systems”. Eight hits, including
  `SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app`,
  `SheafOfModules.Presentation.map_π_eq`,
  `HomologicalComplex.rightUnitor'_inv_comm`,
  `SheafOfModules.map_ιFree_mapFree_hom_assoc`,
  `SheafOfModules.ιFree_mapFree_inv_assoc`,
  `LightCondensed.ihomPoints_symm_comp`,
  `LightCondensed.free_internallyProjective_iff_tensor_condition`, and its
  primed variant; none states this geometric identity.
- `msearch.py loogle`: `CategoryTheory.Adjunction, "tensor"`. Ten hits,
  including `Adjunction.map_μ_comp_counit_app_tensor` and
  `Adjunction.unit_app_tensor_comp_map_δ`; these are generic monoidal adjunction
  facts, not this normalized geometric square.
- `msearch.py grep`: `proper.*open|interchange.*tensor` in `CategoryTheory`:
  no hits.
- `rg` of the project for proper/open and tensor/mate names found the reused
  `Sheaf/SixFunctors/ProperOpenProjectionMate.lean`, whose complete definitions,
  theorem signatures and proof docstrings were read.
- `rg` in `lean/WeilConjectures` for the item id and the exact reused names
  found no declaration; project implementations were inspected instead.

No node fault or STATEMENT-DISPUTED issue was found. Only `lean` is changed.

## Validation interrupted by published import collision

The resumed worker checked the sandbox and the current local delivery ledger/returns:
there was no recorded delivery result and no active delivery process for this item.
No push was attempted. The prescribed `deliver2.py --no-push` compiled its generated
probe, which imports only `Sheaf.SixFunctors.ProperOpenProjectionMate`, and failed
before preflight with:

```text
error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed,
environment already contains 'HomologicalComplex₂.secondFiltration.eq_1'
from Sheaf.CategoryTheory.DoubleComplexTotal
```

A separate prescribed `scompile.py` call on `scratch/CheckProper2.lean`, containing
only that single import and a check of the system theorem, reproduced the same
error (19.6 seconds). `scompile.py --source` confirmed that the live server's
module exposes the recorded declarations and retains its existing imports.
Searches of both library roots found these two declarations only in this module.
Thus removing unnecessary imports in the probe cannot fix this failure.

The source import paths converge inside the existing integral realization's
coefficient-comparison dependency chain. Both pass through
`FiniteFreeCompletedScalarComparison`, `ExtendedCechCompletionModel`,
`FunctorialRingComplexCechComparison`, `RingComplexGodementCech`, and
`FiniteOrderedFlasqueCechComparison`. One branch imports
`Sheaf.CategoryTheory.DoubleComplexTotal` directly; another passes through
`AlternatingCechTotalComplex`, `ModuleCechComparison` and the upstream
first-quadrant augmentation/total-comparison modules to
`WeilConjectures.CategoryTheory.DoubleComplexTotal`. These are library-internal
imports, not two imports introduced by this delivery. No matching upstream
replacement of the proper/open projection module or of that integral realization
chain was found. Repair requires the published library's duplicate-import
migration; no live source, artifact, launcher tool, or library module was edited.

The node record remains prepared as an existing-declaration delivery. It has
not passed validation and has not been delivered.

## Resume validation, 2026-10-19 12:58 UTC

The required first dry run was repeated after inspecting the retained report,
node, scratch probes and delivery ledger. It exited 1 after 38.4 seconds with
the same duplicate `HomologicalComplex₂.secondFiltration.eq_1` import error;
its output explicitly says nothing was pushed. The separately prescribed
`scompile.py NM lem-sf-proper-open-tensor-compatibility scratch/CheckProper2.lean`
(using the absolute sandbox path) also exited 1 after 19.6 seconds with that
same error. Both tool calls finished; neither remains interrupted or pending.

The live `scompile.py --source Sheaf.SixFunctors.ProperOpenProjectionMate`
request succeeded and confirms the existing declarations and imports are still
present. Current searches of `lean/WeilConjectures` and `lean/Sheaf` still find
both theorem declarations only in that owning module. The probe already has
only one import, so there is no second delivery import to remove and no smaller
owning module to select. Current source also confirms that
`FiniteOrderedFlasqueCechComparison` imports the old
`Sheaf.CategoryTheory.DoubleComplexTotal` directly while importing
`AlternatingCechTotalComplex`, whose `ModuleCechComparison` dependency forwards
to the upstream module. This collision is within the published library closure.
No sandbox statement edit can remove an import from that read-only closure;
duplicating its declarations would violate the one-definition rule. The
delivery remains blocked at the prescribed compiler validation, with the
prepared files retained and no push attempted.

## Resume validation, 2026-10-19 13:34 UTC

Started with the required `deliver2.py NM lem-sf-proper-open-tensor-compatibility
--no-push`. It exited 1, explicitly reporting nothing pushed, with the same
import collision at line 1 of its generated probe (5.0 seconds compiler time).
The prescribed independent `scompile.py` call on the retained
`scratch/CheckProper2.lean` also exited 1 with the identical collision
(48.1 seconds compiler time). That file imports only
`Sheaf.SixFunctors.ProperOpenProjectionMate` and checks its system theorem.
Both validations completed; no process remains pending.

Read the current owning module locally and via `scompile.py --source`.
Its finite and system theorem signatures and proof docstrings are still present.
A fresh search of both library roots finds the two theorem declarations only
in that module, so there is no smaller owning module or upstream replacement
to import. Inspected the current source chain: the flasque Cech comparison
imports `Sheaf.CategoryTheory.DoubleComplexTotal` and
`Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex`; the latter imports the
Sheaf module-Cech forwarder to `WeilConjectures.AlgebraicGeometry.ModuleCechComparison`,
whose first-quadrant dependencies bring in the upstream total complex.
The two DoubleComplexTotal sources still independently define secondFiltration.

Exact diagnostic from both prescribed tools:

```text
error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed,
environment already contains 'HomologicalComplex₂.secondFiltration.eq_1'
from Sheaf.CategoryTheory.DoubleComplexTotal
```

The authorized import-pruning repair is exhausted: the probe contains only
one import, and the collision is internal to its published closure. Repairing
that closure would require edits to read-only library modules outside this
existing-declaration delivery. No library source, artifact, or launcher tool
was edited, and no duplicate statement was introduced. Prepared node and report
are retained; delivery has not passed validation and nothing was pushed.

## Resume validation, 2026-10-19 13:39 UTC

Started with the prescribed dry run after reading the retained delivery.
`deliver2.py NM lem-sf-proper-open-tensor-compatibility --no-push` exited 1
with nothing pushed; its compiler reported the collision below (5.0 s).
The separate prescribed `scompile.py` on `scratch/CheckProper2.lean` exited 1
with the identical import failure (48.1 s). Both processes have completed.

```text
error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed,
environment already contains 'HomologicalComplex₂.secondFiltration.eq_1'
from Sheaf.CategoryTheory.DoubleComplexTotal
```

Re-read the current owning module and retrieved its live source using
`scompile.py --source Sheaf.SixFunctors.ProperOpenProjectionMate` successfully.
The recorded finite and system theorems remain in that module. A fresh search
of both library roots still finds their declarations only there. There is no
repair-note file for this item. The retained probe has one import only.

The current local source confirms the same internal diamond:
`Sheaf.Paper.FiniteOrderedFlasqueCechComparison` imports both
`Sheaf.CategoryTheory.DoubleComplexTotal` and
`Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex`. The latter imports
the `ModuleCechComparison` forwarder to the upstream module; the upstream
first-quadrant dependencies import
`WeilConjectures.CategoryTheory.DoubleComplexTotal`. Both total-complex
source files still define the same filtration declarations independently.
Thus pruning delivery imports or selecting a smaller owner cannot repair
this published-library failure. No read-only library file or launcher script
was changed, no duplicate theorem was introduced, and no push was attempted.
The prepared existing-declaration binding is retained for validation after
the published import collision is repaired.

## Resume validation, 2026-10-19 13:46 UTC

Started with the required dry run after reading the retained sandbox and stage rules.
`deliver2.py NM lem-sf-proper-open-tensor-compatibility --no-push` exited 1,
explicitly reporting nothing pushed, with the import collision below (5.0 s).
The prescribed independent `scompile.py` call on `scratch/CheckProper2.lean`
also exited 1 with that collision (48.1 s). Both processes completed.

```text
error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed,
environment already contains 'HomologicalComplex₂.secondFiltration.eq_1'
from Sheaf.CategoryTheory.DoubleComplexTotal
```

Retrieved the current owning module using
`scompile.py --source Sheaf.SixFunctors.ProperOpenProjectionMate`; it still
contains the finite and system statements and their normalization docstrings.
The retained node differs from the current repository node only in `lean`.
Read the current statement-dependency records. There is no repair-note file
for this item. A fresh search across `lean/Sheaf` and `lean/WeilConjectures`
finds the two recorded theorem declarations only in the owning module.
The independent probe contains exactly one import and one `#check`.

The current source still independently defines `secondFiltration` in both
DoubleComplexTotal modules. The flasque Cech comparison imports the Sheaf
version and the alternating Cech total complex; the latter imports the
module-Cech forwarder to the upstream module, whose first-quadrant imports
bring in the upstream total-complex implementation. Thus import pruning in
this delivery cannot remove the collision: it lies inside the sole owning
module's published closure. No smaller owning module or upstream theorem
replacement was found. No read-only library file, artifact, or launcher script
was changed, and no duplicate theorem was introduced. The prepared binding
is retained; validation failed and no push was attempted.

## Resume validation, 2026-10-19 14:24 UTC

Checked for an interrupted delivery before retrying: no item delivery/compiler
process was running and no item delivery result appeared in the repository
ledger or returns. The first resumed dry-run process was no longer accessible
after the provider interruption. Since it was explicitly `--no-push`, repeated
that dry run with output retained in `scratch/resume-dryrun.log`. The completed
result is exit 1, `COMPILE FAILED on the server, nothing pushed`, with:

```text
error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed,
environment already contains 'HomologicalComplex₂.secondFiltration.eq_1'
from Sheaf.CategoryTheory.DoubleComplexTotal
```

The separate prescribed single-import `scompile.py` probe also completed with
exit 1 and the identical error (48.1 seconds), recorded in
`scratch/resume-scompile.log`. No delivery or compiler process remains pending.
The live owning source was retrieved successfully through `scompile.py --source`
and its theorem signatures and normalization docstrings read again. Both exact
recorded declarations still have only the same owning module in searches of
`lean/Sheaf` and `lean/WeilConjectures`. There is no repair-note file. The node
copy still differs from the current repository node only in `lean`.

Current source confirms the internal import diamond described above:
`FiniteOrderedFlasqueCechComparison` imports the Sheaf double-complex module
alongside `AlternatingCechTotalComplex`; its module-Cech dependency forwards
to the upstream implementation whose first-quadrant chain brings in the
upstream double-complex module. Both independently define `secondFiltration`.
The probe has only one import, so pruning delivery imports cannot repair this
published closure, and neither theorem has a smaller owning module. No live
source or launcher tool was modified and no duplicate theorem was introduced.
The existing-declaration packet is retained; nothing was pushed.

## Interrupted-call recovery and latest validation

On this resumption the interrupted dry-run process handle was unavailable, and
process inspection confirmed that neither deliver2.py nor scompile.py remained
active for this item. The prior persisted logs contained failed compiler checks;
no delivery result or push was recorded. No delivery mutation was repeated.

The live source read through `scompile.py --source
Sheaf.SixFunctors.ProperOpenProjectionMate` succeeded. Fresh searches in both
Lean roots still locate both recorded theorem declarations only in that module.
Its import closure remains the published closure described above; selecting a
smaller owning module or deleting an extra probe import is unavailable.

The fresh prescribed `deliver2.py ... --no-push` completed with exit code 1
(4.0 seconds compiler time), explicitly saying nothing was pushed. The fresh
prescribed `scompile.py` on `scratch/CheckProper2.lean` also completed with exit
code 1 (4.3 seconds compiler time). Both report the identical sole-import failure:

```text
error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed,
environment already contains 'HomologicalComplex₂.secondFiltration.eq_1'
from Sheaf.CategoryTheory.DoubleComplexTotal
```

Full outputs are retained in `scratch/latest-dryrun.log` and
`scratch/latest-scompile.log`; the live source is retained in
`scratch/latest-live-source.txt`. No process is pending. The sandbox node and
existing-declaration report are retained, with no live repository, launcher tool
or compiled artifact edits and no push. The remaining blocker is the published
library import collision, outside the permitted sandbox repair scope.


## Continued validation, 2026-10-19 15:42 UTC

Read the retained packet and completed interrupted-call logs before retrying.
They record failed dry runs with nothing pushed; no pending item compiler or
delivery process was found. The fresh prescribed `deliver2.py NM
lem-sf-proper-open-tensor-compatibility --no-push` again completed with
`COMPILE FAILED on the server, nothing pushed` (4.0 seconds). Its exact
diagnostic remains:

```text
error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed,
environment already contains 'HomologicalComplex₂.secondFiltration.eq_1'
from Sheaf.CategoryTheory.DoubleComplexTotal
```

The output is retained in `scratch/current-dryrun.log`. The live source read
with `scompile.py --source Sheaf.SixFunctors.ProperOpenProjectionMate`
succeeded and still exposes both recorded theorem signatures and their
normalization docstrings. The retained independent probe contains just the
single owning-module import. The delivery wrapper necessarily generates
that same import for an existing-declaration binding. Thus no unnecessary
delivery import can be removed, and the published internal collision remains
the validation failure. Read-only library sources and launcher tools were
not changed; the sandbox remains retained and no push was attempted.

## Resume validation, 2026-10-19 15:51 UTC

Started with the required `deliver2.py NM lem-sf-proper-open-tensor-compatibility
--no-push`. The wrapper exited 1, explicitly reporting nothing pushed. Its
single-import generated probe failed before preflight (22.9 s) with:

```text
error: import WeilConjectures.CategoryTheory.DoubleComplexTotal failed,
environment already contains 'HomologicalComplex₂.secondFiltration.eq_1'
from Sheaf.CategoryTheory.DoubleComplexTotal
```

The independent prescribed `scompile.py NM lem-sf-proper-open-tensor-compatibility`
on the retained absolute `scratch/CheckProper2.lean` path reproduced precisely
that import error (4.3 s, exit 1). Both validation calls have completed.
The probe imports only `Sheaf.SixFunctors.ProperOpenProjectionMate` and checks
`WeilConjectures.IntegralSystemRealization.properOpenProjectionMateSystems`.

The live `scompile.py --source Sheaf.SixFunctors.ProperOpenProjectionMate`
request succeeded. Re-read both theorem signatures and their docstrings;
the retained Lean signature still matches the owner. Fresh searches in
`lean/Sheaf` and `lean/WeilConjectures` find the declarations only in that
owning module, with no smaller owner or upstream replacement. No item repair
note exists. Comparing the sandbox node to the read clone shows only `lean`
changed, as required.

Current source confirms the collision is internal to the published library:
`Sheaf.Paper.FiniteOrderedFlasqueCechComparison` directly imports
`Sheaf.CategoryTheory.DoubleComplexTotal` and
`Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex`; the latter imports
the module-Cech forwarder to the upstream comparison, whose first-quadrant
imports bring in `WeilConjectures.CategoryTheory.DoubleComplexTotal`. Both
total-complex source files still define `secondFiltration` independently.
Removing a delivery import cannot repair a probe already using the sole owner
alone. Repairing the published closure requires library changes outside this
read-only worker's authorized files. No library file, artifact, or launcher
script was edited; no duplicate declaration was added; nothing was pushed.
The prepared delivery remains retained pending the published import repair.


## Final validation after resumption

The retained interrupted-call logs report failed dry runs with nothing pushed; no prior successful delivery was recorded. The prescribed fresh dry run now passes both the server compilation and the maintainer preflight (commit 82d4de2d8d, nothing pushed). Thus the previously documented published import collision no longer blocks this packet. The current live owning module was read through `scompile.py --source`; its finite and intrinsic-system theorem signatures and normalization docstrings still agree with the retained binding and clause correspondence above. Only the item lean record differs from the shared node; there is no statement correction, new definition, or dependency repair. The lean record date is refreshed to the UTC delivery date.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
