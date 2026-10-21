## Worker report

The module `Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence`
states the item on the ordinary semilinear system categories already supplied by
`Sheaf.AlgebraicGeometry.VaryingRingOperations`. It defines the two specified
natural inverse comparisons by actual composites; the sole remaining theorem proof is `sorry`. The general scheme-isomorphism
equivalence theorem is imported and reused, rather than restated.
There are no new DAG nodes, dependency repairs, or statement corrections.

Hypothesis and conclusion correspondence:

- Arbitrary commutative coefficient rings and arbitrary adjacent transition maps:
  `R : ℕ → CommRingCat.{u + 1}` and `φ : ∀ n : ℕ, R (n + 1) ⟶ R n`.
  These are exactly the universes of the recorded operations. No flatness,
  finiteness, torsion, boundedness, or cartesianness condition is introduced.
- Ordinary system categories: `Modules R φ X`, not the derived category or a
  category of unrelated levelwise data. The inverse image is the recorded `pull`.
- Every scheme isomorphism `s : U ⟶ X`: explicit `{U X : Scheme.{u}}` and `[IsIso s]`
  in both new comparison definitions and the imported equivalence theorem.
- Equivalence of `s^*`: the imported existing `pull_equivalence` concludes
  `(pull R φ s).IsEquivalence`. It is available via `import all`; no new
  theorem with that statement is declared.
- The specified quasi-inverse is `(s⁻¹)^* = pull R φ (inv s)`. Its two whole-system
  natural isomorphisms are the actual definitions `pullIsoSourceComparison` and
  `pullIsoTargetComparison`. The former has type
  `pull R φ s ⋙ pull R φ (inv s) ≅ 𝟭 (Modules R φ X)` and the latter has type
  `pull R φ (inv s) ⋙ pull R φ s ≅ 𝟭 (Modules R φ U)`.
  Lean's `⋙` order is left-to-right, so these are respectively HF and FH in the node.
- Each comparison is precisely `(moduleGComp ...).symm`, then
  `eqToIso (congrArg (pull R φ) (IsIso.inv_hom_id s))` or the corresponding
  `IsIso.hom_inv_id s`, then
  `Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 _)) (modulePId R φ _)`.
  This last expression is the ordinary identity comparison already used in the
  recorded `gId` before localization. Neither comparison is an arbitrary chosen
  natural isomorphism. No triangle identity is asserted for these specified maps.
- The square has all four scheme vertices and all four maps explicitly bound:
  `k : V ⟶ W`, `r : V ⟶ S`, `p : W ⟶ T`, `i : S ⟶ T`.
  Its commutativity is `h : k ≫ p = r ≫ i` and its cartesianness is
  `hsq : IsPullback k r p i`. The extra spelling of commutativity supplies the
  actual proof parameter of the canonical lift; it adds no mathematical condition.
- The two horizontal maps are quasi-compact open immersions:
  `[IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]`.
  Properness of both vertical maps is `[IsProper p] [IsProper r]`.
- The chosen fibre product is `pullback p i` and its canonical lift `(k,r)` is
  `pullback.lift k r h`. This is definitionally the `StrictTower.squareLift` of the
  source helper, using the dependency's existing Mathlib construction directly.
- The last theorem concludes both `IsIso (pullback.lift k r h)` and
  `(pull R φ (pullback.lift k r h)).IsEquivalence`. Applying the two comparison
  definitions to that same lift, with the first conjunct as its `IsIso` instance,
  supplies exactly the same specified quasi-inverse comparisons for this case.

Dependency declarations inspected and used:

- `Sheaf.AlgebraicGeometry.VaryingRingOperations`:
  `AlgebraicGeometry.ProEtale.VaryingRing.Modules`, `pull`, `moduleGComp`,
  `moduleAdj`, `modulePId`; also read the defining normalization in `gId` and
  the sections characterization in `modulePId_existsUnique`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.lift` (with its projections and
  universal property); `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`:
  `CategoryTheory.IsPullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its quasi-compactness import:
  the recorded finite-type/quasi-compact conventions, here `AlgebraicGeometry.QuasiCompact`.
- Both statement-proof leaves are in `Mathlib.CategoryTheory.Equivalence`:
  `CategoryTheory.Equivalence.fullyFaithfulFunctor` (the Hom-bijection leaf) and
  `CategoryTheory.Functor.asEquivalence` (the equivalence criterion). Their full
  signatures, together with `Equivalence.mk`, were read. This module is public
  because `Functor.IsEquivalence` itself occurs in the delivered signatures.
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`:
  `CategoryTheory.Adjunction.leftAdjointIdIso`, already publicly imported by the
  operations dependency. Its actual signature and definition were read.

Source and edge-case checks:

Read Stacks Categories `definition-equivalence-categories` (001J) and
`lemma-equivalence-categories` (02C3), and More on Étale Cohomology
`lemma-shriek-proper-and-open` (0F7B). The last is the geometric context;
the ordinary equivalence argument uses only the specified natural isomorphisms.
Read the source helpers `pull_equivalence` and `lift_isIso` in
`VaryingRingProperOpenPasting.lean`; these are private but reusable through Lean
`import all`. The repaired module imports the existing `pull_equivalence` this way
without a file-local instance. It does not restate that theorem. The ordinary identity expression matches
the helper's private `moduleGId` verbatim in its construction.

The identity isomorphism is allowed: both equality transports and the identity
adjunction comparison still apply, without assuming strict equality of pullback
functors with identities. Empty schemes and zero coefficient rings are allowed;
there are no nonempty or nontrivial hypotheses. Nonflat and nonfinite transition
maps, for example ℤ/4 → ℤ/2, require no alteration of either comparison. The
cartesian-lift conclusion remains valid when a horizontal open is empty or is the
identity. Properness and quasi-compactness are retained even though the lift's
universal-property argument only needs cartesianness. The site and coefficient
universes are exactly the recorded ones; no equality of site object and morphism
universes is imposed. All variables and the universe are explicitly bound.

Searches for existing statements/definitions:

- `msearch.py`, LeanFinder: "Inverse image along an isomorphism is an equivalence
  on semilinear systems of module sheaves with specified composition and identity
  comparisons". Eight hits, including `SheafOfModules.pushforwardCongr`,
  `CategoryTheory.Equivalence.sheafCongr_inverse`, and `PresheafOfModules.isoMk`;
  none states this varying-ring item.
- `msearch.py`, Loogle: `CategoryTheory.Equivalence.mk,
  CategoryTheory.IsPullback.isoPullback`. Zero hits for the combined query.
  The generic equivalence constructors were subsequently read directly in source.
- `msearch.py`, grep: `pull_equivalence|lift_isIso|moduleGId|moduleGComp`.
  One unrelated Mathlib hit, `CategoryTheory.IsHomLift.isIso_of_lift_isIso`.
- `msearch.py`, LeanSearch: "A functor with a quasi inverse and natural
  isomorphisms on both composites is an equivalence". Eight generic hits,
  notably `Functor.IsEquivalence.mk'`, `Equivalence.mk`, and `Functor.asEquivalence`;
  these do not supply the geometric specialization or specified comparisons.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `pull_equivalence|lift_isIso|cartesianLift|pullIso`: only the source's private
  varying-ring helpers match the present notion; other hits concern fixed
  coefficient module objects, unrelated cartesian lifts, or unrelated pullIso maps.
- `grep -rn` for the item id in `lean/WeilConjectures`: no match.
- `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for each of the four proposed declaration names:
  no collision.

## Repair of return L (immutable head e91b66932cd7)

The return identifies `pull_isEquivalence_of_isIso` as identical to the existing
`pull_equivalence` in `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting`.
Confirmed against both the read-only local source and current server source,
fetched using `scompile.py --source Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting`.
Its complete binder context is:

```lean
universe u
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
private theorem pull_equivalence {U X : Scheme.{u}} (s : U ⟶ X) [IsIso s] :
    (pull R φ s).IsEquivalence := by
```

The statements mean the same thing: namespace, universes, coefficient maps,
ordinary system category and scheme map are identical. Removed the duplicate
entirely and removed its name from `lean.declarations`. Added
`import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` to reuse
its private `pull_equivalence` directly. This reuses the existing theorem
without proving or restating it. The cartesian-lift theorem's proof docstring now
names that imported theorem. The new comparison definitions retain their actual
compositor/equality-transport/identity data. No node statement changes.

## Second reading by Q23

Self-check performed directly; no other agent was started, as instructed. Re-read
the node, both new definitions, the retained theorem and the imported theorem with
its binders. The node's arbitrary rings and transitions are the shared `R, φ`;
no coefficient hypothesis was introduced. Both comparisons still have the required
whole-system functor types and the prescribed composites. The imported theorem
supplies the general equivalence assertion. The retained theorem still explicitly
binds all four schemes and maps, both open-immersion and quasi-compact hypotheses,
both properness hypotheses, the commutativity proof, and `IsPullback`. Its two
conclusions remain lift invertibility and inverse-image equivalence. The only
removed declaration was the redundant equivalence assertion identified by L;
the mathematical content of the packet is unchanged. Identity maps, empty schemes,
zero rings and nonflat coefficient transitions remain admitted.

## Validation of repair

First inspected the retained report and ran the required saved-packet dry run.
It failed before compiling this module: overlay
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` reports
`unknown module prefix 'Mathlib'`; server confirmation reports
`Live published library is unavailable`. No launcher or library files were modified.
The repaired packet is retried with the prescribed wrappers; their outputs are
the authoritative compile and delivery results.


Final repair validation: two `scompile.py` invocations and the repaired-packet
`deliver2.py --no-push` all failed before this module was reached. The server
compiler's exact diagnostic was a missing object file
`Mathlib/LinearAlgebra/TensorProduct/Basic.olean`; confirmation returned
`Live published library is unavailable`. The delivery wrapper printed
`COMPILE FAILED on the server, nothing pushed`. This is a published-build/tool
prerequisite failure, not an elaboration diagnostic in the delivered module.
The packet's static self-check passed: exact recorded main signature, duplicate
declaration absent from source and node record, and all Lean lines at most 100
characters. No push was attempted after the failed required dry run.

## Repair retry on 2026-10-21

Inspected the saved packet before running the prescribed initial dry run. The
existing duplicate repair is retained: `pull_isEquivalence_of_isIso` is absent,
and `pull_equivalence` is reused through `import all`. Re-read that theorem
and its explicit scheme, ring and transition-map binders in the current source.
Removed the unnecessary local-instance attribute: the retained statement has a
`sorry` proof and does not require instance registration. Refreshed the copied
node from the current read-only repository, retaining only the repaired `lean`
record, so generated `lean_audit` changes cannot leak into the delivery.

The initial dry run again failed before compiling this module: the overlay
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` imports a missing
`Mathlib/LinearAlgebra/TensorProduct/Basic.olean`, and server confirmation says
`Live published library is unavailable`. This is the same published-build
prerequisite failure seen in the preceding repair attempt. No source-library or
launcher-script mutation is authorized to repair the published server build.

Retry result: both the direct `scompile.py` and second `deliver2.py --no-push`
failed in prerequisites before this module. The second dry run names the missing
`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.olean` while compiling
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom` and again
confirms `Live published library is unavailable`. No push was attempted.
The static checks pass: the node differs from current main only in `lean`,
the signature is verbatim, the duplicate and local-instance attribute are absent,
all lines are within 100 characters, and the only postponed theorem has `sorry`.

## Saved-packet retry, 2026-10-21 04:23 UTC

Inspected the retained report and ran `deliver2.py Q23
lem-sp-varying-ring-cartesian-lift-pullback-equivalence --no-push` first, as
requested. Retained the existing duplicate repair. The current server source,
read with `scompile.py --source`, still declares the private `pull_equivalence`
with exactly the ring, transition, scheme and isomorphism binders quoted above.
The sandbox node differs from current main only in `lean`; its main signature
is verbatim, the duplicate declaration is absent, each line has at most 100
characters, all variables are bound, and the sole theorem proof is `sorry`.
The definitions and the cartesian theorem were reread against every clause;
identity and empty schemes and arbitrary coefficient transitions remain admitted.

This initial dry run failed in prerequisites before the delivered module:
local overlay `WeilConjectures.Algebra.Homology.HomComplexSectionsCochains`
timed out at 60 seconds. Server confirmation then failed in
`Sheaf/Paper/CoefficientHomRepresentativeEvaluation.lean:6:0`, reporting the
missing published object
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`.
The wrapper printed `COMPILE FAILED on the server, nothing pushed`.
A direct prescribed `scompile.py` retry follows; no launcher scripts, library
sources or build artifacts were changed.

Final result of this retry: the direct `scompile.py` and the second
`deliver2.py --no-push` both failed in
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation` on the same missing
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`.
Both server confirmations reproduce that error, before compiling the delivered
module. Thus the initial dependency timeout is no longer the blocker; the
published build artifact remains unavailable. The corrected packet is retained
in the sandbox. Nothing was pushed.

## Saved-packet retry, 2026-10-21 04:25 UTC

Read the retained report and ran the required initial `deliver2.py --no-push`
before further investigation. It failed before this module in
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation:6:0`: published object
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean` does not exist.
The direct prescribed `scompile.py` retry and its server confirmation reproduce
the same prerequisite failure. This is not a timeout or an elaboration error
in the delivered file. The wrapper reports `COMPILE FAILED on the server, nothing pushed`.

Retained the duplicate repair after reading current server `pull_equivalence`
with `scompile.py --source` and reading the operations declarations again.
Its binders still agree exactly with the removed theorem. The saved module
imports that theorem with `import all` and declares no duplicate. The item
differs from current main only in `lean`; the recorded main signature is
verbatim, all lines are at most 100 characters, and the sole postponed theorem
has `sorry`. Rechecked both comparisons against the prescribed compositors,
equality transports and identity comparisons. The cartesian statement retains
all four schemes and maps, both properness and open/quasi-compact hypotheses,
and both conclusions. Identity/empty schemes, zero rings and arbitrary
transition maps remain admitted. No Lean or node changes were needed.
No launcher scripts, source-library files or published build artifacts were modified.

The final `deliver2.py --no-push` retry failed on that same missing published
object; server confirmation reproduced it again. The repaired packet is retained,
and nothing was pushed.


## Saved-packet repair retry, 2026-10-21 04:28 UTC

Inspected the retained report and packet, then ran the prescribed initial
`deliver2.py --no-push`. It failed before this module in
`Sheaf.Paper.RestrictionOfScalarsExact`: the published object
`WeilConjectures/RingTheory/FaithfullyFlat/FamilyDescent.olean` is missing.
The server-source confirmation reproduced the same diagnostic.

Retained the repair of return L: the duplicate
`pull_isEquivalence_of_isIso` is absent and the module imports all of
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` to reuse its private
`pull_equivalence`. Read the current server source with `scompile.py --source`;
the explicit ring, transition, scheme and isomorphism binders remain exactly
those recorded above. Compared the sandbox node to current main: only `lean`
differs. Its main signature matches the file verbatim; all lines are at most
100 characters, all variables are bound, both comparison definitions have real
data, and the sole theorem proof is `sorry`. Re-read each hypothesis and clause
against the node: the specified composites, arbitrary coefficient transitions,
proper/open square, cartesianness, lift invertibility and equivalence are
retained, including identity maps and empty schemes. No new source edit is
needed for return L.

The direct prescribed `scompile.py` retry also failed before this module,
in `Sheaf.Paper.CoefficientRingedSequenceSite`, on missing published object
`WeilConjectures/SixFunctors/Etale/Derived/Hom.olean`. Server-source
confirmation reproduced that diagnostic. These are missing published build
artifacts, not errors in the retained module; library and launcher changes
are outside this worker's authorized write scope. A final dry run follows.

Final dry-run result: after waiting for concurrent dependency compiles,
`deliver2.py --no-push` failed before the delivered module in the server overlay
`Sheaf.CategoryTheory.RingedSiteDualityMaps`. At line 795, the equality
`(hβ i q h' hqi U x W φ).trans (hγ i q h' hqi U x W φ).symm`
has a component-expression type different from the expected composite with
`homComplexπ`. At line 828, `ringedSiteBidualDegree_eval` has a type using
`homComplexπ` where the goal uses `WeilConjectures.coefficientHomComponent`
and `β`. Both are upstream dependency type mismatches, not diagnostics in
this delivered module. The wrapper printed `COMPILE FAILED on the server,
nothing pushed`. No permitted change to this item can repair that shared
dependency source; the existing repair and the new diagnostics are retained.


## Saved-packet repair retry, 2026-10-21 04:35 UTC

Read the retained report and ran the prescribed initial `deliver2.py --no-push`
before changing anything. It fails before the delivered module in the server
overlay `Sheaf.CategoryTheory.RingedSiteDualityMaps`: type mismatches at lines
795 and 828. A direct `scompile.py` retry reproduces both diagnostics against
the same server snapshot, `95fe8449bb0472d0fb5c47544aef5f199bafc802ac4938eb2ebb3f54e7f22318`.
At 795 the component equality does not elaborate to the expected composite
with `homComplexπ`; at 828 the evaluation lemma uses `homComplexπ` and the
bidual map where the expected expression uses `coefficientHomComponent` and `β`.

Confirmed that this failure is already in the mandatory statement dependency:
`VaryingRingOperations` imports `SemilinearDerivedSections`, which imports
`SemilinearSystemsExistence`, which imports `RingedInternalHomShiftOfUniverses`,
which imports `RingedSiteDualityMaps`. Removing the import of the existing
proper/open theorem would not remove this prerequisite, and would undo return L's
required reuse. This is a shared dependency build failure; the brief forbids
editing its source or the launcher scripts. No such files were changed.

Retained the existing repair of L after rereading current server
`pull_equivalence` using `scompile.py --source`: its arbitrary `R`, `φ`,
scheme and isomorphism binders still match the removed duplicate exactly.
The sandbox declares no `pull_isEquivalence_of_isIso`. Compared the node with
current main: only `lean` differs. Verified the recorded main signature verbatim,
all lines at most 100 characters, explicit variables and universe, actual data
for both comparison definitions, and exactly one postponed theorem with `sorry`.
Reread the statement clause by clause: both ordinary comparison composites,
arbitrary rings and transition maps, all four schemes and maps, cartesianness,
both quasi-compact open and both proper hypotheses, and both lift conclusions
are retained. Identity maps, empty schemes, zero rings and nonflat transition
maps remain admitted. No further Lean or node repair is indicated by the return.
A final prescribed dry run follows; no push is permitted without its success.

Final dry run reproduces both `RingedSiteDualityMaps` type mismatches at
795 and 828 before this module, and prints `COMPILE FAILED on the server,
nothing pushed`. The repaired packet is retained.


## Current repair retry, 2026-10-21 05:46 UTC

Read the retained packet and ran the required saved-packet dry run first. It fails before this module on upstream `Sheaf.CategoryTheory.RingedSiteDualityMaps` type mismatches at 795:4 and 828:4 (overlay snapshot `fcf3d81923f39a93f40790da657d1c7172b3a0564784c7d1d9117dd13b53e8fb`). A direct prescribed `scompile.py` retry reproduces both diagnostics, also before reaching the delivered module. The first compares evaluation through a composite with evaluation through `homComplexπ`; the second compares the bidual-degree evaluation with `coefficientHomComponent` evaluation. These are upstream proof failures, not a missing notion or an unusable mathematical interface in this packet.

Retained the existing repair of L: no duplicate `pull_isEquivalence_of_isIso`; `import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` reuses the existing private `pull_equivalence`. Re-read the current server source via `scompile.py --source`; its binders and conclusion agree with the quoted signature. The current node and saved node differ only in `lean`; its main signature is verbatim, all Lean lines fit 100 characters, and the sole postponed theorem proof is `sorry`. Rechecked the two actual inverse-comparison definitions and every cartesian-square hypothesis against the unchanged node.

The mandatory `VaryingRingOperations` dependency itself transitively imports `RingedSiteDualityMaps`, so removing the extra proper/open-pasting import cannot repair the upstream failure and would discard the mandated theorem reuse. No shared source, launcher script or build artifact was changed. A final prescribed dry run follows.

Final dry-run result: `deliver2.py --no-push` again exits 1 with
`COMPILE FAILED on the server, nothing pushed`, reproducing the same two
upstream `RingedSiteDualityMaps.lean` type mismatches at 795:4 and 828:4.
The required direct compile and two dry runs therefore cannot reach this
module. The duplicate repair is retained; no delivery was pushed.

## Saved-packet retry, 2026-10-21 05:49 UTC

Inspected this report and ran the required initial `deliver2.py --no-push`
before making changes. It fails before the delivered module in upstream
`Sheaf.CategoryTheory.RingedSiteDualityMaps` at 795:4 and 828:4, with the
same two type mismatches in snapshot
`fcf3d81923f39a93f40790da657d1c7172b3a0564784c7d1d9117dd13b53e8fb`.
The prescribed direct `scompile.py` reproduces both errors. This is neither
a busy-server timeout nor an error in this packet's declarations.

Retained the existing repair of return L. Read current server source with
`scompile.py --source`: `pull_equivalence` still has exactly the explicit
universe, arbitrary coefficient rings, transition maps, scheme map and
isomorphism hypothesis quoted above. The saved module imports it with
`import all` and declares no duplicate. Compared the saved node with current
main: only `lean` differs. The recorded signature is verbatim; every Lean
line fits 100 characters; the two definitions have actual comparison data;
and the sole postponed theorem has `sorry`. Reread all proper/open-square
hypotheses, both conclusions, and both specified inverse comparisons.
Identity and empty schemes, zero rings and nonflat transitions remain allowed.

The mandatory operations dependency imports `SemilinearDerivedSections`,
then `SemilinearSystemsExistence`, then `RingedInternalHomShiftOfUniverses`,
which imports the failing module. Removing the proper/open-pasting import
cannot repair that prerequisite and would undo the required theorem reuse.
No library source, launcher script or build artifact was modified.

Final dry run also exits 1, reproducing both upstream type mismatches and
printing `COMPILE FAILED on the server, nothing pushed`. The duplicate
repair is retained; no delivery was pushed.


## Repair retry with dependency isolation, 2026-10-21

Ran the saved-packet dry run first. It reproduces upstream
`RingedSiteDualityMaps.lean:795:4` and `:828:4` type mismatches before
compiling this item. Confirmed the current server `pull_equivalence` source
using `scompile.py --source`; its explicit binders match the removed duplicate.
The existing `import all` reuse and both actual comparison definitions remain.
Refreshed the node from the current read-only repository, retaining only `lean`.
The recorded main signature, explicit universe and variables, 100-character lines
and sole `sorry` theorem pass static checks. No node statement changed.

A scratch import of just the mandatory `VaryingRingOperations` reproduces
the same transitive failure. A sandbox-only diagnostic copy of the failing
transitive module, with its two failing theorem proofs postponed, compiles
by itself, but full compilation then times out on upstream
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` before reaching
this item. Removed this diagnostic copy: `lem-sfb-ringed-site-duality-maps`
is not an item statement dependency, and replacing its existing proofs is
not an admissible stage-2 packet repair. No such module or node is included
in the delivery. No shared source, launcher script or build artifact was
changed directly. The retained mathematical packet is unchanged.

Self-reading again checks arbitrary rings/transitions, the two actual
compositor/transport/identity comparisons, every scheme and map, the
cartesianness, both quasi-compact open and proper hypotheses, and both lift
conclusions. Identity and empty schemes, zero rings and nonflat transitions
remain admitted. Final prescribed dry run follows.

Final validation: `deliver2.py --no-push` returned exit 0 and
`OK (dry run): commit ee6eaa478b6 passes the preflight and compiles; nothing pushed`.
Although the local overlay timed out on `CohomologyContinuity`, the wrapper's
current-server confirmation passed. This is the authoritative clean compile
and preflight of the retained target-only packet; the scratch dependency
experiment is not included. Proceeding with the prescribed delivery push.
