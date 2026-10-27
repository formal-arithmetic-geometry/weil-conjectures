## Worker report

Stage 2, Q79, 2026-10-24. The current item has no Lean record and is queued at stage 2.
The inherited BLOCKED ending concerns re-splitting an accepted stage-1 node; brief-stage2
§0 explicitly distinguishes this from recording its Lean statement. No accepted split
or mathematical statement is changed here.

The delivery adds RelativeRationalFlatRegularity.lean with the theorem
`AlgebraicGeometry.relative_rational_flat_regularity`, proof `sorry`, and the definition
module RelativeRationalMap.lean. The latter contains only real constructions, no sorries.
The theorem's docstring records all nine proof steps and their DAG dependencies.

The mathematical source was opened and read in the primary BLR scan named by the node:
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
PDF pp.61--64, printed pp.55--58. The definition of fibrewise density, relative rational
maps, and equivalence is on p.55; maximal-domain gluing and the graph description on
p.57; flat inverse-image domains and descent are Proposition 5 on p.58. No source-based
statement correction is needed. The Noetherian assumption already belongs to the node.

Hypothesis-by-hypothesis and clause-by-clause translation:

- Schemes S, X, X', Y are `{S X X' Y : Scheme.{u}}`, with one explicitly declared
  arbitrary universe. Specified structure maps are `sX`, `sX'`, `sY`.
- A finite affine cover of S by Noetherian rings is `[IsNoetherian S]`.
  Mathlib Noetherian.lean's `isNoetherian_iff_of_finite_affine_openCover` identifies
  this class with precisely that finite-cover condition. Its ring notion is the
  recorded `IsNoetherianRing`, not a new definition.
- Each smooth finite-type structure map has `[Smooth ...]`, `[LocallyOfFiniteType ...]`,
  `[QuasiCompact ...]`. The last two are the recorded definition of finite type.
- Y is separated over S as `[IsSeparated sY]`, whose field is exactly
  `IsClosedImmersion (pullback.diagonal sY)`. Absolute separatedness is not imposed.
- The new `Scheme.IsFibrewiseDenseOpen sX U` means
  `∀ s, Dense ((sX.fiberι s) ⁻¹' (U : Set X))`. These are scheme-theoretic fibres;
  `fiberι` identifies the inverse image with the base-changed open in the fibre.
- `Scheme.RelativePartialMap sX sY` supplies the open, its fibrewise density, its actual
  morphism, and the equation making it a morphism over S.
- `RelativePartialMap.Equiv` means agreement on a common fibrewise dense subopen.
  `Scheme.RelativeRationalMap` is `Quot` of that relation. The relation is itself an
  equivalence relation: reflexivity uses the same domain, symmetry reverses equality,
  and transitivity restricts to the intersection of the two common domains. Finite
  intersections of dense opens in each fibre remain dense. Thus `Quot`'s generated
  equivalence imposes exactly the specified equivalence, with no arbitrary choice.
- `RelativeRationalMap.domain` is the supremum of exactly all representative domains,
  so it is their union. `Represents` asserts fibrewise density, the base-map equation,
  and equality of the actual partial-map class.
- For each class φ, the first unique existential supplies a morphism on φ.domain,
  `φ.Represents φ.domain f`, restricting to every representative by
  `X.homOfLE h ≫ f = a.hom`. All domain-inclusion proofs h are quantified; none is an
  added assumption. The union definition ensures each such inclusion.
- Everywhere-defined representatives are written on the top open using
  `X.topIso.hom ≫ f`. The second conjunct states that two of these for φ are equal.
- The flat S-morphism is `p : X' ⟶ X`, `p ≫ sX = sX'`, `Flat p`.
  The unique existential ψ specifies the composite by `φ.IsComposite p ψ`:
  every representative on U pulls back to the canonical restricted composite
  `(p ∣_ U) ≫ a.hom` on `p ⁻¹ᵁ U`. In particular every such inverse image is
  fibrewise dense, and the class is independent of representative. This is a
  characterization of the canonical composite, not a freely supplied map or a
  stronger hypothesis asserting that the composite already exists.
- The domain equality is literally `ψ.domain = p ⁻¹ᵁ φ.domain`.
- Under `Surjective p`, existence of a representative on the top open of X' implies
  `∃! f : X ⟶ Y, φ.Represents ⊤ (X.topIso.hom ≫ f)`, the asserted unique global
  morphism on X.
- The final conjunct quantifies arbitrary `H`, `sH`, smoothness, local finite type,
  quasi-compactness, and an arbitrary open E in `pullback sH sX`. The second projection
  is the actual map `E.ι ≫ pullback.snd sH sX`. Every fibre is nonempty by
  `∀ x, Nonempty ((...).fiber x)`, and the conclusion is flatness, surjectivity,
  smoothness over S, local finite type over S, and quasi-compactness over S. The
  structure map is the actual composite through X. These properties allow the
  first conjunct to be specialized to X'=E, proving the stated application.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, its `Hom`, `Spec`,
  `Spec.map`; these are the records of def-pc-scheme and def-weil-affine-spectrum.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`; via the existing
  Mathlib.AlgebraicGeometry.Noetherian scheme interface.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`, as used by
  the existing separatedness class; Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat`.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions: the dependency's actual
  module, publicly imported. As its record directs, scheme products use the existing
  `Limits.pullback`, not its unrelated module-pullback functor.
- Mathlib.AlgebraicGeometry.Fiber: `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`, as exposed
  by that base-change module.

Recorded proof modules are imported privately: Mathlib Gluing, Proper, UniversallyOpen,
FlatDescent, the landed PointwiseFlatnessBaseChange, upstream Morphisms.Separated,
Morphisms.SchemeTheoreticallyDominant, Morphisms.SmoothFiber, and Pullbacks. The latter
supplies the recorded partial-section graph theorem; SchemeTheoreticallyDominant supplies
`Scheme.Hom.ker_pullback_snd` and `Scheme.Hom.image.pullbackIso` for the proof record that
lists declarations without a module. The generic finiteness and Noetherian Mathlib matches
are available through the statement imports. The unrecorded proof-only node
lem-sfb-smooth-fibrewise-dense-open-base-change has no module to import; no statement
notion depends on having its proof available, and the proof docstring names it explicitly.

Edge cases checked before writing:

- The empty source has its empty top open as fibrewise dense, and unique morphisms
  wherever a global representative is asserted. No nonempty-source assumption occurs.
- Empty fibres impose only density in an empty space. No surjectivity of structure
  maps is imposed. The empty H/product/open satisfies the final premise exactly when
  its projection really has nonempty fibres over every point (vacuously if X is empty).
- A flat p need not be surjective. Domain equality remains unconditional; only the
  descent clause uses surjectivity. In particular open immersions and identity maps
  are included.
- The base may be nonreduced. Neither X nor S is assumed reduced; relative fibrewise
  density and the separated-target graph argument are retained.
- Over a field, fibrewise density reduces to the expected density in the one fibre.
  The nonflat characteristic-2 base change of (T+1)/(T-1) from BLR p.55 is excluded
  precisely by flatness, not by a characteristic restriction.
- No integrality, irreducibility, absolute separatedness, faithful flatness in the
  domain-equality clause, or smoothness of p is imposed.

Searches (full wrapper responses are retained in searches.jsonl):

- leanfinder, "relative rational map maximal domain flat base change smooth schemes
  fibrewise dense open": eight hits, all ordinary Mathlib RationalMap or IsOver APIs.
  Opened Birational/RationalMap.lean: PartialMap uses ordinary `Dense` and maximal
  gluing requires reduced source and absolute separated target. It does not state this
  node or define relative fibrewise-dense rational maps.
- loogle, "AlgebraicGeometry.RationalMap, AlgebraicGeometry.Smooth, Dense": unknown
  first identifier; no hits. The actual nested name was found by semantic and grep search.
- leansearch, "Relative rational maps defined on fibrewise dense open subschemes":
  hits on ordinary partial maps, rational maps, representatives, restrictions and IsOver;
  no fibrewise version.
- msearch grep, "RelativeRational|FibrewiseDense|FiberwiseDense|RationalMap" in
  AlgebraicGeometry/Birational: ordinary rational-map modules only.
- rg on both project trees for RelativeRational, relativeRational, FibrewiseDense,
  FiberwiseDense, IsSDense, SDense: no definition. Grep for this item's id upstream:
  no attachment. Broader fibrewise-dense text search found unrelated purity/curve
  results, no relative rational-map implementation.
- rg on dag/nodes for relative rational maps, S-rational, S-dense found theorem
  nodes using the notion, including the item and its consumers, but no definition.
  `tools/blueprint_refs.py search relative rational` returned 35 broadly matching
  blueprint nodes, no matching definition. The ancestor command returns None,
  agreeing with the item's inherited null blueprint ancestor; that inherited ancestry
  and via-chain are preserved for the new definition node.

## New nodes

`def-sfb-relative-rational-map`: BLR 2.5, printed pp.55,57--58. Its module defines fibrewise
open density, genuine partial morphisms over S, agreement, quotient classes, the union
domain, representation, and the canonical characterization of pullback composition.
All data is constructed explicitly; there is no choice from an unproved existence theorem.
It cites only def-pc-scheme and def-pc-base-change. The searches above, also recorded
with their returned hits in mathlib_searches, distinguish this notion from Mathlib's
ordinary dense-open rational maps. The item's stmt_deps gains only this definition node.

## Second reading by Q79

I reread the item, the definition module, and the theorem module against the node. The
scheme maps, Noetherian and smooth finite-type hypotheses, separatedness, and all three
conclusions in the first conjunct are present verbatim in the theorem signature. The final
open-product clause binds the same H, sH, E, and nonempty-fibre hypothesis and returns the
five stated properties of the second projection. The new definition module introduces only
the fibrewise-dense open, relative partial map, its agreement quotient, maximal domain,
representation, and canonical pullback-composite predicate required by the item. I found no
statement mismatch or extra hypothesis.

## Validation

The definition module compiled successfully through scompile.py on 2026-10-24. The
first two-file compile failed while creating the server's private overlay with
`resource exhausted (error code: 28, no space left on device)`, before the theorem
module could be checked. A normal wrapper retry was started; the final result and
any dry-run failure will be recorded below. No compiler, delivery script, source
checkout, shared cache or server configuration was modified.

The second two-file scompile.py attempt failed identically after 6 seconds, still in
`private overlay Sheaf.AlgebraicGeometry.RelativeRationalMap`, with error code 28.
The prescribed deliver2.py --no-push attempt independently failed at the same private
overlay compile and printed `COMPILE FAILED on the server, nothing pushed` with the
same `no space left on device` diagnostic. Thus neither dry-run preflight nor theorem
compilation could complete. All drafted modules, both node records and this report
remain in the authorized sandbox. Both module files satisfy the 100-character limit.
This is a server compilation infrastructure failure, not the inherited stage-1 gate.

Retry handoff, 2026-10-24: inspected the saved report and modules and ran the
required first `deliver2.py Q79 lem-sfb-relative-rational-flat-regularity --no-push`.
It again exited 1 before preflight with `private overlay
Sheaf.AlgebraicGeometry.RelativeRationalMap`, `resource exhausted (error code: 28,
no space left on device)`, and `COMPILE FAILED on the server, nothing pushed`.
A direct prescribed two-file `scompile.py` retry independently exited 1 with the
same overlay and disk-space error after 6 seconds. No Lean or node files were
changed in this retry; the saved packet remains intact. The failure occurs in
server overlay creation, before theorem elaboration, and cannot be repaired by
changing the mathematical statement or sandbox module.

Retry handoff (attempt 4), 2026-10-24: inspected the saved report and ran the
required initial `deliver2.py Q79 lem-sfb-relative-rational-flat-regularity
--no-push`. It exited 1 before preflight with `private overlay
Sheaf.AlgebraicGeometry.RelativeRationalMap`, `resource exhausted (error code: 28,
no space left on device)` and `COMPILE FAILED on the server, nothing pushed`.
The direct prescribed two-file `scompile.py` retry also exited 1 with the same
private-overlay disk-space error after 6 seconds. No Lean or node files were
changed. The packet is retained; the server infrastructure failure occurs before
Lean elaboration and cannot be repaired within the sandbox.

Retry handoff (attempt 5), 2026-10-24: inspected the retained report and modules,
then ran the prescribed initial `deliver2.py Q79
lem-sfb-relative-rational-flat-regularity --no-push`. It exited 1 with
`COMPILE FAILED on the server, nothing pushed`: `private overlay
Sheaf.AlgebraicGeometry.RelativeRationalMap`, `resource exhausted (error code:
28, no space left on device)` after 6 seconds. A direct prescribed two-file
`scompile.py` retry also exited 1 after 6 seconds with the identical private-overlay
disk-space error. The failure precedes Lean elaboration and preflight; it cannot
be repaired by changing the mathematical packet. No Lean, node, launcher, shared
repository, cache, or server configuration files were changed. The packet is
retained in the authorized sandbox.

Retry handoff (attempt 6), 2026-10-24: read the retained report and ran the
prescribed initial `deliver2.py Q79 lem-sfb-relative-rational-flat-regularity
--no-push`. It exited 1 before elaboration or preflight with `COMPILE FAILED
on the server, nothing pushed`: `private overlay
Sheaf.AlgebraicGeometry.RelativeRationalMap`, `resource exhausted (error code:
28, no space left on device)` after 6 seconds. A direct prescribed two-file
`scompile.py` retry independently exited 1 after 6 seconds with the same
private-overlay disk-space failure. The mathematical packet is retained without
Lean or node changes. Only this sandbox report was updated; no launcher, shared
repository, cache, or server configuration files were changed.

Retry handoff (attempt 7), 2026-10-24: inspected the saved report and both
modules, then ran the required first `deliver2.py Q79
lem-sfb-relative-rational-flat-regularity --no-push`. It exited 1 with
`COMPILE FAILED on the server, nothing pushed`: `private overlay
Sheaf.AlgebraicGeometry.RelativeRationalMap`, `resource exhausted (error code:
28, no space left on device)` after 6 seconds. The prescribed direct two-file
`scompile.py` retry independently exited 1 with the identical overlay creation
error after 6 seconds. Both failures precede Lean elaboration and preflight.
No mathematical packet changes can repair this server disk-space failure.
The saved Lean modules and node records remain unchanged; only this sandbox
report was updated. No launcher, shared repository, cache, or server
configuration files were changed.

Retry handoff (attempt 8), 2026-10-24: after the required initial dry run, I waited one
minute and reran deliver2.py --no-push. It again failed before preflight while creating the
private overlay for Sheaf.AlgebraicGeometry.RelativeRationalMap with `resource exhausted
(error code: 28, no space left on device)`. The direct prescribed scompile.py run then
failed on the definition with the same overlay error; compiling the theorem alone reported
the expected missing RelativeRationalMap. Local files have no overlong lines, and no source,
launcher, shared repository, cache, or server configuration was modified.

Retry handoff (attempt 9), 2026-10-24: inspected the retained report and both Lean
modules, then ran the required initial `deliver2.py Q79
lem-sfb-relative-rational-flat-regularity --no-push`. It exited 1 with
`COMPILE FAILED on the server, nothing pushed`: `private overlay
Sheaf.AlgebraicGeometry.RelativeRationalMap`, `resource exhausted (error code:
28, no space left on device)` after 6 seconds. The prescribed direct two-file
`scompile.py` retry independently exited 1 with the identical overlay error after
6 seconds. Both failures occur before theorem elaboration or preflight. The
saved Lean modules and node records are retained unchanged. Only this sandbox
report was updated; no launcher, shared repository, cache, or server
configuration files were changed. Server overlay storage must be repaired before
the prescribed validation and delivery can proceed.

Retry handoff (attempt 10), 2026-10-24: inspected the retained report and both
Lean modules. The required initial `deliver2.py Q79
lem-sfb-relative-rational-flat-regularity --no-push` exited 1 with
`COMPILE FAILED on the server, nothing pushed`: `private overlay
Sheaf.AlgebraicGeometry.RelativeRationalMap`, `resource exhausted (error code:
28, no space left on device)` after 6 seconds. A direct prescribed two-file
`scompile.py` retry independently exited 1 with the identical overlay error after
6 seconds. Both failures precede Lean elaboration and preflight. No mathematical
packet edit can repair server overlay storage. The saved modules and node
records remain unchanged; only this sandbox report was updated. No launcher,
shared repository, cache, or server configuration files were modified.

Retry handoff (current session), 2026-10-24: inspected the retained report, both
Lean modules and node records, then ran the required initial `deliver2.py Q79
lem-sfb-relative-rational-flat-regularity --no-push`. It failed before elaboration
or preflight in `private overlay Sheaf.AlgebraicGeometry.RelativeRationalMap`
with `resource exhausted (error code: 28, no space left on device)` after 6 seconds.
A direct prescribed two-file `scompile.py` retry independently failed with the
identical server overlay storage error after 6 seconds. The current repository
item matches the retained node outside the authorized lean/stmt_deps fields; both
Lean files retain the 100-character line limit. The saved mathematical packet is
unchanged. Only this sandbox report was updated; server storage repair is required
before compilation, preflight and delivery can proceed.

Repair validation, 2026-10-24: after the server overlay became available, the required
`scompile.py` compile exposed a stale public import of
`Mathlib.AlgebraicGeometry.Morphisms.Surjective`; that file is absent from the live
Mathlib tree, while `AlgebraicGeometry.Surjective` is already available through the
existing imports. I removed only that import. The prescribed two-file compile then
completed successfully: both `RelativeRationalMap.lean` and
`RelativeRationalFlatRegularity.lean` compiled with no errors or warnings (the theorem's
`sorry` warning is accepted by the stage contract).
