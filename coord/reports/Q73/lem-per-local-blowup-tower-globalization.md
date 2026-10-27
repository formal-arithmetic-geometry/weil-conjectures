## Worker report

Item: lem-per-local-blowup-tower-globalization. Group Q73, stage 2, 2026-10-24.
Module: `Sheaf.AlgebraicGeometry.LocalBlowupTowerGlobalization`.

The four theorem declarations jointly render every paragraph of the node:
`exists_localBlowupTower_globalization`,
`localBlowupTower_globalization_ambient`,
`localBlowupTower_globalization_flat`, and
`localBlowupTower_globalization_ambient_flat` (all in `AlgebraicGeometry`).
All four proofs are `sorry`. Each has its matching node id, source and detailed
natural-language proof docstring. No definition contains `sorry`, and no theorem
is proved. No statement correction or disputed statement is needed.

### Hypothesis and clause correspondence

- Schemes and maps are `X P : Scheme.{u}` and `p : P ⟶ X`, with one explicitly
  bound universe `u`. `[IsNoetherian X]`, `[IsNoetherian P]`, `[IsReduced P]` and
  `[IsProper p]` are exactly the initial hypotheses. Mathlib's
  `isNoetherian_iff_of_finite_iSup_eq_top` identifies `IsNoetherian` with the
  stipulated finite affine Noetherian cover; no separation of X is added.
- The finite set is `(S : Set X) (hS : S.Finite)`. `hinc` states pairwise
  non-specialization in both directions, hence precisely incomparability.
  `(r : ℕ) (hr : 1 ≤ r)` and `hdim` specify the common local-ring Krull
  dimension. `ringKrullDim` is the supremum of prime-chain lengths.
- `Scheme.localSpectrumPullback p S` is literally the coproduct over `s : S`
  of `pullback p (X.fromSpecStalk s.1)`. `localSpectrumPullbackMap` is the
  coproduct descent of its first projections. These use actual stalk rings,
  not residue fields or neighborhoods. The set subtype stays in universe u.
- `L : OrdinaryBlowupTower (...)` is the given synchronized finite ordered
  local tower. The existing structure retains its finite length, all levels,
  transition maps, exact ideal centers and isomorphisms to ordinary blowups.
  `hcoh` uses `RingedSpace.IsCoherent ... (L.center i).toModules`, including
  the finite-type-kernel condition. `hred` is reducedness of each center
  subscheme; `hnd` is nowhere-density of its support. Since supports are
  closed, `IsNowhereDense` means they contain no nonempty open subset.
- `hsupp` says the range of each local center's composite to X lies in S.
  On its s-component, every point of Spec O_X,s maps to a generalization
  of s. Incomparability forces a member of S in this range to be s itself;
  the closed point of Spec O_X,s is the unique such point. Thus this is
  exactly support over the closed local base points, not a restriction to
  closed points of X. It imposes no extra scheme structure on the center.
- The main existential supplies `G : OrdinaryBlowupTower P` and
  `LocalClosure p S L G`. This extends the existing
  `OrdinaryTowerCartesianMap`: equal lengths, cartesian squares at every
  level, commuting arrows and equality of all pulled-back center ideals.
  `closure_center` additionally says the global ideal is
  `(L.center i).map (map i.castSucc)`, definitionally the kernel of the
  local-center map to the global stage. This is the smallest closed
  subscheme through which it factors, so no arbitrary extension is used.
- The main geometric conjunction gives coherent global ideals, reduced
  centers and nowhere-density. It is stated for every center, harmlessly
  including the empty scheme. The image formula is exactly the union of
  closures of the active members `S ∩ Set.range (G.centerToBase i ≫ p)`.
  The next clause quantifies over component-generic points of that image
  (as points of its subspace) and gives local-ring dimension r.
- `CentersSchematicallyDenseOver p S G` is schematic dominance of the
  coproduct of the center's actual local base changes. This renders
  determination of functions by those local schemes. Inactive s have empty
  restrictions, so using all S is the same as using the generic image points.
- The last main clause compares G to every H satisfying the same closure
  prescription, using the existing exact-center cartesian comparison over
  the identity of P; nonemptiness and subsingleton give unique comparison.
  It is independence of spreading neighborhoods, without asserting
  uniqueness for arbitrary extensions with extra components elsewhere.
- The ambient theorem repeats the node hypotheses and takes
  `[IsNoetherian M]`, `(j : P ⟶ M) [IsClosedImmersion j]`, `(m : M ⟶ X)`
  and `hp : j ≫ m = p`. `AmbientLift G j` supplies the ambient ordinary
  tower and closed inclusions of the intrinsic levels. Its `center` is
  the schematic image along that closed inclusion, and `center_restrict`
  gives the exact intrinsic ideal. `strictIso`, `strict_toSource` and
  `strict_toAmbient` identify each intrinsic next stage with the actual
  `IdealSheafData.strictTransform` over both projections. Composing the
  intrinsic cartesian local comparison therefore gives every prescribed
  local iterated blowup and all its empty stages.
- For `[IsNoetherian X'] (f : X' ⟶ X) [Flat f]`, the flat theorem gives B
  over `pullback p f` and an uncontracted `OrdinaryTowerCartesianMap` to G.
  `FullCenterImageBaseChange` says the kernel of the full pulled-back local
  center map is the extended global ideal, stage by stage. The source is
  `pullback (I.subschemeι ≫ j) (pullback.fst q f)`, precisely the full
  D ×_X X' via pullback associativity. No radical or reduction occurs.
- The optional contracted comparison is `OrdinaryResolutionComparison`;
  its `retained_ideal` and `deleted_iff_unit` retain original ordering and
  delete exactly unit-ideal (empty-center) stages. In particular a
  nonempty Cartier-center isomorphism cannot be contracted. The primary
  comparison keeps every stage.
- `Scheme.genericSupportPoints f (closure S)` is the set of generic points
  of the subspace `f ⁻¹' closure S`. Since S is finite, closure S is the
  union of the closures of its members. S' is quantified with precisely
  the finiteness stipulated in the node. `CentersSchematicallyDenseOver`
  is the extra condition, and `LocalReconstruction` says both that all
  closure ideals are recovered and that an uncontracted local tower
  realizes that reconstruction. The second implication states that
  reducedness of all pulled-back centers suffices for density. There is
  no claim that a general flat map preserves reducedness or the integer r.
- The ambient-flat theorem supplies B, an ambient lift A', an intrinsic
  cartesian comparison b and an ambient one a. Its `HEq` clause expresses
  the commuting square of closed inclusions; heterogeneous equality only
  bridges the equal-length Fin casts, not a weakened equality of maps.
  The ambient `FullCenterImageBaseChange` clause keeps exact ideals.
  Generic-local density then gives both intrinsic and ambient
  `LocalReconstruction`. The same reduced-center sufficient condition and
  the same unit-stage contraction comparison are included.

### Dependency declarations and interfaces read

Every original statement dependency was read with its node and full recorded
signature/docstring. They are used as follows:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; its `IsNoetherian` class and
  finite affine cover equivalence supply the explicit global Noetherian form.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (separated, universally closed, locally finite type;
  universal closedness supplies quasi-compactness).
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced` and its stalkwise equivalence.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup`, `blowupMap`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, publicly
  exposing `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`. The full finite-type-kernel
  condition is used, not merely the quasi-coherent/finite-type conjunction.
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` supplies
  `IdealSheafData.toModules`, the actual sheaf-kernel construction.
- `def-nagata-strict-transform`: `WeilConjectures.Compactification.StrictTransform`,
  `AlgebraicGeometry.strictTransform`, `strictTransformToSource`,
  `strictTransformMap`, and `IdealSheafData.strictTransform`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` and the stalkwise equivalence.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`.
  Scheme pullbacks and coproducts come from Mathlib's geometry limits.
- `def-nagata-scheme-theoretic-image`:
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, `Scheme.Hom.image` and
  `Scheme.Hom.ker`; `IdealSheafData.map I j` is definitionally
  `(I.subschemeι ≫ j).ker`. `IsSchemeTheoreticallyDominant` is ker = bottom.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.

The landed definition `def-trf-ordinary-resolution-rule` supplies
`OrdinaryBlowupTower`, `toBase` and `OrdinaryResolutionComparison` in
`Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`. The landed definition node
`def-per-ordinary-tower-cartesian-map` owns `OrdinaryTowerCartesianMap` in
`Sheaf.AlgebraicGeometry.OrdinaryTowerCartesianMap`. It is extracted unchanged
from NormalizedTowerRegularPullback; the theorem is no longer imported or cited
as a statement dependency. The contracted `OrdinaryResolutionComparison` is
used only for the explicitly permitted contraction clauses, since its
`deleted_iff_unit` field forces deletion of unit stages.

Proof imports include ReducedSchemeImage, ReducedNoetherianBlowupGeometry,
Blowup.Proper, Blowup.FlatBaseChange, StrictTransformBlowup, localization flatness
and topological Noetherian components. The live server source was read for
`Sheaf.AlgebraicGeometry.FlatMaximalDominanceBaseChange`; its recorded theorem
is `AlgebraicGeometry.flat_maximalDominance_and_baseChange`.
`lem-sfb-scheme-image-flat-base-change` resolves through its closed audit to
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`,
`Scheme.Hom.ker_pullback_snd` and `Scheme.Hom.image.pullbackIso`;
`thm-nagata-blowup-flat-base-change` resolves through its closed audit to
`WeilConjectures.Blowup.FlatBaseChange`, `IdealSheafData.blowupFlatBaseChangeIso`.
These exact signatures/docstrings were read and their modules imported.

### Edge cases checked

The empty S is allowed: its local coproduct is empty, and all global closure
ideals are the unit ideal. Length zero has no center condition and is retained.
Empty P and empty X are permitted. Individual empty component centers and
entirely empty synchronized stages stay in both cartesian comparisons.
At r = 1 the dimension equality is unchanged; r = 0 is excluded precisely by
the node, not implicitly. Reducible P and zero divisors are allowed. No field,
characteristic-zero, excellence or equidimensionality assumption is introduced.
A flat map missing the entire support has empty S' and empty pulled centers.
A nonreduced flat pullback is compared as a full ideal, and receives no
reducedness conclusion; generic-local reconstruction still requires density.
Nonempty Cartier centers can produce isomorphisms but are never deleted.
For dense restrictions, ker = bottom is actual schematic density, not just a
topological assertion. The ambient need not be reduced or proper over X.

### Searches and sources

- `msearch.py ... leanfinder` query: “A finite tower of blowups with reduced
  centers on local schemes globalizes by taking schematic closures of centers”.
  Eight hits, mostly normalization; none states this theorem.
- `msearch.py ... loogle` query `AlgebraicGeometry.Scheme.IdealSheafData.blowup`:
  zero hits (unknown identifier in the external index). Follow-up query
  `AlgebraicGeometry.Scheme.Hom.ker, AlgebraicGeometry.Scheme.fromSpecStalk`:
  zero hits. The exact upstream constructions were instead read locally.
- `msearch.py ... leansearch` query: “Finite ordered blowup tower cartesian
  comparison retaining empty centers and equality of center ideals”. Eight hits,
  including the unit-ideal empty-subscheme fact, but no globalization theorem.
- `msearch.py ... grep` query `[Bb]lowup|[Bb]lowUp|[Bb]lowing` in
  `AlgebraicGeometry`: zero hits in the Mathlib index.
- `msearch.py ... grep` query
  `OrdinaryTowerCartesianMap|localSpectrumPullbackMap|IsClosureGlobalization`:
  zero Mathlib hits.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for blowup towers
  found OrdinaryResolutionRule and NormalizedTowerRegularPullback, reused here;
  normalized/log/saturated tower statements are different. Direct search for
  the node id in WeilConjectures found no statement. Candidate new declaration
  names were searched in both trees and dag/lean_names_upstream.json: no collision.
- `tools/blueprint_refs.py search 'ordinary blowup tower'` found no blueprint
  node matching that phrase. DAG grep found the existing ordinary resolution
  rule and cartesian-comparison owning nodes. Thus helpers here concern this
  single closure-globalization interface; no missing independent notion or new
  definition node is required.
- Read the current blueprint ancestor
  `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/`
  `sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md` and the
  accepted local-globalization split. The current item is an auxiliary lemma,
  not the unit statement.
- Opened the node's online source:
  https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf
  (arXiv:0904.1592v2). Read 2.1.5--2.1.6, 2.2.1--2.2.8, Lemma 2.2.1,
  4.2.1 and Lemmas 4.2.4--4.2.5. In particular empty blowups are the only
  trivial stages; pro-open closure pushing forward is characterized by
  density, and ambient pushing forward uses strict transforms. The archival
  WANTED status is preserved. No external quotation is copied in the module.

### Verification

`scompile.py Q73 lem-per-local-blowup-tower-globalization` compiled all three
repair modules together in a private server overlay. Library compiles were
clean: OrdinaryTowerCartesianMap 1.6 s, LocalBlowupTowerGlobalization 2.7 s,
NormalizedTowerRegularPullback 2.4 s; their sandbox compiles were clean too.
Both implicit-binding options are false in the new definition and item module;
the unchanged normalization module has autoImplicit false. All variables and
universes are bound. All Lean lines are at most 100 characters. Earlier dry runs rejected the extraction packet. Maintenance has now landed
the prerequisite extraction separately; the current packet contains only this
item and imports the landed definition. See the repair note below.

## Second reading by Q73

Read the finished module again against every paragraph of the node. The local
support condition is over local closed fibers, not closed points of X;
incomparability verifies its equivalence. `LocalClosure` retains the existing
cartesian comparison and adds schematic-image ideals. Main geometry includes
coherence, reducedness, nowhere-density, the active base image formula, pure
codimension and schematic density. Ambient strict transforms are tied to both
projections. Full flat pullback and generic-local reconstruction are distinct,
and the latter has exactly the density condition with reducedness sufficient.
All original hypotheses are repeated in the separately named clause theorems.
No arbitrary tower or canonical morphism is chosen from a sorry theorem.
The second pass replaced two inferred support carrier types with explicit
stage types after a compiler error, and included both intrinsic and ambient
unit-stage contraction comparisons. No mathematical statement was changed.

## Repair of returned delivery H13

Maintenance committed the required prerequisite extraction on the server in
324d85f0b19ebfec5643d9ac6b430462d8d5505e. The unchanged
`AlgebraicGeometry.OrdinaryTowerCartesianMap` signature and all five fields
now belong to `def-per-ordinary-tower-cartesian-map`, in
`Sheaf.AlgebraicGeometry.OrdinaryTowerCartesianMap`. Its node records the
retained source/search evidence and ILO VIII 2.1.7--2.1.9 provenance.
`NormalizedTowerRegularPullback` imports this definition, removes the old
structure, and its node adds the definition dependency and removes the moved
name from lean.declarations while retaining its existing provenance.
Both prerequisite modules compiled individually with tools/lean_file.sh,
60 seconds per file; incremental DAG validation passed before the server
commit under coord/.merge.lock.

The item's mathematical statement and its four theorem signatures are unchanged.
This packet now contains only LocalBlowupTowerGlobalization.lean and its item
node: stmt_deps names the landed definition and ordinary-resolution rule,
and contains no normalization theorem. The item imports the definition owner.
The return required exactly that ownership repair; OrdinaryResolutionComparison
still serves only the contraction clauses because deleted_iff_unit forces
deletion of all unit stages. The five-field uncontracted comparison retains
all stages, including empty centers and length zero, with full extended ideals.

## New nodes

None in this packet. def-per-ordinary-tower-cartesian-map is already landed
by the prerequisite maintenance commit named above.

## Dependency modules

None in this packet. The normalization module and its required node update
are already landed together. Their former sandbox copies, the definition
module and node, and the old report were retained as adjacent
.maint-Q73-1792824291.bak files, outside delivery discovery.

## Maintenance handoff

The prior blocker was a packet-contract conflict: after removing the unused
theorem dependency, normalization is outside the item's prerequisite closure;
its module was rejected as unowned, and deliver2.py filtered its stmt_deps
update. Landing the explicitly authorized prerequisite extraction separately
resolves this item without changing protected tools. Rebase on the maintenance
commit, retain only the item packet, and use the ordinary dry run and delivery.
The maintenance REPORT.md contains the full investigation and tool follow-up.


## Repair of returned delivery 8f78e91a8c8c: centerToBase ownership

Removed the duplicate `AlgebraicGeometry.OrdinaryBlowupTower.centerToBase`
and its entry in lean.declarations. Publicly import its existing owner,
`Sheaf.AlgebraicGeometry.CodimensionResolutionPrefix`, and add the landed
`def-per-codimension-resolution-prefix` to stmt_deps. No new definition node,
replacement definition or renamed copy is supplied.

The prescribed `scompile.py --source` lookup now returns the live module.
Read its full signature, docstring and owning node. Its definition takes a
base scheme X, a tower A on X and an index i, and returns the morphism
`(A.center i).subschemeι ≫ A.toBase i.castSucc` into X. It has no
quasi-excellence, rationality, nonempty-center or resolution hypothesis;
those belong to other declarations in its module. Its provenance is Temkin
§4.1.3, blueprint def-per-codimension-resolution-prefix.

The former helper additionally accepted a morphism p from the tower base.
Every use now explicitly composes the existing declaration with that p:
`G.centerToBase i ≫ p` for global centers, and
`L.centerToBase i ≫ Scheme.localSpectrumPullbackMap p S ≫ p` for local
centers. CentersSchematicallyDenseOver uses the same existing declaration.
The composites are equal to the former maps by associativity. Thus hsupp,
the base-image formula, its pure-codimension clause, all four theorem
hypotheses and the schematic-density predicate retain their exact meaning.
No natural-language statement or other hypothesis/conclusion changes.
Empty centers, length zero and empty schemes still give the same unique
composite morphisms, so this reuse imposes no new restrictions.

The second reading of this repair checked the actual existing signature,
all eight theorem occurrences and the density definition against their
former expressions. The only mathematical interface change is reuse of
the existing center-to-base map with explicit final composition. Previous
source-unavailable failures are superseded by the successful source lookup;
validation of this repaired version is recorded below.

### Validation of this ownership repair

The prescribed scompile.py compiled the existing CodimensionResolutionPrefix
overlay, the sandbox module, and the library-named
Sheaf.AlgebraicGeometry.LocalBlowupTowerGlobalization module successfully.
There were no errors or unexpected warnings; the library-named file took
3.3 seconds. The dependency and sandbox totals include slot acquisition.
The item record contains the revised theorem signature verbatim and no
centerToBase declaration owned by this delivery.
