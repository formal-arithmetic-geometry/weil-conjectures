## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveFlatCoherentRanks` states
`AlgebraicGeometry.projectiveFlatCoherent_geometricCohomology_constructible` with one
`sorry` and no new definitions. The node's statement is unchanged.

Hypotheses and clauses:

- Schemes and the named morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Projectivity is `[IsProjective f]`, the recorded H-projective and quasi-compact
  convention, not an alternate projective-bundle convention.
- A Noetherian base is `[IsLocallyNoetherian S] [CompactSpace S]`: local
  Noetherianity plus quasi-compactness, exactly the two recorded dependency notions.
- The coherent module is `(G : X.Modules)` with
  `(hG : RingedSpace.IsCoherent X.toRingedSpace G)`.
- Flatness over the base through f is `(hflat : G.IsFlatOver f)`.
- Every nonnegative degree is covered by the arbitrary binder `(r : ℕ)`.
- For each `s : S`, the geometric point is explicitly
  `Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
  (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s`.
  The geometric fibre is `pullback f` along precisely this map.
- The geometric fibre module is the recorded `Scheme.Modules.tensorPullback` along
  `pullback.fst`; it is ordinary tensor pullback of G, not derived pullback or
  restriction to a different fibre.
- Coherent cohomology is `RingedSpace.moduleCohomology` of that fibre in degree r,
  applied to this pulled-back module. The result is initially a module over its
  global function ring. `ModuleCat.restrictScalars` along
  `((Scheme.ΓSpecIso (.of (AlgebraicClosure (S.residueField s)))).inv ≫
  (pullback.snd f ...).appTop).hom` supplies exactly its algebraic-closure scalar
  action. `Module.finrank` then renders the displayed dimension over that field.
- `∃ β : S → ℕ, (∀ s, β s = ...) ∧ (Set.range β).Finite ∧
  ∀ n : ℕ, Topology.IsConstructible {s : S | β s = n}` states exactly the finite
  constructible partition conclusion. The existential merely names the explicit
  dimension function: equality determines β pointwise. Its finite range ensures
  finitely many nonempty constructible level sets, disjoint and covering S.
  Conversely every finite constructible partition on which the dimension is
  constant gives this formulation. There is no extra semicontinuity conclusion.
  Proper coherent fibre cohomology is finite-dimensional under these hypotheses,
  so the natural-valued finrank is the dimension in the source.

Dependency declarations used, with modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms,
  `AlgebraicGeometry.Spec`, `Spec.map`, `Scheme.ΓSpecIso`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsProjective`, as recorded on def-pc-projective-morphism.
  This extracted upstream module is absent in the old local slopmaster2 snapshot;
  the matching original class and docstring were read in the group's
  `lean/Sheaf/AlgebraicGeometry/Morphisms/Projective.lean`. The recorded upstream
  import and declaration are available in the published server library, as the
  clean server compile confirms. No replacement class is defined or delivered.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (available through Noetherian).
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
  The dependency's recorded general pullback is usable by its documented explicit
  specialization, so no dependency module is needed.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`, available through DirectImage.Basic/Fiber.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`.
- `Sheaf.Paper.PQFCohomology`: the node pqf-def-cohomology's
  `sheafCohomologyAndHigherDirectImages` records the cohomological interpretation
  of `RingedSpace.moduleCohomology`, defined in its public import
  `Sheaf.Topology.RingedSpaceModuleCohomology`; this is the functor used here.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: `ModuleCat.restrictScalars`,
  available through DirectImage.Basic's imports.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`, the exact
  mathlib_match for def-weil-constructible-subset.

The proof-only imports are the recorded modules
`Sheaf.AlgebraicGeometry.PerfectComplex`,
`Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`,
`Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel`, and
`Sheaf.AlgebraicGeometry.FiniteFreeComplexHomologyUpperSemicontinuous`.
Mathlib's affine Noetherian-space theorem is already imported through Noetherian.
The projective perfect direct image and its base change nodes have no Lean records,
so no unavailable proof modules are imported. The docstring carries all five proof
steps, including field-extension invariance and the empty-base case.

Edge cases checked before writing: empty S (β has empty range; all fibres empty),
empty X (cohomology dimensions zero, with empty or singleton range), zero G (same),
r = 0 and degrees beyond the nonzero cohomology (ordinary coherent cohomology),
disconnected S with different dimensions (finite range, no local constancy imposed),
arbitrary characteristic (no restriction), and arbitrary common scheme universe u.
No nonemptiness, smoothness, field characteristic, connectedness, fixed relative
dimension, freeness or extra quasi-coherence hypothesis has been imposed.

Sources read: the item's blueprint node and its full five-step DAG proof;
`literature/stacks-project/perfect.tex`, lemma-jump-loci-geometric (0BDN) and
lemma-jump-loci (0BDI). The latter gives locally constructible level sets and
semicontinuity; the finite cover and finite term ranks give the finite range
required by this node over its Noetherian base.

Searches (2026-10-15):

- msearch LeanFinder: “For a projective morphism over a Noetherian base and a
  coherent flat module, geometric fibre cohomology dimensions are constructible”.
  Eight hits included `Module.isLocallyConstant_rankAtStalk`, finite scheme fibres,
  flatness, and Chevalley's theorem. No exact match.
- msearch Loogle: `Topology.IsConstructible, Module.finrank`: zero hits.
- msearch grep: `constructible|semicontinu` in AlgebraicGeometry: five hits in
  Morphisms/FinitePresentation about images of constructible subsets, no match.
- msearch LeanSearch: “Cohomology dimensions of geometric fibres of a projective
  morphism with a flat coherent sheaf are constructible”: unavailable, Internal
  Server Error. No conclusion inferred from this unavailable service.
- rg in the upstream project and lean/Sheaf for geometric cohomology, constructible
  dimensions, and finrank/moduleCohomology combinations: no exact statement.
- grep of the item's node id in upstream WeilConjectures: no occurrence.
- rg in upstream Cohomology for hFiber constructibility and semicontinuity found
  `Scheme.Modules.upperSemicontinuous_hFiber`; its full signature was read. It
  asserts semicontinuity of ordinary residue-field hFiber (an abelian-sheaf
  cohomology encoding), not the present finite constructible partition of coherent
  geometric-fibre cohomology, so it is not an exact existing declaration.
- DAG and project searches for constructible functions found no shared definition
  needed here: constructibility is expressed directly by finite range and the
  existing constructible-subset predicate. No new notion is defined.

Validation: scompile.py NW lem-fin-projective-flat-coherent-ranks compiled the
module cleanly on the server in 1.6 seconds, nice 19, two threads, limit 60 seconds.
All universes and variables are explicit. No node correction, new node, dependency
module, or STATEMENT-DISPUTED issue is needed.


## Second reading by NW

I independently read the node, its blueprint source, Stacks perfect.tex
`lemma-jump-loci-geometric` (0BDN) and `lemma-jump-loci` (0BDI), all statement
dependency records and the declarations they designate. No mathematical mismatch
was found; the module and node signature are retained unchanged.

Object/hypothesis/conclusion checklist (node order):

1. Schemes X and S, and the named morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   PASS. These are Mathlib schemes and scheme morphisms, not affine-only objects.
2. Projective f: `[IsProjective f]`. PASS. Read the recorded class through the
   available extracted source in `Sheaf/AlgebraicGeometry/Morphisms/Projective.lean`:
   it extends `IsHProjective f` and `QuasiCompact f`; H-projectivity is a closed
   immersion into projective n-space with the correct composite. The canonical
   upstream import is confirmed available by the server compile. This matches
   the node's H-projective convention.
3. Noetherian S: `[IsLocallyNoetherian S] [CompactSpace S]`. PASS. Read Mathlib's
   class (Noetherian rings on all affine opens), and the recorded equivalence
   with a Noetherian affine cover. CompactSpace means quasi-compactness without
   Hausdorffness. Together these say Noetherian scheme, with no separatedness
   added. Stacks 0BDN assumes proper finite presentation; projectivity over this
   base supplies these properties, rather than requiring additional binders.
4. Coherent O_X-module G: `(G : X.Modules)` and
   `(hG : RingedSpace.IsCoherent X.toRingedSpace G)`. PASS. Opened the shared
   definition: finite type, with finite-type kernel for every finite free map
   on every open. It is the dependency's coherent notion. Over this locally
   Noetherian X it gives the finite presentation used in Stacks 0BDN.
5. Flat over S through f: `(hflat : G.IsFlatOver f)`. PASS. Read DirectImage.Basic:
   sections on affine U over affine V are flat after restricting scalars along
   `f.appLE`. No flatness of the morphism f itself is assumed.
6. Each r >= 0: `(r : ℕ)`. PASS. Arbitrary degree precedes the existential naming
   the function; the finite partition is allowed to depend on r.
7. Each s and its geometric fibre: `∀ s : S`, with
   `Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
   (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s`, and
   `pullback f` along that map. PASS. Opened residueField/fromSpecResidueField
   and the general pullback declaration. This is exactly the dependency's
   documented specialization; the second projection is its structure map.
8. Fibre module G_bar_s: `(Scheme.Modules.tensorPullback (pullback.fst f ...)).obj G`.
   PASS. Opened tensorPullback and tensorPullbackObj: inverse-image module followed
   by extension of scalars and sheafification. This is ordinary module pullback,
   the prescribed common definition, with no substitute notion.
9. Coherent H^r and its dimension over kappa(bar s):
   `RingedSpace.moduleCohomology ... r` followed by `ModuleCat.restrictScalars`,
   then `Module.finrank (AlgebraicClosure (S.residueField s))`. PASS. Opened the
   shared globalSectionsFunctor and moduleCohomology definitions: evaluation in
   modules and its right derived functor. The ring map is the composite of the
   inverse ΓSpecIso and `(pullback.snd f ...).appTop`, hence maps the closure field
   into the fibre's global functions. RestrictScalars gives its exact scalar
   action, not an unrelated action. Finrank is Cardinal.toNat of rank; proper
   coherent cohomology here is finite-dimensional, so it is the displayed dimension.
10. Constructible function: `∃ β : S → ℕ, (∀ s, β s = ...) ∧
    (Set.range β).Finite ∧ ∀ n : ℕ, Topology.IsConstructible {s | β s = n}`.
    PASS. Pointwise equality determines β uniquely. The last two conjuncts give
    precisely a finite constructible partition by nonempty level sets. Opened
    Mathlib's IsConstructible: Boolean algebra generated by retrocompact opens,
    exactly the recorded dependency. Stacks gives locally constructible level
    sets; Noetherian quasi-compactness and finite local free ranks give the global
    finite partition required by the node. No extra semicontinuity is asserted.

Edge cases: S empty permits the empty function and empty range; no maximum or
nonempty chart is required in the signature. X empty and G zero give the zero
function (empty range if S is empty, otherwise singleton). Degree zero and all
higher natural degrees are covered; there is no positive-r restriction. Level
n = 0 and empty level sets are included. There is no index type, characteristic,
connectedness, smoothness or relative-dimension restriction. The arbitrary common
universe u is Mathlib's scheme/module convention and includes arbitrary sizes;
there is no small independent test-object universe or extra instance binder.

Independent H4 searches, with wording different from the worker's:

- LeanFinder through msearch: "finite stratification by dimensions of cohomology
  of a relatively flat coherent sheaf on a proper scheme". Eight results concern
  finite-type sheaves, presentations and limit sections; no exact theorem.
- Loogle through msearch: `Module.finrank, Topology.IsConstructible`: zero results.
- msearch grep: `hFiber|jump_loci|cohomology.*dimension`: eleven results, mostly
  preimageHomeomorphFiber, none matching this statement.
- Direct rg in upstream WeilConjectures, Mathlib/AlgebraicGeometry and this
  project's lean/Sheaf for hFiber and constructible/cohomology and finrank/cohomology
  combinations. Opened `upperSemicontinuous_hFiber`, its section hypotheses and
  `hFiber`: they concern upper semicontinuity of ordinary residue-field fibres
  using upstream Modules.pullback and finrankH. They neither state this finite
  constructible partition nor use the recorded coherent geometric-fibre encoding.
  DerivedFiberBetti concerns derived fibres of a complex, not this assertion.
- Checked the proposed full name and node id in dag/lean_names_upstream.json and
  upstream WeilConjectures: no existing declaration.

No new definition nodes or dependency modules are in this delivery. All shared
notions are usable, including the documented geometric-fibre specialization of
pullback. There is no statement correction and therefore no correction-citer audit.
The module contains only one theorem with whole proof `sorry`, no definitions,
private copies, local notation, local instances or hidden let/show binders.
Its module and declaration docstrings name the source and blueprint id, and the
proof docstring carries all five node steps with their dependency names. Lines
are within 100 characters and all universes/variables are bound. Unavailable
proof-only nodes remain listed in the worker report; the available proof modules
are imported. The node's lean.statement is verbatim the declaration signature.

Validation: independently compiled the sole delivered module with scompile.py
on the server: clean, 1.7 seconds, nice 19, two threads, 60-second limit. The first
invocation used a repository-relative path rather than the sandbox path and failed
before compilation; rerunning with the absolute sandbox file succeeded. No compiler
warning or mathematical repair was needed. Second reading adds this audit only.
