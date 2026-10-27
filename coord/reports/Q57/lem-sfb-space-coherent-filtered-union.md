## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentFilteredUnion` states
`AlgebraicGeometry.AlgebraicSpace.coherentSubobjects_filtered_colimit`, with its proof
postponed by `sorry`. Its three helper declarations construct the coherent-subobject
index, the inclusion diagram, and its canonical cocone. They contain actual data, not
postponed existence choices. There are no new DAG nodes or dependency-record changes.
The accepted Q50 stage-1 split and every node field other than `lean` are preserved.

Stage handoff: the inherited BLOCKED ending concerns stage-1 supersession. The current
`coord/brief-stage2.md` section 0 explicitly says that such an ending does not block
stage 2. The current `coord/queue.tsv` lists this item at stage 2 and the base node has
no Lean record. The Q50 report and accepted review were read; they contain a stage-1
split, not a duplicate Lean statement.

Hypothesis and clause correspondence:

- The scheme S is `{S : Scheme.{u}}`, and the algebraic space over S is
  `(X : AlgebraicSpace S)`. These are the existing scheme category and the existing
  full subcategory of fppf sheaves with representable diagonal and etale atlas.
- The locally Noetherian part of Noetherian is
  `hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)`.
  Thus every etale scheme chart, including non-quasi-compact charts, is tested.
- The quasi-compact part is `hqc : CompactSpace (Point X.obj.obj)`, using the existing
  field-valued point quotient and its existing algebraic-space topology.
- Absolute quasi-separatedness is `hqs`: for every two affine schemes over S with
  maps to X, `Point (Limits.pullback a b)` is compact. This is exactly the equivalent
  affine-pair criterion of Stacks 0AHR, spaces-properties.tex,
  lemma-characterize-quasi-separated, (1) iff (3). This avoids substituting relative
  quasi-separatedness over a potentially non-quasi-separated base S. The presheaf
  fibre product represents the usual scheme fibre product because X has representable
  diagonal. No relative separatedness or affineness of the atlas relation is added.
- A module is `(F : X.Modules)`, the existing module-sheaf category on the small etale
  ringed site. Quasi-coherence is `[F.IsQuasicoherent]`, Mathlib's existing local
  presentation predicate with the slice instances supplied by the dependency module.
- Coherent submodules are `CoherentSubobjects F`, the subtype of `Subobject F` whose
  underlying module satisfies `SheafOfModules.IsFinitePresentation`. This is an
  equivalent expression of precisely the node's chartwise coherence under hln:
  Stacks 07UB, spaces-cohomology.tex, lemma-coherent-Noetherian, identifies coherence,
  quasi-coherence plus finite type, finite presentation, and coherence on every etale
  scheme chart in clauses (1)--(4). The actual source was read at lines 1877--1905.
  There is no new predicate for coherence and no arbitrary family of coherent objects.
- Subobjects are Mathlib's isomorphism classes of monomorphisms into the fixed F.
  This is a set in the universe containing the objects and morphisms of X.Modules;
  no shrinking to the coefficient universe is assumed. The subtype inherits its
  partial order from `Subobject F`, and its arrows are inclusions.
- Nonemptiness is `Nonempty (CoherentSubobjects F)`; directedness is
  `IsDirected (CoherentSubobjects F) (· ≤ ·)`. In particular the empty index set is
  not silently allowed. No order or filteredness is assumed as an input.
- `coherentSubobjectDiagram F` is the monotone subtype-inclusion functor followed by
  `Subobject.underlying`, and `coherentSubobjectCocone F` has point F and legs
  `G.val.arrow`. Its naturality is the existing `Subobject.underlying_arrow` identity.
- The last conjunct supplies `c : ColimitCocone (coherentSubobjectDiagram F)` in the
  category X.Modules and asserts
  `IsIso (c.isColimit.desc (coherentSubobjectCocone F))`.
  This is the canonical map from the colimit to F, determined by the actual submodule
  inclusions. An existential colimit cocone simultaneously supplies existence and
  avoids adding an unavailable large-colimit typeclass as a hypothesis. For any
  other choice of colimit the map differs by the unique colimit isomorphism, so this
  says exactly that the canonical map is an isomorphism. It is stronger than mere
  existence of some unrelated isomorphism, as required by the node.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its locally affine
  structure and scheme morphisms (Scheme.lean, lines 35--48).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`, `etaleForget`,
  `Modules`, and the full signatures/docstrings of representable maps, structure
  sheaf, and module restriction. No replacement algebraic-space or ringed site is made.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its two
  etale-slice sheafification instances. Its Mathlib predicate
  `SheafOfModules.IsQuasicoherent` is used directly for F.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`; its signature and
  affine Noetherian-ring definition were read (lines 56--59).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: recorded declaration
  `Scheme.Modules.IsQuasiCoherentFiniteType` was read. It applies to scheme modules,
  and spells quasi-coherence plus finite type. Since our modules are on X_et, we use
  the underlying Mathlib predicates, with finite presentation by the source's 07UB
  equivalence. The literal scheme predicate is not applied to an algebraic space.
  The upstream true Stacks coherence definition `RingedSpace.IsCoherent` in
  `WeilConjectures.AlgebraicGeometry.Coherent` was read as well; no duplicate was made.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `ColimitCocone`,
  `IsColimit.desc`, and the chosen-colimit interface `colimit`/`colimit.desc`.
  The existential packaging uses the same universal property, without an extra
  colimit-existence assumption.
- `Mathlib.CategoryTheory.Subobject.Basic`: `Subobject`, `Subobject.underlying`,
  `Subobject.arrow`, `Subobject.underlying_arrow`; definitions and types were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point` and its topology;
  the existing point quotient is used for both compactness conditions.

Already stated proof dependencies are imported privately:
`WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`,
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`, and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
The atlas, relation, groupoid equivalence, groupoid approximation, space quasi-coherent
kernels/colimits, and coherent-support nodes currently have no usable module records;
they are not needed to type this stage-2 statement. No construction waits on them.

Sources: Stacks spaces-cohomology.tex, lemma-directed-colimit-coherent (07UV), both
paragraphs, lines 2649--2679; lemma-coherent-Noetherian (07UB), lines 1877--1905;
spaces-properties.tex definition-noetherian, lines 4155 onward, and
lemma-characterize-quasi-separated (0AHR), lines 133 onward. The theorem docstring
contains all five steps of the accepted node's natural-language proof, including
monicity and the inverse built from coherent images.

Edge cases checked before writing:

- F = 0: the zero subobject is coherent and the index is inhabited; no nonzero-module
  hypothesis is added. The canonical cocone still makes sense.
- X empty: all chart conditions and compactness are valid and the zero module category
  case is included; no point of X or chosen atlas is required in the statement.
- Non-affine/non-separated relation R: hqs imposes quasi-compactness only, not affineness
  or closedness of the diagonal. The proof route explicitly keeps this case.
- An arbitrary scheme base S: no Noetherianity, quasi-compactness, or separatedness of
  S is assumed. The affine-pair criterion is absolute and tests all scheme maps to X.
- Arbitrarily large quasi-coherent F: F need not be finitely generated, and the poset
  is not replaced by a finite family or by all coherent modules.
- Universes: u is explicitly bound; subobjects live in the available larger object
  universe rather than requiring the index to lie in Type u. All helper and theorem
  variables are explicitly bound with `autoImplicit false`.

Searches actually run for this delivery:

- `msearch.py ... leanfinder` with query "A quasi coherent module on a Noetherian
  algebraic space is the filtered colimit of its coherent submodules": eight hits,
  all general local-presentation/finite-presentation definitions and related instances;
  no algebraic-space theorem or canonical subobject-colimit theorem.
- `msearch.py ... loogle` with query `"IsQuasicoherent", "colimit"`: zero hits.
- `msearch.py ... leansearch` with query "A quasicoherent module on a Noetherian
  algebraic space is the filtered colimit of its coherent submodules": eight hits,
  including Mathlib quasi-coherence definitions and ModuleCat.FilteredColimits; none
  states this geometry theorem.
- `msearch.py ... grep` with query
  `coherent.*[Cc]olimit|[Cc]olimit.*coherent|[Qq]uasicoherent.*[Nn]oetherian`:
  four hits in condensed/coherent topology and filtered-colimit infrastructure;
  no matching theorem.
- `rg` in lean/WeilConjectures and lean/Sheaf for the node id: no hits.
- `rg` in both source trees for coherent filtered colimits and coherent subobjects:
  found scheme-only ModuleFilteredColimitFinitePresentation and
  NoetherianQuasicoherentSubmodules, not the algebraic-space theorem. Further searches
  over AlgebraicSpace modules found no coherence or Noetherian predicate to duplicate.
- `python3 tools/blueprint_refs.py search 'coherent filtered union'`: zero blueprint
  node matches. No new definition node was required.

No STATEMENT-DISPUTED issue or statement correction. The old stage-1 refusal is
resolved by the explicit stage-handoff rule; it is not reproduced as a tool blocker.

Validation: scompile.py compiles the file separately in sandbox and library module mode.
An initial naturality elaboration failed because unrestricted simp reduced the known
subobject identity to True before the diagram unfolded. Unfolding only the diagram,
removing the identity composition, and applying Subobject.underlying_arrow fixed it.
The subsequent server compilation was clean. Final dry-run and delivery results are
recorded below after running deliver2.py.

## Second reading by Q57

A separate second pass was performed in this worker, reopening the node, module and
source clauses. No other agent was started, as the dispatch brief forbids delegation;
this section does not claim an independent agent review.

I checked S, X, all three Noetherian hypotheses, F and its quasi-coherence, chartwise
coherence against 07UB, the subobject partial order, nonemptiness, directedness, and the
canonical comparison in order. The important distinction is absolute versus relative
quasi-separatedness: I retained the affine-pair test of 0AHR, valid over an arbitrary S.
The module's initial explanatory reference 03HB was corrected to 0AHR after reading
the tags table. The recorded pqf-def-coherent module was added as a public dependency;
its scheme-only predicate is not misapplied to X_et. The colimit existence is part of
the conclusion, and its comparison is fixed by subobject inclusions. Every signature
uses explicitly bound variables and the only postponed theorem is the recorded item.
No mismatch in the mathematical statement was found; no statement correction or
additional DAG record is made. The final library compile and maintainer preflight
remain independent checks of this delivery.

Final validation: the final-import version compiled cleanly in both modes via
scompile.py (1.8 s sandbox, 1.7 s library). The prescribed deliver2.py --no-push run
reported `OK (dry run): commit 8263bf4a8e2 passes the preflight and compiles; nothing
pushed`. No gate or launcher script was patched or bypassed.
