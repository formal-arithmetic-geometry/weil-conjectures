## Worker report

The statement is `AlgebraicGeometry.RiemannZariski.birational_riemann_zariski_neighbourhoods`
in `Sheaf.AlgebraicGeometry.BirationalRiemannZariskiNeighbourhoods`. Its sole proof is
`sorry`; its docstring reproduces all fourteen DAG proof steps. The definition module
`Sheaf.AlgebraicGeometry.BirationalValuationNeighbourhoodData` has real data throughout,
no postponed proof and no chosen map. The original statement is unchanged.

Hypotheses and the objects of the statement:

- `Z : Scheme.{u}` is the scheme; `[IsIntegral Z]` includes nonemptiness and domain
  coordinate rings, exactly the recorded `def-pc-integral-scheme`.
- `[CompactSpace Z]` is quasi-compactness, with no Hausdorff hypothesis.
  `[QuasiSeparatedSpace Z]` says intersections of compact opens are compact.
- `Z.functionField` is the actual stalk at `genericPoint Z`, not a separable closure.
  `Z.fromSpecStalk (genericPoint Z)` is its canonical generic-point map.
- The existing `RiemannZariski.Model Z Z.functionField ...` has an integral source,
  a proper map to Z, a specified dominant generic map from this very field, and the
  commuting generic triangle. These data already encode the compatible identification
  of its function field with F. Indeed its canonical stalk map k(M) -> F is injective;
  the map from Z gives F -> k(M), whose composite to F is the identity. Injectivity
  then gives the opposite composite identity as well. Thus no extra proper models
  with a different function field are quantified over.
- The existing `QuasiModel` has the same generic-factorization data and instances
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on its structure map.
  Hence it encodes the separated finite-type birational quasi-models in the node.
- The existing `ValuationPoint Z Z.functionField ...` remembers the actual subring
  `v.V : ValuationSubring Z.functionField`, the map `v.centre : Spec v.V -> Z`, and
  `v.fac`, the required equality on the generic fibre. `ValuationSubring` uses
  a-or-inverse membership and has F as fraction field. In particular this does not
  identify distinct centres on a nonseparated base.

Clauses of the statement, in the order of the Lean conjunction:

1. `∀ v M, ∃! l, l ≫ M.map = v.centre ∧ Spec.map ... ≫ l = M.generic`
   is precisely unique lifting to every proper birational model, including both
   factorization and agreement with the specified generic map.
2. `valuationTopology ... = ⨅ M, TopologicalSpace.induced ...` characterizes the
   topology stipulated in the node. The quantified `c` is required to consist of
   the actual closed-point images of valuative lifts. The preceding unique-lift
   assertion guarantees these projections exist and are uniquely determined.
   The actual topology is constructed without this choice as `generateFrom` of
   the open model cylinders; the equality identifies it with the stipulated
   coarsest topology. The topology is not a parameter or a discrete substitute.
3. `@CompactSpace ... (valuationTopology ...)` is (i).
4. For every `U : QuasiModel ...`, `@IsOpenEmbedding ... (ValuationPoint.push U)`
   is (ii): it gives a homeomorphism onto an open range for exactly the map induced
   by composition. Both topologies are the actual model-cylinder topologies.
5. `Nonempty (AffineValuationColimit v (fun _ ↦ True))` is all of (iii).
   Its `I : Type u`, `Preorder`, `Nonempty`, and `IsDirected` give a small filtered
   ring index and a small cofiltered opposite for the affine neighbourhoods.
   Mathlib's `isFiltered_of_directed_le_nonempty` and `isCofiltered_op_of_isFiltered`
   supply those category properties. `N` consists of actual affine opens on proper
   models with lifts; `cofinal` says every affine neighbourhood is refined by the
   chosen family. Thus the system represents all neighbourhoods through a small
   cofinal family. `AffineValuationRefinement` consists of actual morphisms of the
   models and their restrictions to the opens, respecting the valuation and
   generic maps. `ringDiagram` uses their pullbacks on coordinate rings.
   `intoV_injective` identifies these coordinate rings with subrings of O;
   `transition_injective` gives the injective transitions; `intoV_compat`
   makes them inclusions inside O and F. `fractionField` is `IsFractionRing`
   for the actual map `intoField`, and so is the common fraction field F.
   `ring_colimit : IsColimit ...ringCocone` is the categorical ring colimit
   assertion with its specified maps into O. `union_eq` also writes the directed
   union assertion elementwise. No arbitrary ring maps or abstract colimit object
   replace the specified ones.
6. `AffineValuationColimit v (fun N ↦ N.AboveWithin M ⊤)` is restriction to models
   dominating any prescribed M, retaining the whole colimit and injectivity data.
7. For every prescribed M, its actual valuative lift l, and open W containing its
   closed-point image, the last clause supplies
   `AffineValuationColimit v (fun N ↦ N.AboveWithin M W)`. `AboveWithin` requires
   a model morphism to M mapping the whole affine neighbourhood into W. This
   retains arbitrary open neighbourhoods, not merely affine neighbourhoods.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`,
  with its actual nonempty/domain fields.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme.ΓSpecIso` (canonical evaluation on affine global sections).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact` (the conjunction is finite type).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and `.Separated`:
  `IsProper`, `IsSeparated`; universal closedness supplies quasi-compactness.
- `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement`:
  `GenericScheme`, `Model`, `QuasiModel`, `ModelHom`, `ValuationPoint`,
  `ValuationPoint.push`; their full definitions were read. These constructors
  have arbitrary T, L and generic map, even though the theorem `finite_refinement`
  in that module assumes a separable closure and finite type over integers.
  This delivery uses only the general constructors, never that restricted theorem.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField` and
  `Scheme.fromSpecStalk`; `Mathlib.RingTheory.Valuation.ValuationSubring`:
  `ValuationSubring`; `Mathlib.CategoryTheory.Limits.IsLimit`: `IsColimit`.
- The new definition node records the topology, affine neighbourhoods, their
  canonical coordinate-ring diagram/cocone and the colimit-data structure.

The main file imports all recorded proof-dependency modules, using ordinary
(non-public) imports. In particular it imports the recorded side reduced-induced
closed-subscheme theorem and boundary-compactification interface. The definitions
are obtained from their existing imports. No dependency interface was repaired.

Edge cases checked before writing: the empty scheme is already excluded by the
node's integrality; the field base and its trivial valuation are retained; the
identity proper model is allowed; a nonseparated qcqs integral base (e.g. the
line with doubled origin) retains its distinct valuation-centre maps; valuation
height is unrestricted, including trivial valuations and infinite height;
no Noetherian, finite-presentation, finite-type-over-integers, or separable-closure
assumption was introduced. All universes are explicitly declared. The small
index is in the universe of F, which accommodates the cofinal set of affine
subrings and gluing data. Prescribed W need not be affine or quasi-compact.

Searches (actual tool receipts are recorded in the new node's mathlib_searches):

- msearch leanfinder, `Riemann Zariski space compact valuation rings affine
  neighbourhoods birational models`: eight hits about compact schemes, affine
  opens and dominant global-section maps; none is this statement.
- msearch loogle, `"RiemannZariski"`: zero hits.
- msearch grep, `Riemann.?Zariski|[Bb]irational|ValuationSubring`, AlgebraicGeometry:
  eight hits in Mathlib's rational/birational maps, not Riemann--Zariski spaces.
- msearch leansearch, `valuation points of integral scheme Riemann Zariski topology
  affine centre neighbourhoods filtered colimit`: eight valuative-topology hits;
  these are ring topologies, not the valuation-point space topology.
- msearch leanfinder, `affine neighbourhoods on proper birational models valuation
  ring filtered union`: eight hits on affine covers and transition limits;
  none supplies this affine-model-neighbourhood diagram.
- msearch loogle, `"ValuationSubring"`: twelve hits; the existing valuation
  subring definition is reused, not copied.
- msearch grep, `Riemann.?Zariski|[Bb]irational.*[Mm]odel|valuationTopology`:
  four imports of unrelated valued-field valuation topologies.
- rg of WeilConjectures/, Mathlib and lean/Sheaf for the concept and the new
  declaration names: the existing Sheaf general model/valuation constructors
  above were found and reused; no matching affine-neighbourhood data or topology.
  The `RiemannZariskiLocalColimit` module uses centre stalks, not coordinate rings
  of affine opens, and its theorem imposes the separable-closure setting.
- rg of dag/nodes and `blueprint_refs.py search birational` / `search valuation`:
  no standalone definition of the added data. The ancestor command gives
  `lem-trf-local-term-locality`. An explicit traversal of both dependency lists
  from `lem-trf-riemann-zariski-finite-refinement` originally found no path back to this
  item (586 visited nodes). The repaired statement dependency now names the standalone
  definition node below, not that theorem node.
- rg of WeilConjectures/ for the item id: no declaration for this item.

Source checked directly: arXiv:0707.3953v3, printed pp. 15--17, especially
Proposition 3.2.1, Lemma 3.2.2, and Corollaries 3.2.4--3.2.5 and 3.2.7.
The source is available at https://arxiv.org/pdf/0707.3953; the node's Huji PDF URL
failed to fetch, so the arXiv copy of the same version was read.
No statement dispute or correction is required.

## New nodes

`def-trf-birational-valuation-neighbourhood-data` defines the open-cylinder
valuation topology and the canonical affine-model-neighbourhood diagram and
colimit-data predicate. Source: Temkin §3.2, pp. 15--16, expressed using affine
neighbourhoods in Lemma 3.2.2 and the valuation description of Corollary 3.2.5.
It reuses the generic model/valuation constructors through
`def-trf-riemann-zariski-generic-models` and the existing Mathlib coordinate
rings, ring morphisms and categorical colimit predicate. The three search
families above found no existing node/declaration for this remaining interface.
Every added declaration has a source/blueprint docstring and is listed in
lean.declarations. No new theorem is concealed in the definition node.

`def-trf-riemann-zariski-generic-models` records the six existing definitions
`GenericScheme`, `Model`, `QuasiModel`, `ModelHom`, `ValuationPoint`, and
`ValuationPoint.push` in `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement`.
Its record is `existing: true`, `branch: newtargets-dag`, with no new Lean file.
The source is Temkin §3.2, opening paragraph p. 15 and the valuation-point and
composition descriptions pp. 16--17. Its statement unpacks the structures for
arbitrary specified T, L and η; it makes no assertion requiring the finite-refinement
theorem. The definition's statement dependencies are definitions only. Both the
item and the affine-neighbourhood definition now cite this new node directly;
the latter no longer cites `lem-trf-riemann-zariski-finite-refinement`.
New searches on 2026-10-19: LeanSearch, “generic factorization proper models separated
finite type quasi models centred valuation subrings of a field”, returned eight
valuation-subring results; Loogle, `"RiemannZariski"`, returned zero; msearch grep,
`GenericScheme|QuasiModel|ValuationPoint|ModelHom` in AlgebraicGeometry, returned zero.
Direct rg found no upstream definitions and the six existing Sheaf declarations.
A definition-kind scan of the DAG and `blueprint_refs.py search 'generic model'`
found no node recording this interface. `def-trf-centred-valuation` is a predicate
on a valuation subring of a particular point's residue field, rather than the
arbitrary-L structures, and is not restated. The actual search receipts, including
the upstream/Sheaf/DAG search, are in the new node's `mathlib_searches`.

## Second reading by Q111

Reader: the separately dispatched Q111 repair-session worker, 2026-10-19. This
session did not author the retained Lean files. I opened both saved Lean files,
the item and both definition-node JSON files, and the six original declarations
in `RiemannZariskiFiniteRefinement.lean`; the latter were also confirmed against
the current server source using `scompile.py --source`. This replaces the original
author's self-reading. No additional agent was started.

For the item, `Z : Scheme.{u}`, `[IsIntegral Z]`, `[CompactSpace Z]`, and
`[QuasiSeparatedSpace Z]` give exactly an integral qcqs scheme. The fixed field
is the generic stalk `Z.functionField` and its map is `Z.fromSpecStalk
(genericPoint Z)`. `Model` and `QuasiModel` use that field and map. Their generic
factorizations force the compatible function-field identification in this
specialization; the general definitions do not assume one for arbitrary L.
`ValuationPoint` keeps both the actual subring and the specified centre, including
multiple possible centres on a nonseparated base.

I checked the seven conjuncts independently against the node:

1. `∃! l` imposes both the triangle over Z and the specified generic restriction,
   exactly unique lifting to a proper birational model.
2. The quantified centre functions `c` must come from valuative lifts; the equality
   to the infimum of induced topologies is the required initial centre topology.
   The preceding unique-lifting clause makes this characterization nonvacuous.
3. `@CompactSpace` uses the explicit generated topology and means quasi-compactness.
4. `@IsOpenEmbedding (ValuationPoint.push U)` uses the generated topology on both
   valuation spaces and the actual composite-centre map. It is precisely the
   asserted homeomorphism onto an open subspace, for every quasi-model.
5. `AffineValuationColimit v (fun _ ↦ True)` retains a small nonempty directed
   preorder, cofinality, actual affine-coordinate-ring pullbacks, injective
   coordinate and transition maps, `IsFractionRing` for the canonical map into F,
   `IsColimit` for the canonical cocone into V, and the elementwise union equality.
   Its opposite gives the cofiltered neighbourhood system.
6. `AboveWithin M ⊤` retains the same whole structure above any prescribed model.
7. For an actual lift l and arbitrary open W containing its closed-point image,
   `AboveWithin M W` requires the entire affine chart to map into W. The hypotheses
   on l are exactly the valuative triangle and generic restriction, without an
   extra assumption on W.

For `def-trf-birational-valuation-neighbourhood-data`, I checked all twelve listed
declarations. `valuationCylinder` uses actual lifts; `valuationTopology` is
`generateFrom` of those cylinders. `AffineValuationNeighbourhood` includes the
actual affine open, lift and generic map and all three compatibility equations.
`ring` is Γ of that open; `intoV` is the lift's `appTop` composed with ΓSpecIso;
`intoField` composes with the given subring inclusion. Refinements restrict actual
model morphisms and respect both maps. `AffineValuationSystem` includes admissibility,
cofinality, a nonempty directed small index and coherent ring pullbacks. `ringDiagram`
and `ringCocone` use those pullbacks and the specified maps. `AffineValuationColimit`
adds precisely the injectivity, fraction-field, colimit and union clauses.
`AboveWithin` has the declared domination and whole-chart image condition.
No data or map is chosen from a postponed theorem.

For `def-trf-riemann-zariski-generic-models`, I checked its metadata against the
pre-existing six declarations, not against the nearby theorem's hypotheses:
`GenericScheme.X/integral/map/generic/generic_point/fac` are exactly the integral
generic factorization; `Model.proper` adds properness; the three `QuasiModel`
instances are separatedness and finite type; `ModelHom.hom/over/generic` give
exactly the two commuting triangles. `ValuationPoint.V/centre/fac` are exactly
the valuation subring, centre map and specified generic restriction. `push` retains
V and composes centre with U.map. Its compatibility proof uses only the two
factorization equations. The JSON uses ordinary composition order consistently
with these Lean equations. Its existing record names exactly those six declarations
and no theorem; its signature is the whitespace-normalized GenericScheme signature
up to `where`. All its dependencies are definition nodes. The statement makes no
compactness, existence or finite-refinement claim and adds no duplicate Lean data.

Edge checks: integral excludes the empty scheme; identity models and the whole-field
valuation are allowed; there is no Noetherian, finite-presentation, separable-closure,
finite-type-over-integers or valuation-height restriction. The index universe is u,
the field's universe. W is allowed to be any neighbourhood, including non-affine and
non-quasi-compact opens. Arbitrary T,L,η in the definition node allow empty model or
valuation types; that node asserts no existence in those cases.

The mismatch found was the theorem-node dependency used to access plain structures.
I repaired it with the requested existing-definition record and direct citations
from both consumers. I found no mismatch in the retained Lean statements or data.
The independent maintainer return on immutable head `6090e6624977` likewise accepted
all seven clauses, the real data, docstrings and signatures. Both retained Lean
files are unchanged from that returned packet; only the new definition record,
its citations, record dates and this report change. Against the current shared
item, the only changed fields remain `lean` and added `stmt_deps`; the original
mathematical statement, proof and proof dependencies remain unchanged.

## Return repair

- H12: added `def-trf-riemann-zariski-generic-models` with an existing:true record
  on the published module listing the six requested declarations. Replaced the
  theorem dependency in the affine-neighbourhood definition's statement and
  `stmt_deps`; added the new definition directly to the item's `stmt_deps`.
- Secondary: replaced the original author's self-reading with the repair-session
  reading above, covering the retained item and both definition nodes, their
  declarations, sources and dependency interfaces. The new metadata was checked
  directly against the existing constructions prescribed by the maintainer.

The initial saved-packet dry run passed as commit `850cf35049`; that successful
mechanical check did not discharge the substantive return. The repaired packet
is compiled and dry-run again before delivery.
