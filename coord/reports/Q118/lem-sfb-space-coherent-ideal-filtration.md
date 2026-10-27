## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentIdealFiltration` states
`AlgebraicGeometry.AlgebraicSpace.exists_coherent_ideal_filtration`, with its sole proof
`sorry`. It is exactly the support-controlled, zero-factor-free version of Stacks 07UR
recorded in the item. No statement correction, dependency replacement, or proved theorem
is supplied. The accepted seven-step split is preserved in the theorem docstring.

The inherited BLOCKED ending concerned stage 1. The live node has no Lean record and is
queued with stage 2; brief-stage2 section 0 expressly authorizes this handoff. Q51's
review is of the split, not a previously delivered statement. No repair note exists.

Hypotheses and clauses, matched against the node:

- `S : Scheme.{u}` and `X : AlgebraicSpace S` are the given scheme and algebraic space.
  They use the recorded small etale site and `X.Modules`, with section universe `u`
  and site-object universe `u+1`; no independent universe equality is assumed.
- `hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)` says locally
  Noetherian on every etale scheme chart. `hqc : CompactSpace (Point X.obj.obj)` is
  quasi-compactness in the recorded atlas topology. `hqs` asks that the fibre product
  of any two affine scheme maps to X have quasi-compact point space, the standard
  absolute quasi-separatedness test. It does not require that X be quasi-separated
  over S (a stronger, different relative condition).
- `F : X.Modules`, `hF : F.IsFinitePresentation` express the coherent module. On
  locally Noetherian scheme charts, coherent = quasi-coherent finite type = finite
  presentation (07UB). Mathlib's local finite-presentation predicate already includes
  quasi-coherence. This is the encoding used by the existing
  `AlgebraicSpaceCoherentFilteredUnion` module, rather than a second coherence notion.
  The recorded pqf interface is imported; its scheme-only finite-type predicate is
  not used as though it were an algebraic-space predicate.
- `m : ℕ` includes length zero. `c : Fin (m+1) → Subobject F` and `hc : Monotone c`
  give actual subobjects of F with canonical inclusion arrows. `IsZero (c 0)` is
  the initial zero submodule; `IsIso (c (Fin.last m)).arrow` says that the final
  subobject is all of F. These express bottom and top without requiring an
  unnecessary complete-lattice/sheafification instance.
- Every `c k` has `IsFinitePresentation`, hence is coherent under hln.
- `j : Fin m` indexes the inclusions from `c j.castSucc` to `c j.succ`, namely all
  successive factors numbered 1 through m, including the last.
- `Z : AlgebraicSpace S`, `i : Z ⟶ X`, and
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom` assert a
  representable closed immersion on every scheme test. No relative closed-subset
  or mere arbitrary monomorphism replaces it.
- `∀ T : Z.EtaleSite, IsReduced (Z.etaleForget.obj T)` is reducedness of all etale
  charts; Mathlib's scheme predicate is equivalent to reduced local rings.
  `IrreducibleSpace (Point Z.obj.obj)` includes nonemptiness as required.
- `K : Subobject (SheafOfModules.unit Z.structureSheaf)` is an ideal subsheaf of
  O_Z, using Mathlib's subobjects, not a private ideal-sheaf definition. The
  structure rings are commutative, so their submodules are ideals.
  `¬ IsZero K`, `K.IsFinitePresentation`, and `moduleSupport K = Set.univ` express
  nonzero, coherent, and full support, respectively. Coherence is meaningful here
  because a closed subspace of this Noetherian X is locally Noetherian.
- The module `Q`, arrow `q`, vanishing composite `w`, and
  `Nonempty (IsColimit (CokernelCofork.ofπ q w))` say exactly that Q is the cokernel
  of the canonical inclusion `Subobject.ofLE ... (hc j.castSucc_le_succ)` in all
  module sheaves. It is the quotient, not an arbitrary object or an extra axiom
  asserting a chosen abelian structure. The universal property uniquely determines
  it up to its unique compatible isomorphism.
- `Nonempty (Q ≅ (moduleDirectImage i).obj K)` uses the recorded canonical chart-limit
  direct image. `pointImage i.hom.hom = moduleSupport Q` and
  `moduleSupport Q ⊆ moduleSupport F` are both required support clauses.
- `moduleSupport F = ∅ → m = 0 ∧ IsZero F` states the final empty-support clause
  for the very filtration supplied by the existential.

The new `moduleSupport` is real set-valued data. A point is in it when some section
on some etale chart above the point stays nonzero under every further pointed etale
refinement. Stacks 04JY's filtered-colimit description of stalks gives exactly this
nonzero-germ criterion; 04K4 makes vanishing independent of the geometric lift. For a
section defined on a chart, conjugation of lifts fixes its germ, so ordinary chart
points suffice in the formula. Refining again excludes a section that is globally
nonzero but has zero germ at the designated point. The definition also works for
arbitrary modules, without Noetherian or finite-presentation assumptions.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`
  and its slice instances; `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFinitePresentation`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType` (the recorded scheme interface).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point`, `schemePointMap`,
  `pointTopologicalSpace`, `pointImage` (with the point-class module underneath).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`
  from the recorded `ModuleDirectImageModel` and its complete chart-limit property.
- Mathlib `Subobject`, `Subobject.ofLE`, `IsZero`, `IsIso`, `IsReduced`,
  `IrreducibleSpace`, `CokernelCofork.ofπ`, and `IsColimit` give the remaining standard
  notions directly.

Already-stated proof dependencies are plain imports: `SiteRestrictionExact`,
`CoherentKernelCokernelLocallyNoetherian`, `SchemeZariskiEtaleQuasiCoherentEquivalence`,
`ModuleStalkExact`, and Mathlib `Topology.Sheaves.Stalks` (the iso-on-stalks match).
The module-sheaf category is publicly imported through AlgebraicSpace. Other proof
nodes in the accepted split have no Lean record yet, so have no module to import;
no theorem prerequisite was needed as a hypothesis to type the statement.

Edge cases checked against the source and the Lean:

- F=0 and empty X: take m=0 and the unique zero subobject; there are no factor
  witnesses to provide, because `Fin 0` is empty. Initial and final conditions agree.
- A field: a finite-dimensional nonzero module has a coordinate filtration; each
  ideal is the whole structure module on the one-point reduced irreducible space.
- Nonreduced X, for example Spec(k[e]/e²): X itself need not be reduced; the two
  adic factors can come from the reduced closed point. No global reducedness added.
- Reducible support: different j may have different Z; no equidimensionality,
  disjointness, or common closed subspace is required.
- No zero factors: K is nonzero and Z has nonempty irreducible point space.
- Zero support forces m=0 for the chosen filtration, not merely existence of a
  different filtration. Full support is stated on K itself as well as on Q.
- All scheme tests use the same scheme universe u, including arbitrary base S.

Searches for an existing statement (through msearch.py): LeanFinder queried the
finite ideal filtration on a Noetherian algebraic space and returned 8 scheme
Noetherianity declarations. LeanSearch queried the same filtration and returned
8 finite-presentation and ordinary Ideal.Filtration declarations. Loogle queried
`SheafOfModules.Submodule, CategoryTheory.Limits.cokernel, Ideal.Filtration` with
0 hits. Mathlib grep `coherent.*filtration|filtration.*coherent|structure Submodule`
returned 4 unrelated submodule/basis declarations. Direct rg in WeilConjectures and
Sheaf found `Scheme.Modules.HasCoherentIntegralFiltration` and its scheme-only
existence theorem, not the algebraic-space assertion; exact item-id search found no
existing declaration. The full search log is retained in sandbox searches.jsonl.
Support-specific searches are recorded verbatim as JSON results in the new node.
`blueprint_refs.py search 'geometric support'` returned three unrelated nodes;
DAG definition searches found no duplicate algebraic-space module-support notion.

No STATEMENT-DISPUTED issue remains. Both files compiled cleanly through scompile.py;
the first attempt's bottom/top typeclass failure was repaired using their exact
categorical meanings (IsZero and IsIso of the inclusion), without changing mathematics.
No library build or live-file edit was performed.

## New nodes

`def-sfb-space-module-support` defines geometric support of an algebraic-space module
by the explicit nonzero-germ test of Stacks Properties of Spaces 04JY, 04K4, and 04KA.
Its module is `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`; its declaration
is `AlgebraicGeometry.AlgebraicSpace.moduleSupport`. LeanSearch returned scheme ideal
supports and affine-module support; LeanFinder returned ordinary germs/zero loci;
Loogle and module-sheaf Mathlib grep had no support definition. Project and DAG
searches found uses of the notion but no defining node/declaration. None of the hits
is this set of point classes for a module on X_et. All definition data are supplied.
The inherited blueprint ancestor is null, as confirmed by blueprint_refs.py ancestor;
the place and via chain explain the supporting use in Tag 07UR.

## Second reading by Q118

Performed a separate second reading of the current node, source 07UR, and both files
in this single-worker session; no second agent was started, as the dispatcher forbids
it. This is not claimed to be a reading by a different person. The maintainer's
independent delivery review remains required.

The hln/hqc/hqs binders match the node's absolute Noetherian hypothesis; finite
presentation on locally Noetherian charts matches coherence. The chosen subobjects
are a finite monotone chain of coherent modules, initial zero and final all of F.
The adjacent indices are j.castSucc and j.succ, so no factor is omitted. The closed
immersion predicate uses every scheme base change; reducedness uses every etale
chart; IrreducibleSpace supplies nonemptiness. K is a nonzero coherent subobject
of O_Z, and its support is all of Z. The quotient is explicitly a categorical
cokernel of the chain inclusion and is isomorphic to the recorded i_*K. Both support
identities and the subset bound appear. The last implication gives both m=0 and F=0.
No mathematical mismatch was found. The initial bottom/top encoding was replaced by
IsZero/IsIso of the canonical subobject arrow after the compiler exposed an irrelevant
complete-lattice requirement; the equivalent endpoint clauses now compile. The support
definition was checked against 04JY and 04KA, including the need to test every pointed
refinement rather than global nonzeroness alone. Source tags in its docstrings were
made precise. No statement correction or dependency module is necessary.
