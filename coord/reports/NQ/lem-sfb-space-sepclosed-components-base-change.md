## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.sepClosed_components_baseChange`
in `Sheaf.AlgebraicGeometry.SpaceSepClosedComponentsBaseChange`. The theorem's proof is
`sorry`; no theorem is proved. Three construction helpers and two transparent abbreviations in the same module give the
actual base morphism, extension-field spectrum, its base morphism, the sheaf scalar
extension, and its projection. They are recorded in `lean.declarations`. Their data are
existing categorical constructions, never a choice from an existence theorem. In
particular the structural map is the unique morphism to the sheaf Yoneda image of the
terminal object `Over.mk (𝟙 S)`; the scalar extension and projection abbreviate the
existing `enlargedFibreProduct` and `enlargedFibreProductFst` constructions exactly.

Sources read: `spaces-over-fields.tex`, lemma-separably-closed-field-connected-components
(Tag 0A12), including lemma-bijection-connected-components and its proof;
`spaces-morphisms.tex`, lemma-space-over-field-universally-open (Tag 06DN);
`spaces-properties.tex`, lemma-open-subspaces (Tag 03BZ) and
lemma-factor-through-open-subspace (Tag 03IE). These give exactly the node's generality.
No statement correction, dependency repair, new independent notion, or disputed statement
is needed. The existing CompactObject example is withdrawn; its recorded upstream module
supplies the historical convention, while current modules supply the module header style.

Hypothesis and clause correspondence:

- The separably closed ground field is `(k : Type u) [Field k] [IsSepClosed k]`.
- An arbitrary field extension is `(L : Type u) [Field L] [Algebra k L]`, using
  `algebraMap k L` and `Spec.map (CommRingCat.ofHom (algebraMap k L))`.
- The algebraic space over Spec k is
  `Z : AlgebraicSpace (Spec (CommRingCat.of k))`, the recorded fppf-sheaf/atlas notion.
- The point type and atlas topology are precisely `Point Z.obj.obj` and its existing
  `pointTopologicalSpace` instance. They are not replaced by a scheme atlas or by its points.
- `fieldScalarExtension k L Z` is the sheaf pullback of the two canonical maps to
  `schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of k))))`. As in the node it is viewed over k;
  it retains its second projection to Spec L. `fieldScalarExtensionProjection k L Z`
  is its first projection. This uses the recorded sheaf fibre-product construction.
- `Continuous`, `Function.Surjective`, and `IsOpenMap`, applied to the recorded `mapPoint`
  of this projection, render the three properties of |p|.
- `Set.range (connectedComponent (α := Point Z.obj.obj))` is the set of all connected
  component subsets. Mathlib defines `connectedComponent x` as the maximal connected
  subset containing x; it is nonempty. This set of subsets therefore has exactly the
  node's maximal nonempty connected subsets, with repeated point representatives removed.
  Mathlib's `IsConnected` is nonempty plus no nontrivial relatively open partition.
- `Set.BijOn (fun D ↦ mapPoint ... ⁻¹' D)` between these two ranges asserts exactly that
  inverse image takes components to components and is bijective on them. It specifies
  the inverse-image correspondence itself, rather than an unspecified equivalence.
- `∀ D ∈ Set.range ..., IsClopen D ↔ IsClopen (mapPoint ... ⁻¹' D)` is the component
  clopenness equivalence, without asserting that arbitrary components are open.
- The final descent conjunct quantifies `C : OpenSubspace (fieldScalarExtension k L Z)`
  whose point image is a connected component and is clopen. It asserts `∃! D : OpenSubspace Z`
  whose point image is a clopen connected component and whose subfunctor preimage along
  the canonical projection equals `C.val`. Literal preimage of a subfunctor is the
  pullback open subspace, so this is `C = D ×_k L`, with equality as subspaces over Z_L.
  Open-subspace structures use precisely the recorded `OpenSubspace`, not extra data.
- `ConnectedSpace (Point Z.obj.obj) ↔ ∀ (K : Type u) [Field K] [Algebra k K],
  ConnectedSpace (Point (fieldScalarExtension k K Z).obj.obj)` expands exactly the given
  meaning of geometrically connected. `ConnectedSpace` includes nonemptiness.
- There is no quasi-compactness, finite type, finite presentation, connectedness or
  nonemptiness assumption on Z and no algebraicity, separability or finiteness assumption
  on L/k. All scheme/field objects use the ambient universe of the project's recorded
  algebraic-space and point-class definitions. The theorem is polymorphic in that
  ambient universe; no smaller independent universe is used for test field extensions.

Statement dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs` (mathlib leaf).
- `def-pc-separably-closed`: `IsSepClosed`, `Mathlib.FieldTheory.IsSepClosed`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpace` (fppf sheaf, representable diagonal and atlas).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-a1-space-point-topology`: `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`,
  `PointRepresentative.map` and `pointImage`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`; the point type and representative
  relation come from its public import `AlgebraicSpacePointClasses`.
- `lem-trf-space-fibre-products-etale-covers`: `fibreProduct_isAlgebraicSpace`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`.
- `def-a1-space-open-subspace`: `OpenSubspace`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`.
- `def-sfb-proper-curve-moduli`: `AlgebraicGeometry.AlgebraicSpace.mapPoint`,
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`.
- `def-trf-scheme-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace.schemeSpace`,
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`.
- `def-sfb-space-sheaf-fibre-product`: `AlgebraicGeometry.AlgebraicSpace.enlargedFibreProduct`
  and `AlgebraicGeometry.AlgebraicSpace.enlargedFibreProductFst`,
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`.

Additional existing constructions used: `schemeSpace` from
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, `mapPoint` from
`Sheaf.AlgebraicGeometry.ProperCurveModuli`, `Over.mkIdTerminal`, the sheaf Yoneda
limit-preservation instance and `IsTerminal.isTerminalObj`. These supply the canonical
map to the base without an arbitrary structure-map argument. `connectedComponent`,
`Set.BijOn`, `IsClopen`, and `ConnectedSpace` are existing Mathlib notions.

All recorded proof-dependency modules available at the time of writing are imported
without `public`: `AlgebraicSpaceEtaleOpenImage`, `AlgebraicSpaceOpenFactorSchemeTests`,
`AlgebraicSpacePointOpenCalculus`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`.
The fibre-product dependency is already a public statement import.
The nodes `lem-sfb-quotient-connected-component-preimage` and
`lem-sfb-space-over-field-universally-open` have no recorded Lean module to import.
They remain named in the proof docstring; no substitute theorem is assumed.
The full seven-step proof in the item is rendered in the main theorem docstring.

Edge cases checked before writing and again on rereading:

- Empty Z: no component subsets exist on either side, the empty-map bijection and open
  surjection make sense, and both connectedness predicates are false.
- Identity extension: the canonical fibre product is isomorphic to Z, and the final
  universal quantifier includes this case; there is no exceptional arbitrary-lift case.
- A point, disconnected spaces, infinitely many components, and components that are not
  open: neither `Set.range` nor `Set.BijOn` imposes local connectedness or finiteness;
  the descent statement applies only when the specified component is clopen.
- Transcendental extensions and inseparable extensions in positive characteristic:
  there is only `[Algebra k L]`, with no `Algebra.IsAlgebraic` or separability assumption.
- The empty subset cannot be a component, since every `connectedComponent x` contains x.
  Thus the open empty subspace is not inadvertently included among component subspaces.
- Uniqueness is equality of open subfunctors, exactly the open-subspace convention,
  rather than equality of arbitrary isomorphic representatives of spaces.

Searches for existing declarations (2026-10-24):

- `msearch.py ... leanfinder` query: "Base extension from a separably closed field induces
  a bijection on connected components of algebraic spaces". Eight hits, including
  `IsPurelyInseparable.bijective_comp_algebraMap`,
  `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`, and
  `Scheme.SpecToEquivOfField`; none states the algebraic-space component result.
- `msearch.py ... leansearch` query: "Algebraic space over separably closed field has
  connected components preserved under field extensions". Eight field-theory hits,
  including `Algebra.IsAlgebraic.isSepClosed`, `IsSepClosed.of_isAlgClosed` and
  `IsSepClosure.recOn`; no match.
- `msearch.py ... loogle` query: `"GeometricallyConnected", "ConnectedComponents"`.
  Zero hits.
- `msearch.py ... grep 'GeometricallyConnected|AlgebraicSpace' AlgebraicGeometry`:
  five hits in Mathlib's `AlgebraicGeometry/Geometrically/Connected.lean`; this is
  expressly the scheme-only notion and does not state this node.
- Direct `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for separably closed component statements and this item id found the scheme-only
  `Sheaf.AlgebraicGeometry.SepClosedFieldComponentsBijection`, its geometric-component
  count consumer, a valuation-specific result and proof references, including
  `SpaceSteinFactorizationAffine`. The scheme statement's full signature was read;
  it cannot replace an assertion about arbitrary algebraic spaces or clopen subspaces.
- Direct searches for `structuralMapToBase|extensionFieldSpace|extensionFieldBaseMap|
  fieldScalarExtension|sepClosed_components_baseChange` found no full-name collision
  in `AlgebraicGeometry.AlgebraicSpace`. Existing field scalar extension for coefficient
  sheaves is in another namespace and constructs a different object.
- Repair search: `rg -n enlargedFibreProduct` in the current `lean/Sheaf/AlgebraicGeometry`
  sources and the landed owner node identified `enlargedFibreProduct` and
  `enlargedFibreProductFst` in `EnlargedEtaleRingedSite.lean` (lines 230 and 236).
  Their full signatures, bodies and docstrings were read and are now reused exactly.
  The original search missed these declarations; the returned duplication is repaired.

Validation: prescribed `scompile.py NQ lem-sfb-space-sepclosed-components-base-change`
compiled the module in both its sandbox and final module namespaces, with no errors or
warnings. The initial missing terminal-preservation instance was resolved by explicitly
importing Mathlib's Yoneda limit and subcanonical-site APIs. Only this sandbox was edited;
no Git command or global/local Lean build was run by the worker.

## Second reading by NQ

This is a second pass by the same dispatcher-started worker; the brief explicitly forbids
starting another agent. The maintainer's independent delivery review remains separate.
I reread the node, the source passages and the complete Lean declaration together.

The binders supply exactly k, its separable closedness, L/k, and Z over Spec k. The three
map properties appear in the stated order. The bijection acts by inverse image on sets
of actual component subsets; using `Set.range connectedComponent` preserves nonemptiness
and removes duplicate descriptions. The clopen equivalence quantifies precisely over
components. The descent clause retains the open-subfunctor structures and states uniqueness
of a clopen component D with the required literal pullback, so it loses neither the
structure nor uniqueness. The final quantifier includes all ambient field extensions,
including the identity, and `ConnectedSpace` retains the nonempty convention. No finiteness
condition or algebraicity assumption was added. The three helper definitions are explicit
canonical base constructions; the two scalar-extension abbreviations specialize the landed
fibre-product API exactly. None uses sorried data or an arbitrary map.
The only compile defect found was the missing public limit-preservation imports, repaired
before the successful compile. No mathematical mismatch or statement correction was found.

## Returned delivery repair

Return reviewed immutable head `7f6a78939e0e`; the maintainer accepted the statement
mathematics and requested H2 and H4 repairs only. I compared the retained sandbox node
with current main before editing: all existing fields agreed except for the sandbox's
new `lean` record. The repaired node uses the current main record plus the authorized
statement dependencies and repaired Lean attachment. The delivery wrapper rebases it.

1. H2: added exactly `def-sfb-proper-curve-moduli`, `def-trf-scheme-algebraic-space`, and
   `def-sfb-space-sheaf-fibre-product` to `stmt_deps`. Their landed records and the full
   source declarations/docstrings for `mapPoint`, `schemeSpace`, `enlargedFibreProduct`,
   and `enlargedFibreProductFst` were read. The module already publicly imports both
   owning modules, so no new import is necessary.
2. H4: replaced the two copied constructions with `abbrev fieldScalarExtension` whose
   body is exactly `enlargedFibreProduct (structuralMapToBase Z) (extensionFieldBaseMap k L)`
   and `abbrev fieldScalarExtensionProjection` whose body is exactly
   `enlargedFibreProductFst (structuralMapToBase Z) (extensionFieldBaseMap k L)`.
   `lean.declarations` continues to list the three actual base helpers, the two allowed
   transparent specializations and the theorem; `lean.note` now identifies them as such.
   The theorem signature and `lean.statement` are byte-for-byte unchanged, checked by
   comparing the signature extracted from the repaired module with the returned record.

Repair second reading: both abbreviation bodies call the existing owner declarations
directly, with the same canonical arguments as the removed constructions. The reviewer
accepted the clause mapping and edge cases, and those are unchanged. The explicit owner
edges now match all three signature notions identified in the return. The prior report's
duplication claim and description of five independent constructions have been corrected.
The prescribed `scompile.py` repair run passed in both sandbox and final module
namespaces with no errors or warnings. The delivery dry run is repeated below.
