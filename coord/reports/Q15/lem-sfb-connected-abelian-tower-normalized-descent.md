## Worker report

This is stage 2. The live item has a PASS-reviewed stage-1 split by Q37 on
2026-10-22, but no `lean` record and no `reviewed_lean`. There is no repair note.
The prior worker's stale-assignment conclusion confused the stage-1 split with
stage-2 completion. I preserve that reviewed split verbatim and supply its Lean
statement. No statement correction and no dependency interface repair is needed.

`Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedDescent` states
`AlgebraicGeometry.ProEtale.nonempty_connectedAbelianTowerNormalizedDescent`,
with exactly one `sorry`. Its conclusion is nonemptiness of a structure packaging
the node's assertions; it assumes no splitting, action, or classification result.
All helper definitions have actual data. The complete eleven-step DAG proof is
in the theorem docstring, including the finite-frame argument for the final clause.

Hypotheses and clauses, individually:

- Affine base: `(U : Scheme.{u}) [IsAffine U]`.
- Small nonempty directed index set: `(I : Type u) [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. This follows the standing Stacks 00D3 convention and
  permits directed preorders, not just antisymmetric orders.
- The inverse system is `T.levels : Iᵒᵖ ⥤ U.ProEt`. The new tower's fields
  `affine`, `connected`, `finite`, `etale` impose precisely the finite-level
  conditions. `ConnectedSpace` includes nonemptiness.
- Finite abelian deck groups are `T.groups : Iᵒᵖ ⥤ ProfiniteGrp`, with
  `finite_groups`, `commutative`, `surjective`. A finite Hausdorff group has its
  discrete topology. `action` is a monoid hom into endomorphisms over U;
  `equivariant` is the exact transition compatibility.
- `finiteComparison`, `finite_fst`, `finite_action` pin the finite comparisons
  to `(x,g) ↦ (x,gx)`. Finite profinite test objects are the specified disjoint
  labelled copies, by def-sfb-profinite-test-objects. No inversion convention
  has been substituted.
- `T.cone` and `T.isLimit` give the limit of the underlying scheme diagram.
  Its vertex is already a U-proetale object. `limit_connected` includes
  nonemptiness; `cover` is actual singleton membership in the proetale precoverage.
- `groupCone` and `groupIsLimit` specify G as the limit in profinite groups,
  so the limit topology is part of the hypothesis. `comparison` and
  `comparison_fst` give X[G] ≅ X×_U X. `compatibility` is equality of scheme
  maps on the whole profinite test object, inducing the given finite comparisons.
- The geometric point is the actual map `z : Spec (.of Ω) ⟶ T.cone.pt.left`,
  with explicit `[Field Ω] [IsAlgClosed Ω]`.
- L is `T.finiteLevel.FullSubcategory`. Its object predicate says
  `∃ i, abelianTowerConstantAt F (T.levels.obj i)`;
  `abelianTowerConstantAt` uses the recorded proetale inverse-image functor and
  Mathlib's constantSheaf, with a finite set that may be empty.
- The actual geometric stalk Q_F is `T.finiteLevelStalk z`, constructed on maps
  by the colimit of the recorded pointed-neighborhood diagram. `fibreIso` is
  a natural isomorphism from the finite labels to precisely that stalk. The
  `ULift` only reconciles the finite label universe with the set-sheaf universe.
- `splitting` is the universal section on X[Q]; `normalized` says that its
  restrictions give bijections on EVERY proetale object over X and that its
  germ at label q is exactly q via `fibreIso`. By finite-constant representability
  and Yoneda this is the inverse of the isomorphism φ_F in the node. Thus the
  normalization is identity on the actual fibre, not an arbitrary identification.
- `unique` states uniqueness of this normalized universal section, equivalently
  of φ_F. `finiteLevel` supplies normalized sections at EVERY level i trivializing
  F, and its restriction equality identifies their pullbacks with `splitting`.
  Uniqueness at each connected level follows from `constant_maps` applied in
  finite constant labels. Thus the clause covers every trivializing level.
- `constant_maps` explicitly quantifies over every connected scheme V, geometric
  point v, finite label sets A,B and constant sheaf maps f,g, asserting that equal
  maps on the actual geometric stalk imply f=g. This is the node's independent
  constant-sheaf fibre-determination assertion.
- `fibre` lands in `ContAction FintypeCat G`, hence supplies continuous LEFT
  actions. `finiteLevel` includes a monoid hom ρ_i from Γ_i and equality
  `fibre.ρ g = ρ_i (π_i g)` for all g. Its last germ equation pins ρ_i to deck
  descent in the given `(x,gx)` convention, rather than merely choosing any
  finite-quotient action.
- `actionLabels` is a continuous map G×Q→Q pinned pointwise to that action.
  `descentLabel_base` pins the other scheme map to the deck coordinate gx;
  `descentLabel_label` pins its Q-coordinate to q. `descent` says the two
  restrictions of the universal section AGREE ON ALL X[G×Q]. This is an
  equality of sheaf arrows by Yoneda, including nonconstant profinite parameters,
  not just an equation at individual group elements.
- `unique` and the pullback and factorization assertions in `finiteLevel`
  identify all level splittings and their descent actions with the one splitting
  and action in the package. Thus both are independent of the chosen level.
- `fullyFaithful` is the Hom bijection into equivariant finite-set maps.
  Under the natural `fibreIso` it is precisely taking the actual stalk, so it
  states the displayed Hom bijection in the node. In particular every equivariant
  actual fibre map glues uniquely to a global map. It imposes no nonempty-fibre
  assumption and hence includes both empty fibres and an empty source fibre.
- `natural` is the equality of universal splitting sections for EVERY sheaf
  morphism, so all φ_F are natural.
- `complete` quantifies over ALL set sheaves F and asserts
  `T.finiteLevel F ↔ abelianTowerConstantAt F T.cone.pt`. In particular its
  right-to-left direction does not assume that F is already in L. This is
  exactly the final equality of full categories and finite-stage descent clause.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.profiniteToProEtOf`, the actual LC(S,Z) test objects.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`,
  and `Scheme.proetalePrecoverage`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; together with an
  actual Spec-to-scheme arrow this is the recorded geometric-point interface.
  Read `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`
  as well: it identifies those arrows with the point and residue embedding.
- The recorded finite-etale category match in
  `Mathlib.CategoryTheory.MorphismProperty.Comma` and `OverAdjunction` uses
  `MorphismProperty.Over` and `.Over.pullback`. Here its objects are expressed by
  the identical `IsFinite` and `Etale` structure-morphism predicates; no replacement
  finite-etale category or morphism restriction is introduced.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor` publicly imports the
  recorded stalk construction. Read its `geometricRingModuleStalkFunctor` and
  the full signatures/docstrings of `proEtaleGeometricStalkDiagram`,
  `proEtaleGeometricSetStalk`, and `proEtaleGeometricNeighbourhoodForget` in
  `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`; these are the set-stalk part
  of that same dependency node, used here.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage` is the recorded inverse-image construction.
- Reused generic profinite-product maps and constant-label sections from
  `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`:
  `Scheme.UniversalCover.profiniteProduct`, `.profiniteProductBase`,
  `.profiniteProductMap`, `.profiniteProductSection`. Their full definitions and
  source docstrings were read; no universal-cover hypothesis is imposed by them.
- Every recorded proof-dependency module is imported, including the object
  inverse-image restriction, weakly-etale localization, finite-constant
  representability, clopen decomposition, inverse-image stalk, sheaf morphism
  descent, site comparison, and locally-classical continuity modules.
  The Mathlib leaves use `CategoryTheory.yonedaEquiv` in
  `Mathlib.CategoryTheory.Yoneda` and
  `CategoryTheory.Functor.eval_section_surjective_of_surjective` /
  `nonempty_sections_of_finite_inverse_system` in
  `Mathlib.CategoryTheory.CofilteredSystem`.

Edge cases checked before writing: one-stage and trivial-group towers; directed
preorders; Q empty (no chosen element or nonempty hypothesis on any label set);
both fibres empty; nonempty source with empty target (no equivariant map, hence
no sheaf map); arbitrary disconnected test objects over connected X (the
universal-section predicate tests every object); and finite constancy only on X
(the unqualified `complete` clause supplies the finite stage). Empty X, empty
levels and an empty index set are excluded exactly by the original hypotheses.
U need not be assumed nonempty separately: a nonempty level already forces it.

Searches used the prescribed `msearch.py` wrapper with group Q15 and this item:

- LeanFinder: “Finite sheaves trivialized on a connected abelian Galois cover tower
  have unique normalized splittings, continuous monodromy and equivariant fibre maps
  descend”. Eight hits on abstract Galois-category connectedness, natural actions
  and representation lifting; no geometric tower or this normalized descent result.
- LeanSearch: “inverse systems of connected finite abelian torsors over a scheme
  and normalized finite sheaf descent”. Eight hits: generic `InverseSystem`
  declarations, sheaf abelianity and dense-subsite comparison; none states this.
- Loogle: `"Sheaf", "Action", "FullyFaithful"`: zero hits.
- Mathlib grep: `normalized.*splitting|abelian.*tower|Galois.*[Ss]heaf` in
  CategoryTheory: zero hits.
- `rg` of WeilConjectures and Sheaf for the item ID,
  `connected_abelian_tower|normalized_splitting`: no match. A broader review found
  SNCFiniteFibreData, SNCFiniteFibreClassification and PointedLimitCech; these
  address specialized SNC charts or universal covers, not the general tower.
- DAG search `connected abelian.*tower|abelian cover tower|finite abelian.*torsor.*tower`
  finds the item and its SNC finite-fibre parent only. `tools/blueprint_refs.py
  search 'abelian tower'` finds zero blueprint nodes. The ancestor tool confirms
  the inherited `blueprint.from.node = null`, which is preserved in the new node.

Read Bhatt--Scholze PDF printed pp.34--35 directly: Lemmas 5.1.1--5.1.4 and
Corollary 5.1.5. In particular the final clause uses finite-frame descent by the
same continuity mechanism as the corollary, as Q37's reviewed proof says.
No STATEMENT-DISPUTED and no mathematical node fault found.

Validation uses only scompile.py on the server, one file at a time, in dependency
order, followed by deliver2.py preflight. No local Lean compiler or global build.

## New nodes

`def-sfb-connected-abelian-cover-tower` packages precisely the item's geometric
and finite-group inverse-system hypotheses, their limit cones, the specified
(x,gx) comparisons and whole-scheme compatibility. Its Lean module is
`Sheaf.AlgebraicGeometry.ConnectedAbelianCoverTower`, declaring
`AlgebraicGeometry.ProEtale.ConnectedAbelianCoverTower` as a structure with real
fields. The source is Bhatt--Scholze §§4.2, 5.1 and the item's agent-formulated
finite connected torsor setup. The LeanSearch, LeanFinder, Loogle, Mathlib grep,
project searches and DAG/blueprint searches above found no existing general tower
notion; their results are recorded in this node's mathlib_searches. It uses the
recorded profinite test objects, proetale site and finite-etale predicates. It is
cited by the item, in the same chapter, with its inherited blueprint route.
All smaller helpers in the item's module package or construct parts of this one
normalized-descent assertion and are listed in lean.declarations.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
