## Worker report

This is a stage-2 statement delivery for lem-sfb-space-eventually-surjective-map,
not a new stage-1 split. The accepted Q04 split is preserved verbatim. The inherited
unchanged-item rejection concerned the former stage-1 attempt; the live node had no
Lean record and queue.tsv listed stage 2. No released repair note exists for this item.

The module Sheaf.AlgebraicGeometry.AlgebraicSpaceEventuallySurjectiveMap states
AlgebraicGeometry.AlgebraicSpace.eventually_surjective_of_isLimit, with sorry as
its sole theorem proof. Its helper spaceBaseChangeMap is actual data: the underlying
map produced by Mathlib's Over.pullback on Over.homMk f rfl. No arbitrary morphism,
existence choice, or postponed data is used.

The source is Stacks spaces-limits.tex, Situation 084W and Tag 07SN, read with its
proof. The node's strengthened-looking persistence clause follows by further base
change, exactly as its accepted proof says. The latest blueprint's direct-images
proof (3) was also read; this auxiliary limit statement changes no unit statement.

Hypotheses and clauses, matched individually:

- The scheme S is {S : Scheme.{u}}. Spaces over S are the existing AlgebraicSpace S,
  the full subcategory of fppf sheaves with representable diagonal and an étale atlas.
  Morphisms are the existing full-subcategory morphisms, hence natural transformations.
- The size convention uses explicit universe u. The directed index I : Type u is in
  the schemes' universe, with [Preorder I], [IsDirected I (· ≤ ·)] and [Nonempty I].
  No antisymmetry or countability restriction is imposed.
- The inverse system is D : Iᵒᵖ ⥤ AlgebraicSpace S. The binders hqc and hqs give,
  for every stage, CompactSpace on its existing point space and absolute
  quasi-separatedness. CompactSpace means precisely finite subcovers for open covers.
- Absolute quasi-separatedness is IsAbsolutelyQuasiSeparated, the affine-test
  characterization of Stacks 0AHR(3), equivalent to the absolute diagonal over Z
  being quasi-compact. This keeps the absolute condition even for non-qcqs S.
- Affine transitions are haff, for every arrow a of Iᵒᵖ, using the existing
  IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left). Testing all scheme bases
  with the scheme affine-morphism predicate is equivalent to the node's affine
  scheme-test definition, by Zariski locality. No transition-surjectivity assumption
  appears anywhere.
- The given limit B is c.pt, with c : Cone D and hc : IsLimit c. This is a limit
  in the category of algebraic spaces, not a limit of the underlying point sets.
- The distinguished stage is i₀ : I. X₀,Y₀ : Over (D.obj (op i₀)) and f₀ : X₀ ⟶ Y₀
  encode spaces over B_i₀ and their morphism over B_i₀, including its commuting triangle.
- hXqc, hXqs, hYqc, hYqs are exactly the four source/target qcqs assumptions.
- hlfp : MapIsLocallyOfFinitePresentation f₀.left uses the recorded compatible
  étale-chart test with the scheme LocallyOfFinitePresentation property. No flatness,
  separatedness, finite type, or additional finiteness of f₀ is imposed.
- The node's preliminary glossary for quasi-compact and quasi-separated morphisms,
  local finite type and finite presentation introduces no extra hypothesis: none of
  those properties of f₀ occurs in its conclusion or assumptions. The recorded
  MapIsQuasiCompact and MapIsLocally interfaces supply that glossary where needed.
- The limit base change f is spaceBaseChangeMap f₀.left.hom.hom Y₀.hom.hom.hom
  (c.π.app (op i₀)).hom.hom. Its source is the presheaf pullback of f₀ followed by
  Y₀'s structural map. By Over.w this composite equals X₀'s structural map, so this
  is exactly X₀ ×_{B_i₀} B, with target Y₀ ×_{B_i₀} B. Presheaf pullbacks of sheaves
  are their sheaf pullbacks; the recorded fibre-product theorem identifies the space.
- hf : Function.Surjective (mapPoint (...)) is surjectivity of |f|, not the stronger
  requirement of surjectivity on every section set. mapPoint uses the recorded
  field-valued point quotient and its canonical map.
- The conclusion ∃ (j : I) (hj : i₀ ≤ j), ∀ (i : I) (hi : j ≤ i), ... gives j ≥ i₀
  and surjectivity at every later i. The map used there is the same canonical pullback
  along D.map (homOfLE (le_trans hj hi)).op, namely B_i → B_i₀. In particular i=j
  and i₀=j are included. All proof terms in these signatures are structural data;
  the theorem itself remains sorry.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  AlgebraicSpace.IsRepresentableWith, IsEtale, IsSurjective, IsAlgebraicSpace.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback and etale_fibreProduct_isScheme.
  It is publicly exposed by AlgebraicSpaceMorphismProperties.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: PointRepresentative.map,
  pointImage and pointTopologicalSpace, built on Point and schemePointMap from
  AlgebraicSpacePointClasses. Used through the public dependency imports.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties:
  MapIsLocallyOfFinitePresentation, defined by MapIsLocally (@LocallyOfFinitePresentation).
- Sheaf.AlgebraicGeometry.ProperCurveModuli: mapPoint and MapIsQuasiCompact.
- def-weil-size-convention is a metatheoretic convention, so it has no declaration
  or module to import; its universe bounds are stated explicitly here.
- Mathlib.CategoryTheory.Comma.Over.Pullback: Over.pullback and its actual map.
- Mathlib.AlgebraicGeometry.Morphisms.Affine: IsAffineHom.
- The already stated proof dependency lem-weil-pbc-descend-surjective is imported
  privately from WeilConjectures.AlgebraicGeometry.DescendSurjective:
  AlgebraicGeometry.exists_surjective_of_isLimit. Its full signature and proof
  docstring were read. It concerns schemes, and is not itself this statement.
- The Mathlib proof leaf lem-weil-pbc-affine-scheme-qcqs matches
  Scheme.compactSpace_of_isAffine and quasiSeparatedSpace_of_isAffine; their
  modules are exposed by the affine/scheme descent imports. Other proof nodes
  currently have neither a Lean record nor a Mathlib match, so no module is invented
  for them. Their full proof roles are retained in the theorem docstring.

Edge cases checked mathematically before writing:

- The index set is nonempty as stated; the distinguished i₀ already supplies an
  element, so the explicit Nonempty instance imposes no further restriction.
- Empty sources, empty targets and empty limit bases are allowed. Surjectivity
  into an empty target is valid; an empty limit does not add any assumption that
  earlier bases are empty. The conclusion is the original finite-stage assertion.
- Constant systems and the stage i₀ itself use the same canonical base changes.
- Non-surjective affine transition maps are allowed, including closed immersions.
- Absolute quasi-separatedness is not replaced by quasi-separatedness relative to S
  or by topological QuasiSeparatedSpace of the point set. For X=S with S non-qs,
  the new affine-test predicate still detects the non-qc affine intersections.
- No independent smaller index universe, separation of S, reducedness, characteristic,
  field, or scheme-representability of B_i, X₀, Y₀ is required.

Searches made (actual msearch output is logged in searches.jsonl):

- leanfinder: "Surjectivity of a locally finitely presented morphism of algebraic
  spaces descends from an inverse limit to a finite stage" returned eight hits,
  beginning with scheme flat-descent statements. They do not quantify over spaces.
- loogle: "AlgebraicGeometry.exists_surjective_of_isLimit" returned zero hits
  (that project declaration is outside the service index). Its local source was read.
- grep: "eventually.*surject|descend.*surject" in Mathlib/AlgebraicGeometry returned
  ten fpqc descent hits, not inverse-limit descent for algebraic spaces.
- rg in lean/WeilConjectures and lean/Sheaf for eventual surjectivity, descent and
  the exact item id found scheme instances and unrelated sheaf results, no matching
  algebraic-space statement. The scheme exists_surjective_of_isLimit was examined.
- leansearch: "An algebraic space is quasi separated if the fibre product of two
  affine schemes mapping to it is quasi compact" returned eight hits about schemes
  and topological QuasiSeparatedSpace, not the algebraic-space absolute notion.
- loogle: "QuasiSeparatedSpace" returned twelve topological declarations; none
  represents quasi-compactness of the algebraic-space absolute diagonal.
- grep: "AlgebraicSpace|IsAbsolutelyQuasiSeparated" in Mathlib/AlgebraicGeometry
  returned zero hits. rg for absolute-quasi-separated/affine-map definitions in
  the project and upstream sources found no usable absolute-space predicate.
- blueprint_refs.py search "quasi-separated algebraic space" returned zero blueprint
  nodes; a DAG definition-node scan found only the general stack-qcqs node, with no
  usable recorded Lean declaration. No existing definition is copied.

No statement dispute or correction is necessary. The only changed fields of the
original node are lean and the added statement dependency described below.

Validation: scompile.py compiled each of the two delivered modules independently
in dependency order, both in sandbox and library-module mode, with no warnings or
errors. No global build or direct live-library edit was performed.

## New nodes

The new definition node def-sfb-space-absolute-quasi-separated owns
Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated and
AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated. It defines the absolute
algebraic-space condition by all pairs of affine scheme tests and quasi-compactness
of their sheaf fibre product, exactly Stacks 0AHR(3). The source proves equivalence
with the node's absolute-diagonal convention, without any condition on S. Its
statement cites the existing scheme, algebraic-space and point-topology nodes.
The recorded LeanSearch, Loogle and grep searches above found no declaration of this
notion; the DAG and blueprint searches found no existing usable definition node.
The item directly cites this new node. Its definition has real Prop-valued data and
no sorry. There are no dependency-module repairs or statement corrections.

Resumed validation: both modules compiled cleanly through deliver2.py. The first
dry-run preflight required the new node to carry import_flags; an empty list
was added as required by the live node schema. The accepted split and mathematical
statements remain unchanged.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
