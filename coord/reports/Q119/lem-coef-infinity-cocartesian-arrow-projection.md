## Worker report

The module `Sheaf.CategoryTheory.CocartesianArrowProjection` states the Kerodon
Proposition the project server opposite-category cocartesian-arrow projection result.  It uses
`SSet.Enhanced.cocartesianArrowOfVertex` to convert a vertex of
`(ihom Δ[1]).obj E` into its represented arrow `Δ[1] ⟶ E`.  The full subcomplex
`cocartesianArrowSubcomplex p` keeps exactly vertices whose represented arrows are
`p`-cocartesian.  The target pullback is
`pullback (evaluation Δ[1] B 0) p`, i.e. pairs of a base arrow and an object over its
source.  `cocartesianArrowImageSubcomplex p` is the full subcomplex whose vertices
admit a cocartesian arrow with the displayed source and displayed image.  The
canonical map records the image under `(ihom Δ[1]).map p` and the source under
`evaluation Δ[1] E 0`; the named theorem
`cocartesianArrowCanonicalMap_range` supplies its factorization through the full image,
then `cocartesianArrowProjection` is that factorization.

The item's hypotheses render as the explicit binders `[Quasicategory E]`,
`[Quasicategory B]`, and `[InnerFibration p]` in
`cocartesianArrowProjection_isTrivialKan`.  The conclusion that the projection is a
trivial Kan fibration is rendered by
`SSet.modelCategoryQuillen.I.rlp (cocartesianArrowProjection p)`.  Mathlib's `I` is
the family of all boundary inclusions; its dimension-zero member gives surjectivity
on vertices, and dimensions `n ≥ 1` give fillers for every
`∂Δ[n] ↪ Δ[n]` with the prescribed boundary and prescribed simplex in the target.
Since the target is the full subcomplex on the vertex image, this imposes no lift
requirement for pairs outside that image.

Dependency declarations used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declarations
  `SSet.Enhanced.fullSubcomplex`, `SSet.Enhanced.diagramVertex`,
  `SSet.Enhanced.evaluation`, and the internal functor simplicial set `(ihom Δ[1]).obj`.
* `Sheaf.CategoryTheory.InfinityFibrations`, declarations
  `SSet.Enhanced.IsCocartesianEdge` and `SSet.InnerFibration` (via the class
  `[InnerFibration p]`).
* The Mathlib dependency `SSet.modelCategoryQuillen.I` and its `rlp` predicate,
  recorded by `def-weil-pbc-trivial-kan-fibration`; this is the boundary lifting
  definition including degree zero.

Edge cases checked: `n = 0` is covered by `I.rlp` and gives vertex surjectivity;
positive dimensions include `n = 1`; the source and base simplicial sets may be empty;
no cocartesian lift is required for a pair not in the full image; and the identity map
case reduces to the usual boundary lifting map on the cocartesian-arrow subcomplex.
The source and target use one fixed universe `u`, and all variables are explicitly
bound (`autoImplicit false`).

Searches made: `msearch.py Q119 ... leanfinder` for the cocartesian-arrow projection
returned only general Quillen lifting and ordinary-category cocartesian declarations,
with no matching theorem; `msearch.py ... loogle "Cocartesian", "fibration"` returned
no hits; `msearch.py ... grep "cocartesian|cartesian|trivial.*fibration"`
found only an unrelated comment in Mathlib's `StrictBicategory.lean`; `rg` over
`WeilConjectures/` and project `lean/Sheaf` found no existing statement of this
projection.  The dependency modules and their recorded declarations were read in full.
No `STATEMENT-DISPUTED` flag or node correction is needed.

## Second reading by Q119

I opened the item node, its Kerodon source place (01VK), the dependency records, and
`Sheaf/CategoryTheory/CocartesianArrowProjection.lean` independently.  The statement
matches item by item:

* The fixed containing universe is rendered by `universe u`, and the simplicial sets
  `E`, `B` and all maps use `SSet.{u}`.  The map `p : E ⟶ B` is the displayed Lean
  argument.  The instances `[Quasicategory E]`, `[Quasicategory B]`, and
  `[InnerFibration p]` are exactly the node's hypotheses that `p` is an inner
  fibration between quasicategories; no cocartesian-fibration or existence instance
  is added.
* The node's `Y` is rendered by
  `cocartesianArrowSubcomplex p`, the full subcomplex of
  `((ihom Δ[1]).obj E)` whose vertex predicate is
  `IsCocartesianEdge p (cocartesianArrowOfVertex h)`.  The helper
  `cocartesianArrowOfVertex` is the unit-hom adjunction identifying an internal-hom
  vertex with its arrow `Δ[1] ⟶ E`, so this is the same object rather than a private
  arrow encoding.
* The node's
  `R = Fun(Δ[1], B) ×_{B,ev_0} E` is rendered by
  `cocartesianArrowProjectionTarget p :=
  pullback (evaluation Δ[1] B (stdSimplex.obj₀Equiv.symm 0)) p`.  The first and second
  pullback projections are respectively the base arrow and the source object.
* The node's `θ(u) = (pu,u(0))` is rendered by
  `cocartesianArrowCanonicalMap p`, whose two legs are the internal-hom map of `p`
  and evaluation at vertex `0`; its pullback compatibility is supplied by the named
  postponed theorem `cocartesianArrowCanonicalMap_condition`.
* The node's `Z` is rendered by `cocartesianArrowImageSubcomplex p`, full on the
  pullback vertices `z` for which there is an `e : Δ[1] ⟶ E` with
  `IsCocartesianEdge p e` and the two explicit equalities identifying its source and
  its image with the pullback projections.  This is exactly “belongs to the image of
  `θ`”, with no extra lift hypothesis for other vertices.
* The factorization `θ : Y ⟶ Z` is rendered by
  `cocartesianArrowCanonicalMap_range` followed by
  `cocartesianArrowProjection := Subcomplex.lift ...`.  Thus the conclusion is about
  the codomain `Z`, not all of `R`.
* The conclusion that `θ` is a trivial Kan fibration is rendered by
  `SSet.modelCategoryQuillen.I.rlp (cocartesianArrowProjection p)`.  The recorded
  Mathlib match for `def-weil-pbc-trivial-kan-fibration` identifies `I` with all
  boundary inclusions, including `∂Δ[0] = ∅`; hence this is precisely vertex
  surjectivity plus the node's boundary lifting condition for every `n ≥ 1`, with
  equality on the boundary and over the prescribed simplex.

I checked the source orientation carefully: Kerodon 01VK states the cartesian,
target-endpoint version over `ev_1`; the node explicitly requests its opposite-category
dual, and the Lean uses cocartesian edges, source endpoint `0`, and `ev_0` throughout.
The six proof steps in the node are carried in the theorem docstring: vertex-image
factorization and surjectivity; dual prism filtration; boundary uncurrying and gluing;
inner-horn induction; the cocartesian outer-horn attachment; and currying back to the
required lift.  The inline pullback-compatibility proof was extracted to the named
postponed theorem `cocartesianArrowCanonicalMap_condition`, following AGENTS.md §5.
All three theorem proofs are now `sorry`; all definition data remain explicit.

Edge cases checked: `n = 0` is represented by the `I` generator
`∂Δ[0] ⟶ Δ[0]` and gives vertex surjectivity; `n = 1` is included among positive
dimensions; empty `E` or `B` gives empty source/image where appropriate; a pair outside
the full image is never a target vertex and needs no lift; and `p = 𝟙` reduces to the
boundary lifting map on the cocartesian-arrow subcomplex.  The single universe does not
exclude any case because the node itself specifies a fixed containing universe.

Searches were repeated with `msearch.py` LeanFinder and LeanSearch queries for the
cocartesian-arrow projection and relative cocartesian lifting, Loogle's
`"Cocartesian", "fibration"`, and `rg` over Mathlib, `WeilConjectures/`, and the
project's `lean/Sheaf`.  The new LeanFinder query returned generic Quillen `I/J` lifting predicates
and `SSet.Subcomplex.fromPreimage`/`lift`; LeanSearch returned ordinary subcomplex
image/factorization results, which do not construct the full vertex image or assert
this cocartesian-arrow lifting result. Loogle returned zero hits. The independent
`rg` searches also found no declaration of this projection or its theorem.  The dependency declarations
`SSet.Enhanced.fullSubcomplex`, `diagramVertex`, `evaluation`,
`SSet.Enhanced.IsCocartesianEdge`, `SSet.InnerFibration`, and Mathlib's
`SSet.modelCategoryQuillen.I` were read at their recorded source locations.  The mathematical signature was retained. I repaired the H5/H6 inline compatibility
proof by extracting the named postponed theorem, added the H9 ordinary proof import
`Sheaf.CategoryTheory.RightPrismBoundary`, switched the fibration import to the
current recorded public reexport `InfinityFibrationsOverSimplicialBases`, and
expanded the H8 proof docstring to
carry all six steps. The item's `lean.declarations` includes the added helper, and
its `lean.note` describes the compatibility and range theorems. No natural-language
node statement or dependency was changed.

The independent semantic search queries were:

* LeanFinder: “The restriction from cocartesian arrows in an inner fibration to their
  base arrow and source is a trivial Kan fibration onto the full subcomplex on its
  image vertices”. Its eight hits were generic horn/Quillen lifting declarations
  and `Subcomplex.fromPreimage`/`lift`, not this statement.
* LeanSearch: “For simplicial sets the subcomplex of cocartesian arrows maps by a
  trivial Kan fibration to its image under evaluation at the initial endpoint and
  the base map”. Its eight hits described `Subcomplex.image`, `toImage`, `lift`, and
  their structural properties, not a full vertex-image cocartesian-arrow theorem.
* Loogle: `"Cocartesian", "fibration"`, zero hits.
* Direct `rg`: `cocartesianArrowProjection|cocartesianArrowSubcomplex|IsCocartesianEdge`
  over Mathlib, upstream `WeilConjectures`, and `lean/Sheaf`. The project uses the
  existing `IsCocartesianEdge` in several modules but has no duplicate of this
  projection. I also inspected `fullSubcomplex`, `diagramVertex`, `evaluation`,
  `InnerFibration`, `I`, `boundary`, `boundary_zero`, and `MorphismProperty.rlp`
  directly, rather than inferring their meaning from their names.

Validation: `scompile.py Q119 lem-coef-infinity-cocartesian-arrow-projection
lean/Sheaf/CategoryTheory/CocartesianArrowProjection.lean` compiled the final module
cleanly. The shared signature reader reproduces `lean.statement` exactly under its
whitespace normalization, all nine declarations are recorded, and no Lean line exceeds
100 characters. There are no new nodes or dependency modules in this delivery.
