## Worker report

The module `Sheaf.Compactification.BoundaryRefinement` states exactly the current
main-20261015 node `det-nagata-definition-refinement`. Its main declaration is
`AlgebraicGeometry.Compactification.BoundaryCompactification`. The node's
statement and dependency list are unchanged; the node copy changes only `lean`.
No new DAG node or dependency module is needed.

The defining clauses match as follows (the module namespace throughout is
`AlgebraicGeometry.Compactification`):

- A morphism of schemes `f : X ⟶ S` is bound explicitly, with both schemes in
  arbitrary universe `u`. Both compactifications use the recorded
  `AlgebraicGeometry.Compactification f`, with middle scheme `.Z`, open map `.i`,
  proper map `.g`, factorization `.comm`, and the existing open/proper instances.
- The requirement that both open immersions be quasi-compact is the object
  condition `QuasiCompact c.i` in `QuasiCompactObjects f`. Every object of
  `BoundaryCompactification f` contains a compactification and this proof.
  The main-20261015 dependency update permits a non-quasi-compact open immersion
  in a general compactification, so this item's explicit extra condition is
  retained here; it is not silently assumed to follow from the structure.
- For source `c'` and target `c`, the underlying morphism in
  `QuasiCompactObjects f` is the upstream `c'.obj.Refinement c.obj`. Its `.hom`
  is the required map of ambient schemes. For objects `c' c` in the final
  category and `r : c' ⟶ c`, the ambient map is `r.hom.hom.hom`.
- Condition 1, being over `S`, is the upstream field
  `r.hom.hom.hom_g : r.hom.hom.hom ≫ c.obj.obj.g = c'.obj.obj.g`.
- Condition 2, agreement on `X`, is the upstream field
  `r.hom.hom.i_hom : c'.obj.obj.i ≫ r.hom.hom.hom = c.obj.obj.i`.
- Condition 3 is `r.property`, whose type is exactly
  `r.hom.hom.hom ⁻¹ᵁ c.obj.obj.i.opensRange = c'.obj.obj.i.opensRange`.
  The definition `boundaryRefinementProperty` uses equality in `Scheme.Opens`.
  An open subscheme has the restricted structure sheaf, so this is equality as
  open subschemes, not an equality of arbitrary scheme structures or an added
  density hypothesis.
- The explanatory restriction to `j ∘ (j')⁻¹` is precisely the second triangle
  equality after identifying each open immersion with its image. Conversely,
  that identification recovers the same triangle equality. The boundary
  interpretation is the complement formulation of the third condition: a
  point outside the source open cannot map into the target open. No separate
  arbitrary comparison or chosen isomorphism is introduced.
- Identity and composition of ambient maps come from the existing upstream
  category. The named theorem `boundaryRefinementProperty_isMultiplicative`
  states closure under identities and composition. Its proof is `sorry`, with
  the full argument from the node in its docstring: identity preimage, followed
  by the iterated-preimage formula and the two input open equalities. This is
  the sole postponed theorem and is the identity/composition statement already
  contained in this DAG node. The two triangle equalities are retained by the
  upstream category's identity and composition.
- `BoundaryCompactification f := WideSubcategory (boundaryRefinementProperty f)`
  equips exactly these objects and refinements with Mathlib's category
  structure; no category laws are asserted for arbitrary supplied operations.
- `DenseBoundaryCompactification f` is the `ObjectProperty.FullSubcategory`
  defined by `IsSchemeTheoreticallyDominant c.obj.obj.i`. This is the recorded
  dense-compactification predicate, in the form of its main-20261015 update.
  `denseBoundaryInclusion f` is the standard fully faithful inclusion. The
  standard `Full` and `Faithful` instances apply to it, so no morphisms between
  dense objects are discarded beyond the ambient three refinement conditions.

Dependency declarations read and used:

- `WeilConjectures.Compactification.Defs`:
  `AlgebraicGeometry.Compactification`, full structure and docstring, and its
  `quasiCompact_openImmersion_iff`. The structure is imported through
  `WeilConjectures.Compactification.Refinement`, which supplies the two triangle
  equalities and category operations used here.
- `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`:
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant`, defined by `f.ker = ⊥`.
  The current dense-dependency update expressly uses this predicate; because
  the objects here have quasi-compact open maps, it also agrees with the
  injectivity formulation in the older dependency text.
- Mathlib's `ObjectProperty.FullSubcategory`, its inclusion `ObjectProperty.ι`,
  and `WideSubcategory` are the existing category constructions used directly.

Searches before writing:

- `msearch.py ... leanfinder` with query "A refinement of scheme
  compactifications preserves the open subscheme: inverse image of the open
  image is the source open image" returned eight hits, including
  `Scheme.Hom.preimage_image_eq`, `resLE_preimage`, and `preimageIso_inv_ι`.
  None defines this compactification-refinement category.
- `msearch.py ... loogle "AlgebraicGeometry.Compactification.Refinement"`
  returned zero hits (unknown identifier in the Mathlib search service).
- `msearch.py ... leansearch` with query "Refinement of compactifications of a
  scheme morphism with inverse image of the open subscheme equal to the source
  open subscheme" returned eight hits about quasi-compact morphisms, open
  immersions, and restricted schemes, with no refinement definition.
- `msearch.py ... grep "Compactification|Refinement" AlgebraicGeometry`
  returned fifteen hits about cover refinements; no compactification structure.
- `rg` on upstream `WeilConjectures` found
  `Compactification.Refinement`, read in full locally and confirmed by
  `scompile.py --source WeilConjectures.Compactification.Refinement`.
  It has only `hom`, `i_hom`, and `hom_g`: not an exact match, since the third
  condition is absent. `RefinementPullback.lean` was also read: its cartesian
  statement requires density of the source and quasi-compactness. The present
  node does not assume density for arbitrary compactifications.
- `rg -n 'det-nagata-definition-refinement'` on upstream found no binding.
  Searches for refinement, boundary-preserving refinement, `BoundaryCompactification`,
  `StrictRefinement`, and the proposed names in Mathlib, upstream, and
  `lean/Sheaf` found no existing definition of this three-condition category.
  Existing project modules use the weaker upstream refinement interface.

Edge cases checked before writing:

- The source `X` may be empty: both distinguished opens are empty; inverse
  images of the empty open are empty, and ambient proper schemes remain
  arbitrary. No nonempty, finite-type, reduced, or Noetherian hypothesis is
  introduced.
- The open may be the whole middle scheme; identities satisfy the equality.
  The composite-open equation is valid also for empty or whole opens.
- Density is imposed only on the dense full subcategory, not on the ambient
  category or on refinement maps.
- The boundary condition is not redundant. For `f = id_S`, the compactification
  with ambient `S ⨿ S`, open inclusion of the first summand, and proper fold map
  admits an upstream refinement to the identity compactification. Its second
  summand maps into the target open, so it fails condition 3 (take, for example,
  `S = Spec(k)`). Thus recording upstream `Refinement` as an exact existing
  match would omit a genuine clause.
- Quasi-compactness is attached to each object's open immersion, not an
  arbitrary extra property of a refinement; non-quasi-compact compactifications
  are excluded exactly as this item's opening sentence requires.
- Object universe is `u + 1` and morphism universe is `u`, inherited from
  `Scheme.{u}`; no universe equality or size restriction is added.

Validation: the delivered file compiled cleanly via `scompile.py`. A separate
sandbox consumer probe additionally checks the category instances for both
object types, fullness and faithfulness of the dense inclusion, the two
triangle projections, the third-condition projection, quasi-compactness of
objects, and the density projection. The probe is not part of the delivery.
Every definition has actual data. There is no statement correction and no
STATEMENT-DISPUTED fault.

Published-base reconciliation: the shared checkout still had the imported node;
the first dry run detected that the published node had already received its
stage-1 split. I read that current node directly from the server and refreshed
the sandbox copy, retaining its statement, all seven dependencies, the four
proof steps, and every other field. The current split makes explicit the same
restricted-sheaf meaning of open subschemes, underlying-set boundaries,
quasi-compact object class, and meaning of a full subcategory already used in
this module. This is a base refresh, not a statement correction.

The additional recorded dependency interfaces in that current split were read
in full at their declarations and are used as follows:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`, including the existing scheme
  category. These give every object and ambient map here.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` records
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`;
  the latter's actual class in `Morphisms.QuasiCompact` is the object predicate
  used here. No finite-type assumption on `f` is added.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, supplied by each compactification's
  existing instance. Its `Scheme.Hom.opensRange` is the actual open image in
  condition 3.
- `def-weil-scheme-over-base`: `Mathlib.AlgebraicGeometry.Over`,
  `AlgebraicGeometry.Scheme.Over` / `Scheme.Hom.IsOver`. The signature of
  `Scheme.Hom.isOver_iff` identifies the over-base condition with exactly
  `h ≫ p = p'`. Here the source already names the two structure morphisms
  explicitly, and that equality is the existing `Refinement.hom_g` field;
  there is no second scheme-over-base definition or implicit choice of a
  structure map.
- `def-nagata-category`: `Mathlib.CategoryTheory.Category.Basic`,
  `CategoryTheory.Category` extending `CategoryStruct` with `id_comp`,
  `comp_id`, and `assoc`. The compiled category instances for both object
  types have exactly this type. The full-subcategory and wide-subcategory
  constructions transport the existing scheme-map identities and composites.

These standard notions are imported transitively through the dependency and
subcategory modules actually used by the definitions. No additional node is
restated. The only local postponed theorem covers current proof Steps 2--3;
the restriction/boundary explanation of Step 1 is encoded by the two triangles
and open equality, and Step 4 is the standard category/full-subcategory data.

## Second reading by Q56

I independently read the sandbox node, all seven dependency records and their
declarations, the complete Lean module, and the current main-20261015 source
`sec-nagata-compactification/sk-def-nagata-sketch-data/det-nagata-definition-refinement.md`.
This node's source is the blueprint definition, not a Stacks tag. I also read
the unit's `_section.md`, the current compactification and density definition
sources, upstream `Compactification.Defs`, `Refinement`, and `RefinementPullback`,
and the Mathlib full/wide-subcategory implementations. I checked the current
server node records and obtained both upstream compactification modules with
`scompile.py --source`; their operative declarations agree with those read here.
There is no maintenance repair note for this item.

The source-to-Lean checklist, with `c' c : BoundaryCompactification f` and
`r : c' ⟶ c`, is as follows. Every entry passes.

1. Objects `X`, `S` and the fixed scheme morphism `f : X ⟶ S` are the explicit
   binders `{X S : Scheme.{u}} (f : X ⟶ S)`. `Scheme` and `Scheme.Hom` are the
   recorded `def-pc-scheme` declarations. No property of `f` is assumed.
2. Each compactification has ambient scheme, proper structure map, open
   immersion, and factorization: `c.obj.obj.Z`, `.g`, `.i`, and `.comm` in the
   recorded upstream `Compactification f`, with its existing `isProper` and
   `isOpenImmersion` instances. The same projections apply to `c'`. This is
   actual factorization data, not arbitrary ambient maps or an existence choice.
3. Both open immersions are quasi-compact. `QuasiCompactObjects f` is exactly
   `ObjectProperty.FullSubcategory (fun c : Compactification f ↦ QuasiCompact c.i)`;
   thus `c.obj.property` and `c'.obj.property` express the two required proofs.
   This uses the recorded `QuasiCompact` class, without adding finite type,
   Noetherian, reduced, separated-base, or base quasi-compactness hypotheses.
4. A refinement has exactly the ambient scheme morphism
   `r.hom.hom.hom : c'.obj.obj.Z ⟶ c.obj.obj.Z` and properties. Condition 1
   is `r.hom.hom.hom_g`, of type
   `r.hom.hom.hom ≫ c.obj.obj.g = c'.obj.obj.g`. This is the required
   `S`-morphism condition with the explicitly named structure maps; it agrees
   with `Scheme.Hom.isOver_iff` from the over-base dependency.
5. Condition 2 is `r.hom.hom.i_hom`, of type
   `c'.obj.obj.i ≫ r.hom.hom.hom = c.obj.obj.i`. Its direction agrees with
   `h ∘ j' = j`, using Lean's diagrammatic composition order.
6. Condition 3 is `r.property`, of type
   `r.hom.hom.hom ⁻¹ᵁ c.obj.obj.i.opensRange = c'.obj.obj.i.opensRange`.
   The dependency's `IsOpenImmersion` gives the actual open images. Both
   sides are `Scheme.Opens` and denote their canonical restricted-sheaf open
   subschemes, so this neither weakens the equality nor chooses new structures.
7. The restriction and boundary explanation is faithfully encoded by entries
   5 and 6. Factoring the open immersions through their images makes the
   restriction `j ∘ (j')⁻¹`; entry 5 already implies that the source open lies
   in the inverse image. Entry 6 adds precisely the complementary containment:
   each boundary point maps into the target boundary. No closed scheme
   structure on either boundary is supplied or required.
8. Identity and composition use the upstream ambient identity and composite.
   `boundaryRefinementProperty_isMultiplicative` states exactly closure of
   condition 3 under these operations. Its docstring gives the identity
   inverse-image calculation and, for the composite, the iterated inverse
   image followed by substitution of the two hypotheses (node Steps 2--3).
   The upstream operations preserve the two triangles. `WideSubcategory`
   then supplies the category axioms from the scheme category (node Step 4).
   Nothing asserts the category laws for arbitrary operations.
9. The dense objects are exactly
   `IsSchemeTheoreticallyDominant c.obj.obj.i` in
   `DenseBoundaryCompactification f`. `ObjectProperty.FullSubcategory` retains
   every ambient refinement between those objects. `denseBoundaryInclusion f`
   is its standard inclusion, whose `Full` and `Faithful` instances were
   checked in the consumer probe. No density restriction is placed on the
   ambient category or on its general refinement arrows.

The older `statement` fields of the compactification and dense-compactification
dependencies differ from their explicit `blueprint_update` fields. I checked
those updates against the current source rather than treating the older text
as a new instruction: the compactification update permits any open immersion,
matching upstream `Compactification`; this item's object predicate separately
requires quasi-compactness. The density update is the largest quasi-coherent
ideal in the kernel being zero, precisely `IsSchemeTheoreticallyDominant`
(`f.ker = ⊥`). For these quasi-compact opens it also agrees with injectivity
in the older wording, as explained by the source and the Mathlib
`Scheme.Hom.app_injective` interface. Thus neither dependency needs a private
replacement or a dependency module. The category and over-base nodes have
Mathlib matches (`CategoryTheory.Category` and `Scheme.Over`/`Hom.IsOver`),
although their `lean` fields are absent; I opened those actual signatures.

Edge cases: an empty `X` gives empty distinguished opens, and condition 3 is
the valid empty-preimage equality; no nonemptiness is bound. If `S` is empty,
all existing objects and arrows are still admitted. An empty object category
is allowed when `f` has no such compactification; no `Nonempty` instance is
assumed. Whole distinguished opens and empty boundaries are included. Density
is scheme-theoretic, so no reduction hypothesis enters. There is no integer,
rank, index-set, or coefficient characteristic parameter to restrict. The
schemes and ambient schemes range over arbitrary `u`; objects live in
`Type (u + 1)` and arrows in `Type u`, with no additional universe equation.
The sole universe is explicitly bound; no implicit variable is left unbound.

Independent searches used different formulations from the worker's queries:

- LeanFinder: `category compactification refinement boundary inverse image
  open` returned eight topology/coborder/one-point-compactification results,
  none the scheme refinement category.
- LeanSearch: `Scheme compactifications with maps that send the complement of
  the source open into the complement of the target open` returned
  quasi-compactness and partial-map declarations, none this definition.
- Loogle: the upstream identifier query was unknown to the Mathlib service;
  I retried with `CategoryTheory.MorphismProperty.IsMultiplicative` and read
  the multiplicativity interface. Its twelve results are generic closure
  machinery, not this geometric predicate.
- `rg` in Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and the
  DAG searched compactification/refinement, the proposed declaration names,
  and inverse-image/open-range equalities. I opened upstream `Refinement`
  rather than accepting the name as a match: it imposes only the two
  triangles. `RefinementPullback.isPullback_of_isSchemeTheoreticallyDominant`
  supplies the open-preimage property only with density of the source and
  quasi-compactness; general objects here have no density hypothesis. Generic
  `WideSubcategory` and `FullSubcategory` are reused, not redefined. No exact
  existing definition was found.

The boundary condition is substantive even for a quasi-compact example: for
`S = Spec k`, the compactification of `id_S` with ambient `S ⨿ S`, distinguished
first summand, and proper fold map has an upstream refinement to the identity
compactification. The second summand maps into the target open, violating
condition 3. Conversely, every map satisfying the node's three conditions is
exactly one of the morphisms selected here; no properness assumption is added
to it (upstream derives properness from the two triangles).

No mathematical or signature mismatch was found, and no Lean or node field
was changed. The `lean.statement` is verbatim the signature of
`BoundaryCompactification`. All six declarations have source/blueprint
docstrings, all lines meet the 100-character limit, and definitions contain
real data. The sole postponed theorem is the named multiplicativity theorem;
it is the identity/composition clause of this node, with its complete proof
in the docstring. No theorem was proved. No new node, dependency module, or
statement correction is needed. The second reading adds this report only.

Validation: reran `scompile.py` on the delivered module and the existing
scratch consumer probe, separately compiled by the wrapper. The probe checks
both category instances, the dense inclusion's fullness and faithfulness,
and projections for all three arrow conditions, quasi-compactness, and
density. Both compiles completed without warnings. The prescribed
`deliver2.py Q56 det-nagata-definition-refinement --no-push` printed
`OK (dry run): commit 81bdd900c7 passes the preflight and compiles; nothing pushed`.
