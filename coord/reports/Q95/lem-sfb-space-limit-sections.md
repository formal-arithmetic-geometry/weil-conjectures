## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.globalFunctions_affine_limit` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceLimitSections`. The item statement and proof are
unchanged; its `stmt_deps` gains the new global-functions definition and two already
landed definition nodes for affine space morphisms and absolute quasi-separatedness.
There is one postponed theorem in the item and one defining comparison theorem in the
new definition module. All definition data are explicit; the comparison theorem is not
used to choose any data.

Clause-by-clause rendering:

- The base is `{S : Scheme.{u}}`. Every stage and the limit apex are objects of the
  existing `AlgebraicSpace S`, i.e. fppf sheaves with representable diagonal and atlas.
- The small nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. No least element is chosen in the statement.
- `D : Iᵒᵖ ⥤ AlgebraicSpace S` is the inverse system, and `c : Cone D` specifies X
  and all projections. `hc : IsLimit ((ObjectProperty.ι ...).mapCone c)` is explicitly
  the limit in fppf sheaves, as in the node, rather than only an abstract space limit.
- `hqc` says for every stage there exists an `Over S` scheme U and a map
  `yoneda.obj U ⟶ (D.obj i).obj.obj`, with `CompactSpace U.left`, `IsEtale a`,
  and `IsSurjective a`. This is exactly the specified quasi-compact atlas condition;
  both predicates include representability in their definitions.
- `hqs` uses the landed `IsAbsolutelyQuasiSeparated`: its affine-test formulation is
  Stacks 0AHR(3), equivalent to quasi-compactness of the absolute diagonal. It does not
  assume S quasi-separated and does not replace the absolute diagonal by the diagonal
  over S.
- `haff` uses the landed `MapIsAffine` for every transition. It is the affine-scheme
  test definition from the node; no schematicity of X_i or extra separatedness is added.
- The stage ring diagram is `D.op ⋙ globalFunctions`. This functor uses ordinary
  scheme regular functions on every scheme test and composition by the actual space
  morphism. Thus its transition maps and the cocone maps are precisely pullback maps.
- `IsIso (colimit.desc (D.op ⋙ globalFunctions)
  (globalFunctions.mapCocone c.op))` asserts that the actual canonical ring map is an
  isomorphism, with no unspecified ring equivalence or arbitrary comparison map.
- The next conjunct is `∀ a, ∃ i aᵢ, globalFunctionMap (c.π.app i) aᵢ = a`, exactly
  representation at a stage.
- The last conjunct quantifies over each i and two elements a,b of its ring, assumes
  equality of their pullbacks by the specified projection, and produces j together
  with `hij : i.unop ≤ j.unop` and equality under
  `globalFunctionMap (D.map (homOfLE hij).op)`. This is the eventual-equality clause.
- The general definition module keeps functions in `CommRingCat.{u+1}`: compatible
  families on all scheme tests have this size. The index remains `Type u`. A named
  public instance applies Mathlib `hasColimitsOfSizeShrink` to the existing colimits
  of commutative rings, so no universe equality or additional existence hypothesis
  is imposed. No file-local notation or instance is required.

Dependency sources read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, and `Scheme.Γ`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsEtale`, `IsSurjective`, `EtaleSite`, `etaleForget`, `structurePresheaf`,
  `structureSheaf`. The latter has exactly Γ(T,O_T) as its values.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`, used through the
  scheme-affine meaning in `MapIsAffine` and through proof dependencies.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.desc`, `Cocone`,
  `IsColimit`; `hasColimitsOfSizeShrink` supplies only the universe transport.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`:
  `AlgebraicSpace.MapIsAffine`.
- `Mathlib.Algebra.Category.Ring.Limits`: `RingCat.sectionsSubring`, reused for
  compatible regular functions rather than reimplementing ring operations.
- Proof-only imports are the recorded `AlgebraicSpaceFibreProductsEtaleCovers`
  (all three node declarations), `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`
  (`exists_limit_affine_transition`), and Mathlib `AffineTransitionLimit`
  (`nonempty_isColimit_Γ_mapCocone`, `exists_appTop_π_eq_of_isLimit`,
  `exists_appTop_map_eq_zero_of_isLimit`). Affine-scheme qcqs is in Mathlib;
  proof nodes for finite affine atlas, qcqs source products, and affine locality
  currently have no recorded Lean declaration and are not fabricated or imported.

Edge cases checked before writing: I must be nonempty as stated; it need not have a
least element or be antisymmetric. A singleton system yields the identity comparison.
Empty stages and the empty space are permitted: the zero ring is a commutative ring
and an empty scheme is an admissible quasi-compact atlas. No nonemptiness of any stage
or test is assumed. No transition map is required to be injective or surjective on
rings or on points. Arbitrary base schemes, including non-quasi-separated bases, are
allowed because the absolute criterion is used. Non-schematic qcqs spaces remain
allowed throughout. No smoothness, reducedness, field, or characteristic assumption
is introduced.

Searches performed (actual msearch logs are in searches.jsonl): LeanFinder query
"Global sections of an inverse limit of qcqs algebraic spaces with affine transitions
are the filtered colimit of global section rings" returned the scheme continuity
lemmas, not algebraic-space continuity. Loogle query
"AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone, CategoryTheory.Limits.IsColimit"
returned the same scheme theorem. Mathlib grep "AlgebraicSpace|algebraic space" in
AlgebraicGeometry returned zero hits. LeanSearch "Ring of global regular functions on
an algebraic space and pullback along morphisms" and LeanFinder "Ring of compatible
regular functions on every scheme mapping to an algebraic space and contravariant
functorial pullback" returned Scheme.Γ and locally ringed-space analogues. Mathlib
grep "globalFunctions|globalSectionsFunctor|sectionsSubring" found generic Sheaf.Γ,
which requires sheafification/right-adjoint infrastructure and gives no canonical
arbitrary-space-morphism pullback, plus the reusable sectionsSubring. Project rg in
WeilConjectures and Sheaf found no algebraic-space global-function functor; rg for the
item id in WeilConjectures found none. Existing H1AffineBaseChange uses a specified
limit cone on small etale charts, without a global-functions functor or pullback;
QuasiCoherentAlgebra defines commStructureSheaf only. These are not duplicate notions
of our functor. Scanning definition-node statements for global functions, global
sections and regular functions found no such definition. blueprint_refs.py searches
"global functions", "algebraic space global", "regular functions" returned 3, 0, 1
unrelated nodes respectively. `ancestor` reports no blueprint ancestor, so the new
node retains `blueprint.from.node = null` and the inherited route with the item prepended.

Sources read: spaces-limits.tex Situation 084R and lemma-descend-section (07SI),
spaces-properties.tex definition-structure-sheaf (03G7), and the latest blueprint
stability direct-images proof (3). The latter is the inherited route; no unit or
chapter statement is changed. No statement dispute or dependency interface fault.

## New nodes

`def-sfb-space-global-functions` defines the ring of compatible regular functions on
all S-scheme tests, canonical pullback by composition, and the contravariant functor.
It also states that restriction to the existing small etale site is bijective onto
its compatible sections, explicitly identifying this real construction with the node's
Gamma(X,O_X). The proof docstring constructs the extension by an etale atlas, scheme
pullback and gluing. Its source is Stacks 03G7 and the 07SI pullback/global-section
formula. The exact three logged search kinds and the project/DAG/blueprint searches
are in its mathlib_searches. The module provides explicit functionDiagram,
globalFunctionRing, globalFunctionMap, globalFunctions, globalFunctionEtaleRestriction,
the named comparison theorem, and the size-transport instance. It is cited directly
by the item. There is no data chosen from a sorry-backed existence theorem.

## Second reading by Q95

I reopened the node and both completed source files for a separate second pass.
The dispatcher prohibits starting other agents; this is a self-review, with the
maintainer's independent review still required. The match above was rechecked with
particular attention to the fppf-sheaf limit, absolute versus relative diagonal,
non-etale transition pullback, ring-colimit map, both element clauses, and universe
sizes. The global-functions restriction theorem supplies the identification with the
specified small etale structure sheaf, without changing the ring construction or
assuming any comparison as a hypothesis. Earlier dependent rewriting in functor laws
was replaced by congruence in the map of a fixed scheme test; this fixes elaboration
without mathematical hypotheses. The only size fix is Mathlib's existing shrinking
of colimit index universes. No item statement correction was needed.

Validation: scompile.py compiled both sibling modules separately in dependency order,
including their library names, with no errors and no warnings (3.5 s and 1.6 s).

Dry-run repair: fixed the recorded theorem signature, whose initial extraction stopped
at the named argument `(S := S)`. The record now contains the full verbatim signature.
