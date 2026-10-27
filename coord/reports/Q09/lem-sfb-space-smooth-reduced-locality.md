## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.smooth_reduced_locality` in
`Sheaf.AlgebraicGeometry.SpaceSmoothReducedLocality` and supplies the missing reducedness
predicate in `Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`. Nothing is proved: the theorem
has `sorry`; the definition has its complete quantifier data and no proof obligation.

The earlier worker ending was a stage-1 supersession, not a stage-2 blocker. The live item
is split and reviewed by Q56, queue stage 2, with no Lean record and no repair note. The
2026-10-22 handoff in brief-stage2 section 0 explicitly authorizes proceeding. This delivery
preserves its statement, proof, proof dependencies, and review metadata.

Clause correspondence:
- Base scheme S: `{S : Scheme.{u}}`, using the existing Scheme definition.
- Algebraic spaces over S: `{X Y : AlgebraicSpace S}`; these are the recorded full subcategory
  of fppf sheaves with representable diagonal and an etale surjective scheme atlas.
- Morphism f: `(f : X ⟶ Y)`, the full-subcategory natural transformation.
- Smoothness on etale scheme charts: `(hf : MapIsLocally (@Smooth) f)`. Unfolding MapIsLocally
  quantifies every compatible pair of representable etale scheme charts and asserts
  Mathlib Smooth on the scheme map. It does not assume representability of f.
- Reducedness: `AlgebraicSpace.IsReduced X` is `∀ T : X.EtaleSite,
  AlgebraicGeometry.IsReduced ((etaleForget X).obj T)`. Objects of EtaleSite are precisely
  schemes over S with representable etale maps to X. Mathlib scheme reducedness is
  equivalent to reducedness of all local rings (isReduced_of_isReduced_stalk and
  isReduced_stalk_of_isReduced, Properties.lean).
- First assertion: `(IsReduced Y → IsReduced X)`.
- Surjectivity on field-valued point classes: `∀ p : Point Y.obj.obj,
  p ∈ pointImage f.hom.hom`, using the exact recorded pointImage definition: every target
  class is the image of a source field-valued representative.
- Second assertion: the second conjunct is that surjectivity implies
  `IsReduced X → IsReduced Y`. Surjectivity is required only for descent.

Dependencies read and reused:
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace, IsEtale,
  EtaleSite and etaleForget, with their scheme-test signatures and docstrings.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: PointRepresentative.map, pointImage,
  pointTopologicalSpace; Point comes from AlgebraicSpacePointClasses.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsLocally, the existing
  generic compatible-chart predicate. Its owning landed node is added to stmt_deps.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsReduced, via the new node.
- The available proof dependencies are imported plainly: SchemeEtaleSourceTargetProperties,
  SpaceEtalePresentationPropertyCriterion, ChartwiseEtalePermanence,
  AlgebraicSpaceFibreProductsEtaleCovers, EtaleSmoothZeroDimensionalFibres, the Mathlib Etale,
  faithfully-flat algebra, RingHom.Flat and Smooth.Flat modules. The source docstring gives
  all six accepted proof steps and their dependency identifiers. The two unstated proof
  dependencies lem-sfb-smooth-algebra-over-reduced-ring and
  lem-sfb-space-smooth-surjective-fppf-locality have no module to import; neither is needed
  to type this statement. No import cycle is introduced.

Sources read: spaces-descent.tex lemma-reduced-local-smooth (Tag 0GB3), including its proof;
spaces-properties.tex lemma-type-property (Tag 03E8), definition-type-property, and the
reduced entry in remark-list-properties-local-etale-topology. These give exactly the two
implications and the chart definition used here. No statement correction or dispute.

Edge cases checked before writing: the empty algebraic space is reduced; an empty source
with arbitrary reduced target satisfies ascent; in descent point-surjectivity of an empty
source forces the target empty. The identity and isomorphism cases give unchanged reducedness.
No quasi-compactness, Noetherianity, finite type, characteristic, relative dimension, or
separation assumption is imposed. A single universe u is the existing size convention for
schemes over S, with all charts in Over S and point classes in Type (u+1). No independent
smaller test-scheme universe is introduced. autoImplicit is false in both files.

Searches (msearch.py, Q09/item, outputs retained in searches.jsonl):
- leanfinder: "Reducedness ascends along smooth morphisms of algebraic spaces and descends
  along surjective smooth morphisms": eight hits, scheme open-immersion reducedness and
  scheme smoothness results; no match.
- loogle: `"IsSmooth", "IsReduced"`: zero hits.
- grep: `IsSmooth.*IsReduced|IsReduced.*IsSmooth|AlgebraicSpace` in AlgebraicGeometry:
  zero hits.
- leansearch and leanfinder: "An algebraic space is reduced if every etale scheme chart
  is reduced": eight hits each, all about schemes or geometrically reduced algebras.
  Their full signatures and docstrings were read; none accepts AlgebraicSpace.
- grep: `AlgebraicSpace|reduced algebraic space|reduced.*etale.*chart`: zero Mathlib hits.
- rg of WeilConjectures for reducedness/smoothness found the smooth-over-a-field theorem
  and related scheme-only material; no theorem for general algebraic spaces. Literal
  item-id search there has no hits. rg of Sheaf found no algebraic-space IsReduced.
- DAG full-text searches for reduced algebraic spaces found statement nodes which use the
  notion, including reduced-closed-support and singleton-field-factorization, but no owning
  definition. blueprint_refs.py search "reduced algebraic space": zero blueprint nodes.
  blueprint_refs.py ancestor item: None, so the new node preserves null ancestry and the
  item's via chain with the item prepended.

Validation: both files compiled separately, in dependency order, through the mandated
scompile.py server wrapper (all phases successful, roughly two seconds per compile).

## New nodes

`def-sfb-reduced-algebraic-space` defines exactly the all-etale-scheme-chart condition in
Tag 03E8 and definition-type-property, applied to reduced schemes. The definition reuses
EtaleSite, etaleForget and Mathlib IsReduced; it neither chooses an atlas nor duplicates
scheme reducedness. LeanSearch, LeanFinder, Mathlib/project grep and DAG/blueprint searches
above show that no existing definition node or Lean declaration supplies this notion.
It has its own module and is added directly to the item's stmt_deps.

## Second reading by Q09

The dispatcher explicitly forbids starting other agents, so this is a fresh self-review,
not a claim of independent authorship; the maintainer's independent delivery review remains
required. Reopened the source node, both source modules and the Stacks source passages.
The four original dependencies retain their recorded interfaces. Checked the smoothness
hypothesis unfolds to all commuting etale chart squares, rather than a representable-map
condition; checked reducedness quantifies all EtaleSite objects rather than one chosen
chart; checked the point-image quantifier covers every target field-valued point class;
checked the conjunction has exactly ascent and conditional descent and no extra hypotheses.
The only added statement dependencies are the existing owner of MapIsLocally and the new
reducedness definition. No statement correction, mismatch, hollow data, hidden choice,
unbound universe, or excluded empty case was found. No changes needed after this reading.
