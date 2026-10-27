## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceUnramifiedPermanence` states
`AlgebraicGeometry.AlgebraicSpace.space_unramified_permanence`, with one `sorry`
and no new definitions. The mathematical statement is unchanged.

Hypotheses and clauses:

- The base scheme is `{S : Scheme.{u}}`; all three arbitrary algebraic spaces
  are `{X Y Z : AlgebraicSpace S}`. The two morphisms are `(f : X ⟶ Y)` and
  `(g : Y ⟶ Z)`; `f ≫ g` is the paper's `g ∘ f`.
- Unramifiedness is `MapIsLocally (@AlgebraicGeometry.IsUnramified)`. Expanding
  the existing `MapIsLocally` quantifies over every pair of S-schemes U,V,
  representable etale maps a,b, and S-morphism h with
  `a ≫ f.hom.hom = yoneda.map h ≫ b`, and requires `IsUnramified h.left`.
  The latter is exactly local finite type and the open-immersion diagonal.
  Thus the statement includes local finite type on the charts, without a
  spurious finite-presentation or representability assumption on f.
- The first conjunct assumes the unramified chart tests for f and g and
  concludes the same test for `f ≫ g`.
- The second conjunct assumes only the unramified chart test for `f ≫ g`
  and concludes it for f. There is no condition at all on g.
- The third conjunct assumes the test for f, and quantifies over every
  `(Y' : AlgebraicSpace S)` and `(t : Y' ⟶ Y)`. Its conclusion is the test
  for `enlargedFibreProductFst t f`. This is the actual sheaf-pullback
  projection `Y' ×_Y X → Y'`; swapping the factors gives the node's
  `X ×_Y Y' → Y'`. No restriction is imposed on t. The existing construction
  bundles the sheaf fibre product with its proved algebraic-space predicate.
- The last conjunct assumes `MapIsLocally (@AlgebraicGeometry.Etale) f` and
  concludes the unramified test for f. This is exactly the stipulated chartwise
  interpretation of etale, not the stronger scheme-representable `IsEtale`
  predicate on the entire space morphism.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and its presheaf scheme-test predicates `IsRepresentableWith`, `IsEtale`,
  `IsSurjective`. These give the original category and the chart conditions.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`:
  `AlgebraicGeometry.IsUnramified`, the scheme predicate as recorded by
  `def-weil-unramified-morphism`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  the affine-locally etale scheme predicate recorded by
  `def-weil-etale-morphism`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally` from the already landed
  `def-sfb-space-morphism-properties`. That definition owner is added to
  stmt_deps so the shared universal chart test is explicitly cited.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicGeometry.AlgebraicSpace.enlargedFibreProduct` and
  `enlargedFibreProductFst`. Their definition owner is the already landed
  `def-sfb-space-sheaf-fibre-product` (existing: true, 2026-10-23), added to
  stmt_deps. Its recorded module is `EnlargedEtaleRingedSite`, already
  publicly imported by this delivery. The data are the actual sheaf pullback
  and its first projection; the algebraic-space predicate is supplied by
  `fibreProduct_isAlgebraicSpace`. No enlarged-ringed-site theorem is used
  to supply these definitions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers` is imported
  for the proof's fibre-product and cover permanence input.
- The Mathlib scheme proof inputs are imported from
  `Morphisms.FormallyUnramified`, `Morphisms.FiniteType`,
  `Morphisms.UnderlyingMap`, and the etale module: composition and
  `FormallyUnramified.of_comp`, `locallyOfFiniteType_comp`,
  `locallyOfFiniteType_of_comp`, `Etale.etale_comp`, `Etale.of_comp`, and
  the surjective-composition instance.
- `WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`:
  `AlgebraicGeometry.unramified_baseChange_restrict_open` is the recorded
  proof input for scheme unramified base change.
- The proof-only node `lem-sfb-unramified-etale-compatible-charts` has no
  Lean record or Mathlib match in the read repository; no module can yet
  be imported for it. The complete six-step proof in the docstring retains
  this planned chart-recognition input. It is not needed to type this statement.

One-definition searches, 2026-10-24:

- `msearch.py ... leanfinder` with query "Unramified morphisms of algebraic
  spaces stable under composition and base change and cancellation; etale
  implies unramified": eight results, all scheme/ring properties; no
  algebraic-space permanence statement.
- `msearch.py ... loogle 'AlgebraicGeometry.AlgebraicSpace, IsUnramified'`:
  zero hits, the Mathlib search environment has no algebraic-space identifier.
- `msearch.py ... grep 'unramified|Unramified' AlgebraicGeometry`: thirteen
  hits, all scheme predicates and their descent inputs.
- `msearch.py ... leansearch` with query "Unramified morphisms of algebraic
  spaces are stable under base change and composition and left cancellation":
  eight scheme/ring results; no algebraic-space assertion.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib for unramified,
  compatible charts and chartwise predicates located `MapIsLocally` and
  `SpaceChartwiseUnramified` (`SpaceUniversalConormal.lean:62`). The latter
  has exactly the same expansion as the specialization used here. We reuse
  the generic existing definition, and do not declare another specialization.
  No space permanence theorem was found, including the candidate names
  `space_unramified_permanence`, `unramified_permanence`, and
  `unramifiedPermanence`. Searching the upstream source for this node id
  returned no match.
- `tools/blueprint_refs.py search unramified` and
  `tools/lean_names_upstream.py show lem-sfb-space-unramified-permanence`
  gave no existing statement for this item. The former listed unrelated
  blueprint nodes concerning weights/ramification and convention nodes.

Sources read: `literature/stacks-project/spaces-morphisms.tex`, the definition
of unramifiedness and the full statements/proofs at labels
`lemma-composition-unramified`, `lemma-base-change-unramified`,
`lemma-permanence-unramified`, `lemma-etale-unramified` (03ZI, 03ZJ, 06G6,
06CR). These agree with the node. The proof docstring renders all six DAG
proof steps and names their inputs.

Edge cases checked before writing: empty source and empty target, identity
maps, arbitrary non-etale/non-finite-type second map in cancellation,
arbitrary (including empty) base change, and nonrepresentable space maps.
All are allowed by the binders. Empty charts impose the ordinary empty-scheme
predicates; neither nonemptiness nor separation nor characteristic nor
Noetherian/finite-presentation hypotheses occur. The sole universe `u` is the
existing scheme/algebraic-space universe, including all its scheme charts.
No statement correction or STATEMENT-DISPUTED issue was found.

## Second reading by NO

A second pass through the node and file matched the base, the three spaces,
the two arrows, and the four conjuncts as above. In particular, cancellation
has no hypothesis on g, etale is interpreted on compatible charts, the
unramified chart predicate includes local finite type, and base change uses
the existing canonical projection with reversed factor ordering. No mismatch
or mathematical change was found. This is the worker's own second pass;
the independent delivery review is performed by the maintainer, as the
assignment requires. No other agent was started.

## Returned delivery repair

Repaired L's H2 return on immutable head `9de25b71f51f`: replaced
`lem-trf-space-enlarged-etale-ringed-site-model` in stmt_deps with its
already landed definition owner `def-sfb-space-sheaf-fibre-product`.
Read that node's statement and Lean record and both definitions in
`EnlargedEtaleRingedSite`. The dependency paragraph now records the correct
owner. The Lean file, signature, mathematical statement and proof plan are
unchanged from the returned delivery. Current main still has no Lean record
for this item; this packet preserves its current fields and adds only the
Lean record and the two landed definition dependencies. The delivery wrapper
builds the repaired packet on current main.
