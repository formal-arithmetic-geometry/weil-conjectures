## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest` states
`AlgebraicGeometry.AlgebraicSpace.local_properties_chart_test` and
`AlgebraicGeometry.AlgebraicSpace.local_properties_chart_test_iff_scheme`.
Both proofs are `sorry`; there are no new definitions or other postponed obligations.
The node statement, statement dependencies, proof and proof dependencies are unchanged.
No statement fault or dispute was found.

Sources read: Stacks `spaces-morphisms.tex`, lemma-local-source-target (03MJ),
lemma-flat-local (03MM), lemma-finite-presentation-local (0410), and
lemma-finite-type-local (040Y), including conditions (7),(8) and the scheme comparison.
This is a created supporting node, not a blueprint unit's own statement.

Hypothesis and clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`. The explicit universe `u` uses
  the same size convention as the recorded algebraic-space interface: schemes of
  universe u, presheaves on `(Over S)ᵒᵖ` with values in `Type u`. No new universe
  equality, smallness hypothesis, or restriction on the base is introduced.
- Algebraic spaces and their morphism are `{X Y : AlgebraicSpace S} (f : X ⟶ Y)`.
  These are the recorded full subcategory of fppf sheaves and its natural transformations.
- The choice of precisely one of the three properties is the scheme morphism property
  `P` with `hP : P = @Flat ∨ P = @LocallyOfFinitePresentation ∨
  P = @LocallyOfFiniteType`. No instance of either of the other properties is assumed.
  There is no additional locality or isomorphism-invariance assumption on P.
- The chart extension is the existing `MapIsLocally P f`, not a private definition.
  It quantifies over all compatible representable étale scheme chart diagrams.
- The target scheme over S is `V : Over S`; its map to Y is
  `b : yoneda.obj V ⟶ Y.obj.obj`. `hb : IsEtale b` and
  `hbs : IsSurjective b` are exactly its two chart hypotheses.
- The fibre product is the presheaf pullback `Limits.pullback f.hom.hom b`.
  Fibre products of algebraic spaces are the corresponding sheaf fibre products,
  represented on presheaves by matching pairs; the existing scheme-test predicates
  are defined on these presheaves, so no additional algebraic-space witness is needed.
- The source scheme is `U : Over S`, and the source chart is
  `q : yoneda.obj U ⟶ Limits.pullback f.hom.hom b`, with exactly
  `hq : IsEtale q` and `hqs : IsSurjective q`.
- The indicated scheme map U → V is the canonical
  `(yoneda.preimage (q ≫ Limits.pullback.snd f.hom.hom b)).left`.
  Yoneda's full faithfulness turns precisely this natural transformation into its
  unique scheme map over S. No arbitrary map, extra commutation assumption, or
  chosen lift replaces it.
- The conclusion `MapIsLocally P f ↔ P (...)` is the requested equivalence.
  All charts are arbitrary theorem binders, hence it applies to every chart pair.
- For a scheme target the identity natural transformation is allowed as b: the
  representable-étale scheme tests include isomorphisms and identity scheme maps.
  The presheaf pullback with that map is canonically X; no nonidentity restriction
  occurs in the signature.
- The second theorem states the full scheme comparison. For `X Y : Over S` and
  `f : X ⟶ Y`, its left side is
  `∀ D : EtalePresentation (yoneda.map f), P D.h.left`. Expanding the existing
  `EtalePresentation` gives precisely the universal chart test `MapIsLocally` on
  the representable schemes: all U,V,a,b,h with representable étale vertical maps
  and a commuting square. Its right side is `P f.left`, the indicated scheme
  property. This avoids introducing another scheme-as-algebraic-space construction.
- There is no quasi-compactness, separation, finite-type, nonemptiness or other
  hidden hypothesis. Every variable and universe is explicitly bound, with
  `set_option autoImplicit false`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  `Flat.iff_flat_stalkMap` identifying the node's stalkwise definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (all affine pairs).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (all affine pairs).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocally` (publicly available through the recorded criterion).
- `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`:
  `IsEtaleLocalOnSourceAndTarget`, `AlgebraicSpace.EtalePresentation`,
  `HasEtalePresentationProperty`, `etalePresentation_property_criterion`,
  `etalePresentation_property_iff_scheme`. Their complete source signatures and
  docstrings were read; both the existence/universal criterion and scheme comparison
  are used in the proof plan.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme` (the recorded fibre-product interface).
- Proof-only imports: `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`,
  declaration `AlgebraicGeometry.scheme_etale_source_target_properties`, and
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`, declaration
  `AlgebraicGeometry.AlgebraicSpace.representable_etale_scheme_tests`. The former
  includes each of the three P choices in its five-way list; the latter includes
  surjective étale base change, composition, isomorphisms and scheme-map tests.
- `def-weil-size-convention` is metatheoretic and has no declaration to import.

Edge cases checked before writing: empty base and source are not excluded; an empty
source chart covers precisely an empty pullback, and target surjectivity then forces
X empty, so the vacuous local-property tests agree. Identity target charts and identity
scheme maps are allowed. An infinite disjoint union of affine charts is allowed:
no quasi-compact atlas is assumed. Nonseparated charts are allowed. Flatness can hold
without finite presentation (e.g. an infinitely generated field extension); the Flat
case does not assume either finiteness property. Local finite type can hold without
flatness (e.g. the closed point of the dual numbers); the finite-type case does not
assume flatness. None of these checks requires proving a new theorem in this stage.

Searches made with the prescribed `msearch.py Q132
lem-sfb-space-local-properties-chart-test` wrapper:

- `leanfinder`: "Flatness local finite presentation and local finite type for algebraic
  space morphisms are detected on etale source and target charts". Eight hits: scheme
  Flat and LocallyOfFinitePresentation interfaces, smoothness/étaleness implications,
  and the flat stalk criterion. No algebraic-space chart detection statement.
- `leansearch`: "Algebraic space flat locally finite presentation locally finite type
  tested on etale charts". Eight hits: scheme LocallyOfFinitePresentation and
  LocallyOfFiniteType, affine characterizations, and algebra étaleness. No exact match.
- `loogle`: `AlgebraicGeometry.AlgebraicSpace.MapIsLocally,
  AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation`. Zero hits;
  the service does not know the project's MapIsLocally name.
- `grep`: `AlgebraicSpace|etale.*chart|chart.*property`, subdirectory
  `AlgebraicGeometry`. Zero Mathlib hits.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  `lem-sfb-space-local-properties-chart-test|MapIsLocally|local_properties_chart|chart_test`.
  Found the existing MapIsLocally definition, general presentation criterion, and
  downstream docstring citations of this item, but no declaration of this item.
  All existing interfaces were reused. No new node or dependency repair is needed.

Validation: the delivery module is compiled separately using the prescribed server
wrapper `scompile.py`; the dry run and final delivery also compile it and run server
preflight. Only expected declaration-uses-sorry warnings are acceptable.

## Second reading by Q132

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
