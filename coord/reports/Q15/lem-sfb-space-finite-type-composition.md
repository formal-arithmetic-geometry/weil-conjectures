## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFiniteTypeComposition` states
`AlgebraicGeometry.AlgebraicSpace.mapIsFiniteType_comp`, with its entire proof postponed
by `sorry`. No definitions, dependency repairs, or statement corrections are needed.
Only the item's `lean` field changes; the reviewed stage-1 split is preserved.
The inherited BLOCKED ending concerned stage-1 delivery of the already reviewed split.
The current node has no Lean record and is in the stage-2 queue; brief-stage2 §0 expressly
allows this stage handoff. There is no repair note for this item.

Clause-by-clause correspondence:

- The base scheme S is `{S : Scheme.{u}}`.
- The three algebraic spaces over S are `{X Y Z : AlgebraicSpace S}`. This is the recorded
  full subcategory of big-fppf sheaves having representable diagonal and a surjective etale
  scheme atlas. Morphisms are the full-subcategory natural transformations.
- The two morphisms are `(f : X ⟶ Y) (g : Y ⟶ Z)`.
- Finite type of f and g is exactly `(hf : MapIsFiniteType f)` and
  `(hg : MapIsFiniteType g)`.
- `MapIsFiniteType` unfolds to `MapIsQuasiCompact f.hom.hom ∧
  MapIsLocally (@LocallyOfFiniteType) f`: affine-test quasi-compactness and the compatible
  representable-etale-chart test, precisely as the node specifies.
- The conclusion is `MapIsFiniteType (f ≫ g)`; category composition is g after f.
- `universe u` is explicit, and all schemes, field tests and spaces use the recorded common
  size convention. There is no independent smaller test universe.
- There are no separatedness, representability of f or g, finite-presentation, Noetherian,
  nonemptiness, or other extra hypotheses.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, obtained
  through the public statement import.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`;
  obtained through the public statement import.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties` (public import):
  `AlgebraicSpace.MapIsFiniteType`, `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.MapIsQuasiCompact`, reached
  publicly through the morphism-properties module. Its topology and actual presheaf
  pullbacks are reused, without defining an alternative notion.
- `def-weil-size-convention` is a metatheoretic convention; its record has no module or
  declaration. Explicit `universe u` follows its recorded guidance.

The available proof-dependency modules are plain imports:
`SchemeEtaleSourceTargetProperties` (`scheme_etale_source_target_properties`),
`SpaceEtalePresentationPropertyCriterion` (`etalePresentation_property_criterion`),
`ChartwiseEtalePermanence` (`chartwise_etale_permanence`), and
`AlgebraicSpaceFibreProductsEtaleCovers` (`fibreProduct_isAlgebraicSpace`,
`etaleCover_pullback`, `etale_fibreProduct_isScheme`), all under
`Sheaf.AlgebraicGeometry`. The Mathlib modules listed by the recorded
`lem-weil-pbc-proper-fp-permanence` match are imported as proof dependencies, including
`locallyOfFiniteType_comp` in `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
`lem-a1-space-point-open-calculus` and `lem-sfb-qc-space-affine-etale-atlas` currently have
no recorded Lean declarations; their proof uses remain in the docstring for stage 3.
They are not needed to type the present statement and are not restated here.

Source checked: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-composition-finite-type` (Tag 03XG, finite-type clause),
`remark-composition-P` (0AML), and `lemma-composition-quasi-compact` (03HG).
The node's four proof steps are rendered in the theorem docstring.

Edge cases checked before writing: empty source or target spaces and empty base are not
excluded; compactness of an empty affine-test pullback and its empty covers remain valid.
Identity factors are allowed. Arbitrary non-Noetherian and non-quasi-separated spaces
remain allowed; no scheme atlas map is assumed quasi-compact. No characteristic or degree
parameter occurs. The theorem asks only for finite type of the two given maps.

Searches (all msearch calls logged in `searches.jsonl`, 2026-10-23):

- LeanFinder: "The composite of finite type morphisms of algebraic spaces is finite type".
  Eight scheme-level hits, including `locallyOfFiniteType_comp` and finite-morphism
  composition; none concerns algebraic spaces.
- Loogle: `AlgebraicGeometry.LocallyOfFiniteType, AlgebraicGeometry.QuasiCompact`.
  Eight scheme-level hits concerning quasi-finite maps and properness; no space theorem.
- Mathlib grep: `MapIsFiniteType|AlgebraicSpace|locallyOfFiniteType_comp` in
  `AlgebraicGeometry`. Only `locallyOfFiniteType_comp`, FiniteType.lean:68, matched.
- LeanSearch: "Composition of finite type morphisms of algebraic spaces is finite type".
  Eight scheme-level finite/locally-finite-type composition hits; no exact match.
- Project `rg`: `MapIsFiniteType|mapIsFiniteType_comp|mapIsFiniteType` in `lean/Sheaf`,
  `lean/WeilConjectures` and `dag/lean_names_upstream.json`. Only the existing definition
  and its occurrence in `MapIsProper` matched, both in AlgebraicSpaceMorphismProperties.
- Upstream `rg`: `AlgebraicSpace|mapIsFiniteType_comp`, and the exact item id, in
  `lean/WeilConjectures`; no matching declaration.

No STATEMENT-DISPUTED issue found. The example CompactObject module is withdrawn in this
checkout, so the current module conventions in brief-stage2 and the dependency modules
were followed instead.

## Second reading by Q15

Author's separate rereading; no independent worker was started, as the dispatch forbids
it. I reopened the node and module: S, X/Y/Z over S, both arrows, both finite-type
hypotheses, and finite type of g after f match exactly. I reopened the definitions:
`MapIsLocally` quantifies over compatible charts with both maps `IsEtale`, and
`MapIsFiniteType` conjoins it with affine-test quasi-compactness. There is no global
finite-presentation or representability requirement hidden in the theorem binders.
The universe is bound and no nonemptiness restriction excludes empty spaces. The four
natural-language proof steps keep the compatible-atlas argument, scheme lft composition,
affine-atlas compactness test, and finite-subcover argument. No mismatch or signature
change was found. The maintainer performs the independent delivery review.
