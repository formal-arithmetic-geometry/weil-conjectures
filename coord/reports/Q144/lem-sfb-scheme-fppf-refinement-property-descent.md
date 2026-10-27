## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeFppfRefinementPropertyDescent` states
`AlgebraicGeometry.properties_of_fppf_refinement_of_comp`. It contains one theorem,
with proof `sorry`, and no definitions. The item's only changed field is `lean`.
No repair note exists for this item. No statement fault or dispute was found.

Source read: `literature/stacks-project/descent.tex`, Tag 06NB,
`lemma-curiosity`, lines 4540–4620 (statement and all three cases of its proof).
The source assumes precisely a composite with the chosen property and an fppf
covering refining its first arrow, with no property imposed on that arrow.
The declaration docstring carries all six steps of the accepted DAG proof and
names their dependencies, including the empty-product case.

Hypothesis and conclusion correspondence:

- Schemes and the two given arrows are `{X Y Z : Scheme.{u}}`, `(a : X ⟶ Y)`,
  and `(b : Y ⟶ Z)`. Lean's `a ≫ b` is the source's `b ∘ a`.
- The size convention is rendered by explicitly declared universes `u v`.
  Every scheme has universe `u`, while the index set `{I : Type v}` has an
  independent, unrestricted universe. No smallness, nonemptiness, or finiteness
  hypothesis is imposed on the family.
- The family is `(T : I → Scheme.{u}) (q : ∀ i : I, T i ⟶ Y)`.
  `hcover : Presieve.ofArrows T q ∈ Scheme.fppfPrecoverage Y` says it is jointly
  surjective with each `q i` flat and locally of finite presentation. This is
  the dependency's recorded precoverage, not a newly defined covering notion.
  Its meaning follows directly from `Scheme.fppfPrecoverage` and
  `Scheme.ofArrows_mem_precoverage_iff` in Mathlib's
  `AlgebraicGeometry/Sites/Fpqc.lean:41` and `Sites/MorphismProperty.lean:82`.
- `(s : ∀ i : I, T i ⟶ X)` and
  `hlift : ∀ i : I, s i ≫ a = q i` give exactly the stated factorizations
  `a ∘ s_i = q_i`, in the correct composition order.
- Flatness is the first implication `Flat (a ≫ b) → Flat b`.
- Local finite type is the second implication
  `LocallyOfFiniteType (a ≫ b) → LocallyOfFiniteType b`.
- Local finite presentation is the third implication
  `LocallyOfFinitePresentation (a ≫ b) → LocallyOfFinitePresentation b`.
  Their conjunction states the alternatives separately: it does not assume
  that the composite has all three properties simultaneously.
- No flatness, finiteness, separation, or quasi-compactness hypothesis occurs
  on `a`. There are no other hypotheses or extra conclusions.

Statement dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (definitions and docstrings at lines 35–76).
- `def-weil-size-convention`: its `lean.convention` record explicitly specifies
  universe binders rather than a mathematical object or declaration.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat:36–46`; its
  `Flat.iff_flat_stalkMap:106` identifies the affine and stalkwise formulations.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType:38–47`. Only its local notion
  is requested here; the node's quasi-compact and finite-type notions are not
  imposed.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:42–49`.
- `def-pc-fppf-site`: `AlgebraicGeometry.Scheme.fppfPrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc:38–44`, read together with the
  joint-surjectivity characterization above. The topology itself is not
  needed because the node explicitly supplies a covering family.

The statement modules are public imports. Stated proof-dependency modules are
plain imports, including `Sheaf.RingTheory.FiniteTypeFppfSourceDescent`
(`RingHom.finiteType_of_comp_faithfullyFlat_finitePresentation`) and
`WeilConjectures.Mathlib.RingTheory.Finiteness.Descent`
(`Algebra.FinitePresentation.of_finitePresentation_of_faithfullyFlat`). The
latter is the source declaration of the partially populated upstream match on
`lem-trf-finite-presentation-fppf-source-algebra` (full signature read at
lines 231–235). The affine flatness/type/presentation criteria come from the
public statement imports; finite-product flatness, faithful-flat injectivity,
flat ring maps, and finite-presentation algebra operations have their recorded
Mathlib proof imports. The unstated proof dependencies
`lem-sfb-fppf-lifts-finite-affine-charts` and
`lem-trf-finite-affine-composite-presentation` have no module to import yet;
they remain named in the proof plan. They are not statement prerequisites.

Edge cases checked before writing:

- An empty index type is allowed. The empty family covers precisely an empty
  target `Y`; all three local properties of `b` are then vacuous.
- Empty schemes are allowed throughout; nothing requires a point or an affine
  chart to exist. Empty finite products in the proof are zero algebras.
- A singleton identity covering with `a = 𝟙 Y` reduces each implication to the
  same property under identity composition.
- The refinement assumption is substantive: for `X` empty and `Y` nonempty,
  no family covering `Y` can admit these lifts.
- Index sets of larger universes and arbitrary characteristics are retained;
  no `[Finite I]`, `[Nonempty I]`, or characteristic restriction is present.

Searches actually run with `batch2/msearch.py` (group Q144 and this item):

- LeanFinder: "Schemes X to Y to Z where X to Y admits fppf local lifts:
  flatness local finite type and local finite presentation of X to Z descend
  to Y to Z". Eight hits: property definitions, composition, and base-change
  `DescendsAlong` results; none states this refinement theorem.
- Loogle: "AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFiniteType,
  AlgebraicGeometry.LocallyOfFinitePresentation". Successful search, zero hits.
- LeanSearch: "Scheme morphism properties descend from a composite if the
  first morphism admits fppf local sections". Eight hits, including
  `locallyOfFiniteType_of_comp` (which concludes the property of the first
  arrow, not `b`) and general base-change descent results; no exact match.
- Mathlib grep: `curiosity|fppf.*(refinement|descen)|of_comp`, subdirectory
  `AlgebraicGeometry`. Twenty-five returned hits concern other composition
  results, pullbacks, and integral morphisms; no exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `curiosity`, fppf refinement, lift, and section patterns found affine-cover
  refinements and other sheaf constructions, not this statement. The explicit
  `grep -rn` by item id in `lean/WeilConjectures` found no occurrence.
- The proposed full declaration name was searched in Mathlib's algebraic
  geometry sources, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`; no existing declaration was found.

Validation: `scompile.py Q144 lem-sfb-scheme-fppf-refinement-property-descent`
compiled the module in both sandbox and library module modes with no errors
or warnings (reported times 1.5 s and 1.4 s). All variables and universes are
explicit, with `set_option autoImplicit false`. No local compiler or global
build was run.

## Second reading by Q144

A separate second pass by the same worker re-opened the node, the source, and
the completed Lean declaration. The dispatcher brief prohibits starting other
agents; no independent second worker is claimed here. The maintainer supplies
the independent delivery review.

I checked the direction of both compositions: the composite is `a ≫ b`, and
its local lifts satisfy `s i ≫ a = q i`. The precoverage membership expresses
a genuinely fppf family, including joint surjectivity, rather than merely a
covering sieve in the generated topology. Each of the three composite-property
hypotheses belongs to its own implication. The codomain of each conclusion
is `b`, and local finite type/presentation have not been replaced by their
global versions. The binders allow arbitrary sets and empty schemes, and
there is no instance assumption on `a`. The universe convention needs no
spurious mathematical binder. No mismatch was found; no changes to the
mathematical statement or dependency nodes were needed. The JSON signature
was extracted verbatim from the final source, and all Lean lines are at most
100 characters.
