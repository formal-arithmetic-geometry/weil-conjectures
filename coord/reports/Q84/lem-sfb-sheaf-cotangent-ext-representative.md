## Worker report

States `CategoryTheory.SheafPolynomialCotangent.sheaf_cotangent_ext_representative` in
`Sheaf.CategoryTheory.SheafCotangentExtRepresentative`, with its only proof `sorry`.
The source is Stacks 08UJ, `defos.tex`, the complete statement and proof of
`lemma-NL-represent-ext-class-ringed-topoi`, read locally. The natural-language node
is unchanged. No new DAG node and no statement correction are needed.

Hypothesis and conclusion correspondence:

- Small site in the chosen universe: `{C : Type u} [SmallCategory C]`,
  `J : Precoverage C`, and `_hJ : J.IsSiteForCoverings`. Sheaves use
  `J.toGrothendieck`. Explicit universe `u` is the chosen bound; derived Hom uses
  the standard localization in the larger maximum universe, exactly as the
  recorded polynomial-comparison dependency does.
- Homomorphism of commutative ring sheaves: `A B : Sheaf J.toGrothendieck CommRingCat.{u}`
  and `f : A ⟶ B`.
- The prescribed polynomial cotangent constructions and comparisons:
  `D : Comparison f`. This parameter is the canonically normalized construction
  data, available by `sheaf_polynomial_cotangent_comparison J hJ A B f`.
  The theorem applies to every such system of models. It adds no condition on
  the rings, site or modules, and selects no uncharacterized object by choice.
- The arbitrary B-module sheaf: `G : ringedSiteModules.{u} (siteModuleRings B)`.
- Every Ext-one class: the binder `ξ` is a morphism from the localization of
  `(D.models (canonical f)).complex` to the localization of `G[0]`, shifted by one.
  Thus its source is exactly `NL_{B/A}=K_B`, and it is the node's derived Ext,
  rather than sectionwise Ext or a selected class of extensions.
- Existence of a sheaf E and E→B with sheaf-surjective A[E]→B:
  `∃ P : Presentation f`. The already recorded structure has fields `generators`,
  `values`, `surjective`; the last is local surjectivity of polynomial evaluation,
  not sectionwise surjectivity and not surjectivity of `E→B` itself.
- B-linearity and the specified source of the representative:
  `δ : (D.models P).complex.X (-1) ⟶ G`. This is the actual conormal module:
  `Model.quotient_surjective` and `Model.quotient_kernel` characterize J/J².
- The asserted equality is `ξ = (D.lambda P).inv ≫ twoTermSupportedBoundary ... δ`.
  Diagrammatic composition has λ inverse first, then ∂(δ), exactly the displayed
  equality in the node. The boundary is the positive projection q followed by
  the shifted degree-zero embedding of δ. Its definition is additive.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: actual site axioms.
- `def-weil-size-convention` has only a metatheoretic convention; explicit universes
  render it, with no extra Lean object or copied definition.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  precisely Mathlib module sheaves, their linear morphisms and abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`, `DerivedCategory.singleFunctors`:
  actual localization, embeddings and shift identifications.
- `Sheaf.CategoryTheory.SheafPolynomialCotangentComparison`,
  `CategoryTheory.SheafPolynomialCotangent.Presentation`, `.Model`, `.Comparison`,
  `.canonical`, `.localization`, `.sheaf_polynomial_cotangent_comparison`: all
  polynomial, kernel, conormal, differential and normalized λ data are reused.
- `Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary`,
  `DerivedCategory.twoTermBoundary` and its exactness/naturality/degree-zero clauses:
  directly imported without changing its module, record or declaration ownership.

Proof imports include the recorded modules
`Sheaf.CategoryTheory.YonedaDerivedExtComparison` and
`Sheaf.CategoryTheory.Sites.FreeModuleUniversalProperty`, with their naturality,
free-generator universal property and split-zero statements. Mathlib
`CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂` / `yoneda_exact₃` and
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'` are read and imported through
`Mathlib.CategoryTheory.Triangulated.Pretriangulated` and
`Mathlib.CategoryTheory.Sites.EpiMono`. The proof-only node
`lem-sfb-sheaf-polynomial-differentials-free` has no recorded Lean module at this
writing, so no import for it is available; it is not needed to type this statement.
All five proof steps, including its use, are given in the theorem docstring.

Edge cases checked mathematically: zero G gives ξ=0 and δ=0 with the canonical
presentation; the zero ring B gives zero module sheaves without any nontriviality
assumption; the empty site causes no excluded object or covering hypothesis;
empty E is allowed whenever its polynomial evaluation is locally surjective.
No projectivity of the differential sheaf, injectivity of G, characteristic,
points, terminal object, or sectionwise-surjectivity assumption is imposed.
The quotient onto degree -1 annihilates the incoming differential because the
only possible incoming degree is -2, a zero object by the supplied support.
Its component in degree -1 is the identity, fixing the positive boundary sign.

Searches for an existing statement:

- `msearch.py ... leanfinder "Every Ext one class of the naive cotangent complex of
  sheaves is represented by a conormal map after changing polynomial generators"`:
  8 hits, headed by `Algebra.Extension.H1Cotangent`; ring cotangent homology only,
  no sheaf Ext representative theorem.
- `msearch.py ... loogle '"cotangent", "Ext"'`: 12 hits, headed by
  `Algebra.Extension.Cotangent`; conormal modules only, no existence theorem.
- `msearch.py ... grep 'represent.*[Ee]xt.*class|cotangent.*[Ee]xt'`: 25 hits in
  module-presentation differentials and ideal/extension cotangent modules; no match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for cotangent/Ext and the exact
  node id: no existing declaration of this theorem. Related Zariski extension
  classification is restricted to topological sites and does not state the
  general-site change-of-generators representative result.
- Read `TwoTermDerivedHomBoundary`, `Single`, `SingleFunctors`, and
  `DerivedCategory.Basic`, and searched for a supported-complex boundary:
  the existing boundary is cone-only; `HomologicalComplex.mkHomToSingle` and
  `SingleFunctors.shiftIso` construct its required canonical extension directly.

Validation: the repaired single item module is compiled through `scompile.py`
against the published live library, followed by the delivery dry run.


## Repair of H13

The returned immutable head was 8104b388a872. Its helper definitions had replaced
Q72's primary dependency record, leaving the landed original module without its
owning record. This repair follows the first option of the maintainer's correction:

- `DerivedCategory.twoTermSupportedQuotient` and
  `DerivedCategory.twoTermSupportedBoundary` now live in the item module
  `Sheaf.CategoryTheory.SheafCotangentExtRepresentative`, with the item's blueprint
  tag on both docstrings and both names in the item's `lean.declarations`.
- The item directly imports `Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary`.
  Q72's live node, primary declaration `DerivedCategory.twoTermBoundary_exact`,
  module/file/statement/by fields, declaration list and reviewed_lean are untouched.
  The dependency node is absent from this repaired delivery, so its entire live
  record remains byte-identical.
- Dropped the separate `TwoTermSupportedDerivedHomBoundary.lean` module and its
  sandbox dependency-node override. The repaired delivery owns only the item
  module, the item's Lean record, and this report.

The helper definitions and the theorem signature and mathematics are unchanged.
The item node was reread from current main before applying only its Lean record;
normal delivery tooling rebases the repaired packet on current main.
There are no dependency modules or new nodes in the repaired packet.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
