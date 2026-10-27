## Worker report

The module `Sheaf.CategoryTheory.DerivedShriekCommaHomology` states
`CategoryTheory.derivedShriekCommaModel_exists`. It asserts existence of the complete
pointwise derived comma model. The actual derived isomorphism is the `model` field,
natural in coefficients. `DerivedShriekCommaModel.homologyIso` is constructed by
applying cohomology to this isomorphism and then the localization factorization;
it is not a replacement for the derived assertion. The sole postponed theorem is
`derivedShriekCommaModel_exists`, whose docstring contains all fourteen proof steps.
All helper definitions have actual data and none chooses a model from this theorem.

Clause-by-clause correspondence:

* Small categories and size: `{E D : Type u} [SmallCategory E] [SmallCategory D]`,
  with `R : Type u` and `[CommRing R]`. The imported category-bar instances form
  all derived categories with hom universe `u + 1`. Any sets of objects, arrows,
  chains, and coefficients in the chosen bound fit these binders, including empty
  categories. No independent, smaller index universe is imposed.
* Identity-cover topologies and all presheaves being sheaves: this is the literal
  functor-category presentation `Eᵒᵖ ⥤ ModuleCat R` and `Dᵒᵖ ⥤ ModuleCat R`.
  The bar dependency's `categoryBarConstantRing` uses bottom topology, and its
  `CategoryColimitPoint.modules` identifies the recorded `ringedSiteModules`
  category with these same module-presheaf categories. Thus no topology or sheaf
  condition has been dropped from a nontrivial site.
* The arbitrary functor is `f : E ⥤ D`. `commaShriekInverse f` is literal
  precomposition by `f.op`. `shriek` and `adjunction` give its ordinary left
  adjoint; the real construction `M.lanIso` canonically identifies it with
  Mathlib `f.op.lan` using `Adjunction.leftAdjointUniq` and `f.op.lanAdjunction`.
* The total unbounded `Lg_!` is `derived`, with universal comparison `comparison`
  and `universal`. `definedAt` retains essential constancy at every homotopy
  object, `commShift` and `triangulated` give the triangulated functor, and
  `derivedAdjunction` and `normalization` give precisely the canonical adjunction
  from the dependency, including its chain-level transpose normalization.
  These are conclusions of existence, not extra assumptions on `f` or `R`.
* The comma category is exactly Mathlib `StructuredArrow V f`: an object has
  `right : E` and `hom : V ⟶ f.obj right`; an arrow is a map of right objects
  satisfying the stated comma equation. It is not its opposite. The opposite
  enters only in its coefficient-presheaf category, as required.
* `commaShriekCoefficients f V` is precomposition with
  `(StructuredArrow.proj V f).op`. Hence its value and restriction are exactly
  `F(U)` and `F(h)` in the node. The existing bar model is
  `(B.models (StructuredArrow V f) R).bar`, never a second bar definition.
* `F` in degree zero is `CochainComplex.singleFunctor ... 0`. The field `model`
  is a natural isomorphism from its derived shriek followed by exact derived
  evaluation to the localization of that comma bar complex.
* Canonicity is fixed beyond an arbitrary natural isomorphism: `resolution`,
  `augmentation`, `quasiIso`, `acyclic`, `coordinates`, `resolutionRestriction`
  and `augmentationFormula` describe the augmented sum-of-representables
  resolution in proof steps 6--8. The coordinate index is `(c,b)` with
  `c : ComposableArrows E n` and `b : W ⟶ c.left`, and coefficient `F(c.right)`.
  `chainFormula` takes its identity-arrow generator, applies the ordinary
  adjunction unit, restricts along `c.left.hom`, and sends it to the same comma
  chain's bar generator. `chainIso` therefore fixes the chain comparison in
  every degree. `model_eq` is exactly evaluation of
  `inv (derived.map (Q.map augmentation)) ≫ comparison`, followed by the exact
  evaluation factorization and localization of this chain isomorphism.
  These fields spell out the canonical identification asserted by the node;
  they do not replace it by unspecified maps or projectivity assumptions.
* Every `n ≥ 0` is `n : ℕ`. `M.homologyIso F V n` identifies the degree `-n`
  derived cohomology object with the actual bar complex's degree `-n` homology.
  `positive` states vanishing as `IsZero` for every integer `r` with `0 < r`.
* For any presheaf `K`, `counitAugmentation K V` is a chain map from the bar
  model for `F = (commaShriekInverse f).obj K` to `K(V)[0]`.
  `counitFormula` sends the degree-zero generator at `c.right` to
  `K.map c.right.hom.op x`, exactly `K(a)(x)`. Its other components are zero
  because the target is the degree-zero single complex.
* `counit_eq` identifies this localized augmentation with the evaluated derived
  counit, inserting only Mathlib's single-complex and exact-factorization
  isomorphisms. It does not merely assert agreement on degree-zero cohomology.
* Restriction along `b : W ⟶ V` is `StructuredArrow.map b`, i.e. precomposition
  of each comma arrow by `b`, with unchanged coefficient. `restrictionFormula`
  fixes the chain map on all generators. `commaShriekDerivedRestriction` is an
  actual `Localization.liftNatTrans` construction from ordinary presheaf
  restriction. `restrictionNaturality` states its square with `model`.
* Coefficient naturality is built into `model : ... ≅ ...` as a natural
  isomorphism of functors in `F`. `restrictionCoefficient` makes its compatibility
  with restrictions explicit. `counitRestriction` and `counitCoefficient` state
  both naturalities for the augmentation as well. Generator formulas force the
  identity/composition laws for these restriction maps.

Dependencies read and used:

* `def-weil-size-convention`: metatheoretic `lean.convention` record; represented
  by the explicit common universe and the bar dependency's standard derived
  localization instances. It has no object declaration to import.
* `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`. Its role here is the
  identity-cover site specialization, already used by the bar module.
* `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  and its recorded Mathlib match `SheafOfModules`; the bar point's module
  equivalences are the same category presentation.
* `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; also the recorded cohomology
  functors/factorizations and exact-functor descent.
* `lem-trf-derived-colimit-bar`:
  `Sheaf.CategoryTheory.DerivedColimitBar`,
  `CategoryTheory.CategoryColimitBarSystem`, its `models`, and
  `CategoryColimitBarModel.bar`, `generator`, `coordinates`, `positive`,
  `model`, and canonical augmented-resolution interface. The arbitrary `B`
  binder is a choice of the bar system asserted to exist by
  `categoryColimitBarSystem_exists`, not an extra mathematical hypothesis.
* `lem-trf-continuous-cocontinuous-derived-shriek`:
  `Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek`,
  `ContinuousCocontinuousDerivedShriekData` and
  `continuousCocontinuous_exists_derivedShriek`. This supplies the normalized
  adjunction after transport to module presheaves in proof step 1.
* Proof-only dependency `lem-trf-bounded-above-acyclic-derived-computation`:
  `Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation`,
  `exists_boundedAbove_projective_resolution` and
  `boundedAbove_acyclic_leftDerived_computation`. Imported privately, used in
  the proof plan for representable-sum acyclicity and canonical comparison.

The full recorded source signatures and docstrings were read. The Stacks source
was read locally at `sites-cohomology.tex`, examples `example-left-derived-colimits`
and `example-morphism-categories`, and `lemma-compute-left-derived-g-shriek`,
including the comma-arrow direction in its proof.

Edge cases checked mathematically before finalizing:

* Empty `E` or empty `(V ↓ f)`: all chain sums are empty, so the bar and derived
  evaluation are zero. There is no nonempty-category hypothesis.
* Empty `D`: all pointwise clauses are vacuous, while the adjunction is the
  unique one into the empty-index presheaf category. A functor into empty `D`
  already forces empty `E`.
* `f = identity`: `(V ↓ identity)` has initial object `(V,id)`; the opposite
  has terminal object. The bar contracts to `F(V)[0]`, consistently with
  identity shriek, restriction and the identity counit.
* One-object identity category: the model is a resolution of the coefficient
  module with identity augmentation in degree zero, without projectivity.
* `n = 0`: the isomorphism gives the ordinary comma colimit (the cokernel of
  the degree `-1` differential). Positive cohomology is not confused with
  higher negative derived colimits.
* `R` the zero ring and `F = 0`: all coefficients and complexes vanish; every
  formula is still meaningful. No characteristic assumption is used.
* Arbitrary nonprojective coefficients, such as `ℤ/2` over `ℤ`: step 5 uses
  projective module resolutions to establish representable-sum acyclicity,
  rather than asserting that these coefficient representables are projective.
* Restriction direction: for `b : W → V` and `a : V → fU` the new arrow is
  `b ≫ a`, exactly the convention of `StructuredArrow.map`.

Searches for an existing statement:

* `msearch.py ... leanfinder "left derived left Kan extension of module
  presheaves pointwise comma category bar complex counit"`: eight hits,
  including `Functor.totalLeftDerivedCounit`, generic derived Kan statements,
  and adjunction counit constructions. None states the comma-bar computation.
* `msearch.py ... loogle "Functor.lan, CostructuredArrow, StructuredArrow,
  DerivedCategory"`: zero hits, unknown unqualified `Functor.lan`.
  Direct Mathlib search then found and read `Functor.lan`,
  `Functor.lanAdjunction`, `Functor.leftKanExtensionObjIsoColimit`, and
  `StructuredArrow.proj`/`map`. These supply the ordinary constructions,
  not the requested derived theorem.
* `msearch.py ... leansearch "derived left Kan extension presheaf modules
  computed by comma category bar resolution"`: eight hits, ordinary Kan
  extension definitions and generic derived universal properties; no match.
* `msearch.py ... grep 'leftKanExtension|StructuredArrow|categoryColimitBar'
  CategoryTheory`: 25 hits, ordinary structured-arrow/adjunction constructions.
* `rg` over `lean/WeilConjectures` and `lean/Sheaf` for comma/bar and derived/Kan
  patterns, and the exact node id: generic Kan transport and the existing bar
  dependency, no theorem for this node. The required upstream exact-id search
  found no declaration. Proposed declaration names were also searched in these
  trees and `dag/lean_names_upstream.json`, with no collisions.

No statement correction, new independent notion, dependency-module repair,
or mathematical dispute was needed. The auxiliary constructions and record
only express this node's own canonical computation; existing Mathlib comma,
Kan, derived, and dependency bar notions are reused.

## Second reading by NX

A separate pass over the node and module checked each binder and conclusion
against the correspondence above. This is a worker self-check; the maintainer
performs the independent review required by the dispatch brief. No other agent
was started. The first compiler pass found that an unannotated composite
functor did not expose `ComposableArrows.right`; the coefficient expression now
uses `c.right.right` directly. The counit square initially omitted the standard
single-complex/precomposition isomorphism on its source; it now explicitly
inserts `singleMapHomologicalComplex.inv` before the exact derived-factorization
inverse. The semantic pass checked the orientation of both factors, the
negative-degree chain order, the identity-arrow generator under the ordinary
adjunction unit, and the precise comparison in `model_eq`. The source statement
and its dependency lists are unchanged.

Validation: the final module compiled cleanly with `scompile.py` against the live
published server build in both sandbox and library-module passes (13.0 s and
13.8 s); neither pass reported an error or warning. The only node delta is
`lean`, its recorded signature matches the file verbatim, and all source lines
are at most 100 characters.
