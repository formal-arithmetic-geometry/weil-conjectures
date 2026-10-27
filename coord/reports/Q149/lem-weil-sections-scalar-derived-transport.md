## Worker report

The module `Sheaf.Algebra.Homology.SectionsScalarDerivedTransport` states
`CategoryTheory.SectionsScalarTransport.derived_transport` and
`CategoryTheory.SectionsScalarTransport.roof_naturality`. Both proofs are `sorry`.
The supporting records have real fields and the termwise functors are real constructions.
No mathematical statement is corrected and no dependency interface is replaced.
The node gains only its Lean record and the two already landed definition dependencies
`def-sfb-derived-change-of-rings-cochain-model` and `def-trf-scalar-tensor-section`.

Hypotheses and clauses, matched to the node:

- The general site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`.
  `[EssentiallySmall.{r} C]`, sheaf composition, abelian sheafification and the
  locally-bijective equivalence instances implement smallness relative to the module
  universe. Site object and Hom universes remain independent of `r`.
- The four coefficient sheaves and ordinary rings, all their composites and diagonal
  identities, are the functors `R : Fin 4 ⥤ Sheaf J CommRingCat.{r}` and
  `A : Fin 4 ⥤ CommRingCat.{r}`. Their functor laws impose precisely composition
  and identity of the coefficient arrows, without identifying tensor-by-the-source-ring
  with the identity functor.
- Complexes are `CochainComplex ... ℤ`; `DerivedCategory` and its `Q` use explicit
  `HasDerivedCategory` instance binders with independent sheaf/module localization
  universes `dS`, `dA`. No boundedness or completeness predicate occurs.
- `M i j h` is the specified `DerivedChangeOfRingsCochainModel` for the actual
  sheaf coefficient arrow. Its ordinary `E` is fixed on objects/maps by the recorded
  sheafified scalar construction; its derived `T` and universal `ε` are retained.
  The local helper `T` applies `M.E` termwise, and `t` applies Mathlib's actual
  `ModuleCat.extendScalars` for the ordinary coefficient arrow termwise.
- `G` is the family of additive functors on module sheaves, with `[∀ i, (G i).Additive]`;
  `g` applies each termwise. No K-flat preservation by `G` is imposed.
- `ChainHypotheses.sheaf_quasiIso`, `.module_quasiIso`, `.sections_quasiIso` quantify
  over every quasi-isomorphism of entire unbounded complexes for every allowed pair.
- `u₀`, `a₀`, `m₀`, `μ₀`, `θ₀` are natural chain isomorphisms of the exact required
  sources and targets. `ChainHypotheses.sheaf_associator` and `.module_associator`
  stipulate the balanced multiplication formulas degreewise. `.sheaf_unit` and
  `.module_unit` stipulate the action formulas. Inverse formulas follow from the
  isomorphism inverse laws and these generator formulas; there is no assumption
  that all sheaf tensor sections are globally pure tensors.
- `Coherent.triple` is the three-index comparison equation, `.unit` the action-unit
  equation, `.sheaf_four` and `.module_four` the two four-stage associator equations,
  and `.iterated` the displayed three-comparison equation. All equations are
  componentwise equalities of natural chain maps, with diagrammatic Lean composition.
  `ChainHypotheses.coherent` imposes exactly these equations.
- `DerivedTransport.barT`, `.td`, `.gd` and `.beta`, `.delta`, `.gamma` are the
  localized functors with specified representative factorizations. Thus arbitrary
  choices of representatives are compared by actual natural isomorphisms.
- `.c` is the derived-to-localized scalar comparison. `.counit` is exactly
  `c_Q(P) ≫ beta_P = ε_P`; `.c_unique` quantifies over every competing natural
  transformation, not only isomorphisms. `.sigma` and `.sigma_counit` record the
  invertible representative comparison whose hom is precisely the specified counit.
- `.alpha`, `.ad`, `.md`, `.mud`, `.theta` are the derived scalar/module associators,
  action units, and sections comparisons. `.alpha_rep` and `.alpha_inv_rep` give
  their two counit-normalized ordinary associator formulas on every complex.
  `.a_rep`, `.m_rep`, `.mu_rep` give the corresponding localized module/action maps.
- `.theta_rep` is the localized chain theta conjugated by the explicit representative
  comparisons. `.theta_unique` quantifies over all competing natural transformations
  with those components. Invertibility is supplied by the field `.theta` itself.
- `.coherent` applies the very same five-equation record to the derived functors.
  Consequently all triple, action, both four-stage, and iterated equations are stated.
- `.resolution_computation` gives the unique computation isomorphism for each
  flat-term K-flat resolution, with its inverse expressed using that resolution
  and the counit. `.resolution_associator` gives both composite/direct computation
  isomorphisms and the forward and inverse ordinary associator equations on that
  resolution. Their inverse formulas fix these isomorphisms, rather than merely
  asserting that some model is isomorphic.
- The second conjunct of `derived_transport` states that every scalar extension of
  every flat-term K-flat complex is again flat-term K-flat. Applying it twice gives
  every intermediate double extension appearing in the composite computation.
- The formulas for all complexes, their natural-isomorphism types, and the fixed
  resolution computations express resolution independence: both choices compute the
  same already defined derived component. Units, inverses and pastings inherit this
  naturality. `roof_naturality` states the node's final roof equality for every cell
  between the corresponding derived composite functors and arbitrary representative
  comparisons. It assumes only invertibility of `Q(v)`, which holds for every
  quasi-isomorphism denominator under the recorded derived localization.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules` and its abelian structure.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its localization instance.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` (exactness of the existing tensor-right functor).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the independent-universe sheaf tensor structures, with the existing tensor.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.derivedChangeRingIndependentCoefficients` (definition owner
  `def-sfb-derived-change-of-rings-cochain-model`).
- `Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence`:
  `CategoryTheory.PrincipalQuotientCompletion.scalarTensorSection` (definition owner
  `def-trf-scalar-tensor-section`), the actual sheafified pure tensor transported
  through `M.obj_eq`; no finite-free/completion hypothesis is used.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: `ModuleCat.extendScalars`,
  with its scalar-left tensor presentation; commutativity identifies it with the
  source's scalar-right notation.
- `Mathlib.CategoryTheory.Localization.Predicate`: `Localization.lift`, `fac`,
  `liftNatTrans`, `liftNatIso`, `natTrans_ext` for the proof plan.
- Plain proof imports retain the recorded modules for
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings` (and its public generic sheaf
  interface), `Functor.localizationLeftDerivedComparison`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`,
  `SheafOfModules.changeOfRings_isKFlat_of_flat_terms`, and
  `RingedKFlatWord.word_comparison_descent`. The full signatures and docstrings
  were read; the node's nine-step natural-language proof appears in the main theorem.

Edge cases checked before completing the statement: diagonal and repeated indices
use actual action units, without strictifying scalar extension; zero rings, zero
complexes, and the empty site are allowed; every degree of an unbounded complex is
present; there is no characteristic assumption, no flatness hypothesis on a structural
ring map beyond preservation of all quasi-isomorphisms explicitly stipulated by the
item, and no assumption that sections preserve K-flat complexes. Site universes need
not coincide, and the localization Hom universes are separate.

Searches for an existing statement:

- `msearch.py leanfinder`, query "Counit normalized coherent exact scalar extension
  and sections comparison descend to unbounded derived categories with K flat
  computations": 8 results, including `Adjunction.derived_counit`,
  `Functor.mapDerivedCategoryFactorsh`, `Functor.totalLeftDerivedCounit`;
  these are individual tools, not the coherent four-stage statement.
- `msearch.py loogle`, query `CategoryTheory.Localization.liftNatIso`: 3 results,
  the generic localization isomorphism and its hom/inv formulas; no exact statement.
- `msearch.py grep`, query `liftNatIso|scalar.*[Aa]ssoc`, subdirectory CategoryTheory:
  25 hits, principally localization constructions; no simultaneous normalized
  scalar/sections coherence and K-flat model assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for scalar-derived transport,
  `sectionsScalar`, and the declaration names: no matching statement. Existing
  word-comparison descent is a generic proof dependency and does not state this
  sections diagram with its five stipulated chain equations.
- `grep -rn lem-weil-sections-scalar-derived-transport lean/WeilConjectures`:
  no occurrence. The existing declaration index was searched for the new names.
  No new independent notion or definition node is required.

Sources opened: Stacks sites-cohomology.tex, the K-flat-resolution,
pullback-K-flat, derived-base-change and derived-pullback-composition lemmas
(Tags 06YS, 0G7E, 06YY, 0D6D); categories.tex, localization lemma 04VG;
current blueprint `def-weil-finite-coefficient-point.md`, final stagewise/common-stage
colimit paragraph. No statement dispute or source correction was found.

Validation: all compilation uses the prescribed `scompile.py`; the final clean
compile, dry run and delivery results are recorded by the delivery tool.

## Second reading by Q149

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
