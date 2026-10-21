## Worker report

The module `Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection` states
`SheafOfModules.derivedScalarLocalizationReflection`, with one `sorry` and no new
definitions. The node's mathematical statement is unchanged. Its `lean` field is the
only changed node field. No dependency repair or new node is needed. There is no
statement dispute and no repair note for this item.

The theorem uses the already recorded
`SheafOfModules.DerivedChangeOfRingsCochainModel` to name the prescribed ordinary
extension E, derived extension F, and universal comparison. It quantifies over every
such model rather than choosing another derived functor. This is not an existence
assumption: `nonempty_derivedChangeOfRingsCochainModel` supplies the models. Its
`obj_eq`, `map_eq`, `additive`, and `universal` fields specify exactly the ordinary
tensor and its universal left derived pair. The theorem concludes ordinary exactness;
it does not assume exactness of localization or reflection. The normalized ordinary
and derived adjunctions are existential witnesses, as in the recorded coefficient
adjunction theorem. The unit formulas determine the evaluation normalization, so the
derived adjunction is not an unrelated adjunction on the same functors.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A site small in the module universe | `{C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]`, topology `J`. Object and arrow universes remain independent. |
| Ring sheaf R | `R : Sheaf J CommRingCat.{r}`. |
| Global section s | `s : (R.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections`. This is a compatible family; no terminal object is assumed. |
| S is the sheafified sectionwise localization | Every occurrence of S is `ringedLocalizationRingOfUniverses R s`, and its map is `ringedLocalizationRingUnitOfUniverses R s`. Neither is replaced by objectwise localization of sheaf sections. |
| Module sheaves and unbounded derived categories | `ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)` and its S counterpart; `DerivedCategory` and `CochainComplex ... ℤ`. |
| Size convention for derived localization | Separate explicit `[HasDerivedCategory.{wR} ...]` and `[HasDerivedCategory.{wS} ...]`. No equality of the derived morphism universes is imposed. |
| Sheafification interfaces | `HasSheafify` for commutative rings and abelian groups, `HasSheafCompose`, and `WEqualsLocallyBijective`. These are the standard technical interfaces available on the stipulated relatively small site, not geometric hypotheses or flatness assumptions. |
| E(M) = S tensor M | `m.E`, with its recorded `obj_eq` and `map_eq` identifying the sheafified tensor objects and maps. The existing construction already writes the scalar on the left. |
| F is derived scalar extension | `m.T`, the universal left derived pair with counit `m.ε`. |
| U0 is ordinary restriction | Every occurrence is the actual `restrictScalars` of the sheafified localization ring map. |
| E and U0 exact | First the theorem supplies `PreservesFiniteLimits` and `PreservesFiniteColimits` for U0; then concludes the same two properties of `m.E` for every model. U0 is additive by Mathlib and E by `m.additive`. |
| U is derived restriction | The exact U0's `mapDerivedCategory`. The existential exactness witnesses are available to elaborate this construction. |
| Natural identification F(Q_R M) with Q_S(E M) | The natural isomorphism `c : DerivedCategory.Q ⋙ m.T ≅ m.E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q`. The equation `c.hom = m.ε` pins it to the existing universal derived pair. |
| Natural identification U(Q_S N) with Q_R(U0 N) | Mathlib's canonical natural isomorphism `U0.mapDerivedCategoryFactors`, explicitly used in both normalization equations. It exists as a construction from the exactness witnesses, rather than as an extra unproved clause. |
| Ordinary unit x maps to 1 tensor x | The first section formula evaluates `a.unit.app M`, transported with `U0.map (eqToHom (m.obj_eq M))`, and equates it to `toSheafify` applied to the actual pure tensor `1 ⊗ₜ x`. |
| Ordinary counit is multiplication | The second section formula evaluates `eqToHom (m.obj_eq (U0.obj N)).symm ≫ a.counit.app N` on the sheafification image of `b ⊗ₜ x` and equates it to `b • x`. Pure tensors and sheafification determine the entire map. |
| Derived unit at every Q_R M has the same representation | For every integer-indexed M, `d.unit.app (Q.obj M) ≫ U.map (c.hom.app M) ≫ U0.mapDerivedCategoryFactors.hom.app (E(M)) = Q.map ((a.mapHomologicalComplex ...).unit.app M)`. The chain unit is degreewise the ordinary unit by the imported construction. |
| Derived counit at every Q_S N is multiplication | For every integer-indexed N, `d.counit.app (Q.obj N) = F.map (U0.mapDerivedCategoryFactors.hom.app N) ≫ c.hom.app (U0(N)) ≫ Q.map ((a.mapHomologicalComplex ...).counit.app N)`. This is the multiplication chain map after exactly the displayed comparisons. |
| Counit invertible for every derived N | `∀ N : DerivedCategory ..., IsIso (d.counit.app N)`. This is not restricted to objects literally of the form QN. |
| Precomposition is a bijection | For every A and N the theorem supplies `e : (UFA ⟶ UN) ≃ (A ⟶ UN)` with `∀ q, e q = d.unit.app A ≫ q`. Composition is in Lean's left-to-right convention. |
| Specified inverse | `∀ h, e.symm h = U.map (m.T.map h) ≫ U.map (d.counit.app N)`, namely Uε_N after UF(h). |
| UF(eta_A) = eta_UFA | The final universal equality is `U.map (m.T.map (d.unit.app A)) = d.unit.app (U.obj (m.T.obj A))`. |
| No boundedness or nonzero condition | No bounded subcategory, vanishing, domain, nontriviality, regularity, or invertibility hypothesis on s occurs. |

Dependency declarations read and used (module names omit only repeated namespace prefixes
in descriptions):

- `def-weil-size-convention`: the convention has no declaration; explicit universes
  `uC vC r wR wS` implement its role.
- `def-weil-pbc-ringed-section-localization`:
  `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`,
  `CategoryTheory.ringedLocalizationRingOfUniverses` and
  `CategoryTheory.ringedLocalizationRingUnitOfUniverses`. Read the actual localization
  presheaf, sheafification, canonical unit, and comparison with module sheafification.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, the transparent abbreviation for Mathlib's category.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` (lines 75–115), and the additive and
  essentially-surjective localization instances (lines 140–196).
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public imports.
  Read `cochainModulesMonoidal`, its localization tensor, and the actual `changeOfRings`
  construction retained from `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
  The scalar-first tensor convention already matches E in this item; no new switch is defined.
- `def-pc-sheaf-restrict-scalars`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
  `SheafOfModules.restrictScalars` and its additive instance (lines 36–46).
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` (all fields) and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `lem-pur-sheaf-ring-derived-coefficient-adjunction`:
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`,
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`. Read its full signature and
  proof docstring: ordinary Hom evaluation, universal left derived pair, and normalized
  unit, transpose and counit. The item extends the representative formulas to all complexes
  using exactness. The declaration's common derived universe is not imposed here: the
  cochain-model interface already permits independent derived universes, and the normalized
  adjunction descends directly with those localizations by the node's steps 2–4.

Proof imports are retained as the node's proof plan: `ScalarLocalizationSheafExact`
(`CategoryTheory.scalarLocalization_sheaf_exact`),
`SheafRingCoefficientOrdinaryAdjunction` (`sheafRingCoefficientOrdinaryAdjunction`),
`ExactFunctorDerivedFunctor` (`Functor.exactFunctor_derivedFunctor`), and
`KFlatResolutionIndependentCoefficients`
(`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`, including its
flat-term and degreewise-epimorphism clauses).
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` supplies exact termwise
factorization and its canonical comparison; `Mathlib.CategoryTheory.Localization.Predicate`
supplies `lift`, `fac`, `liftNatTrans`, `liftNatIso`, and `natTrans_ext`;
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` supplies the module
sheafification interface. `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
defines `Adjunction.mapHomologicalComplex` with unit and counit literally degreewise.
All stated proof dependencies are therefore imported; none requires an import-cycle omission.

Sources opened: `literature/stacks-project/sites-modules.tex`,
`lemma-flatness-sheafification` (Tag 03ET, lines 4293ff),
`lemma-sheafification-presheaf-modules` (Tag 03CY, lines 815ff), and
`lemma-adjointness-tensor-restrict` (Tag 03CZ, lines 933ff);
`derived.tex`, `lemma-pre-derived-adjoint-functors-general` (Tag 0FND, lines 9517ff);
`sites-cohomology.tex`, `lemma-K-flat-resolution` (Tag 06YS, lines 3207ff), and
`lemma-adjoint` (Tag 07A6, lines 3990ff). The node explicitly attributes the reflection
argument to its agent proof, not to a nonexistent complete Stacks assertion. All eight
steps of that argument are included in the theorem docstring, including the sheafification
step that avoids assuming S(V) = R(V)[1/s(V)].

Edge cases checked before drafting:

- If s is a unit, localization is R and the canonical adjunction specializes to identity;
  the precomposition equivalence and its inverse specialize to identity transport.
- If s = 0, or s is nilpotent, S is the zero sheaf. Its module category is trivial;
  multiplication and the derived counit remain invertible there, and the Hom types to UN
  are singleton. No `Nontrivial` condition excludes this case.
- Arbitrarily unbounded complexes occur in every representative binder; no K-flat,
  degreewise-flat or resolution hypothesis is imposed on M or N.
- Empty sites, the zero ring sheaf, and sites without a terminal object are covered:
  global sections are compatible families, not evaluation at a chosen terminal object.
- The site object and Hom universes, and the two derived Hom universes, remain separate.
- The inverse has type UFA → UN: UF(h) first maps into UFUN, then Uε_N maps to UN.
  The final unit equation has source UFA and target UFUFA on both sides.

Searches actually run with `msearch.py N9 lem-sfb-derived-scalar-localization-reflection`:

1. `leanfinder`: `Derived extension of scalars along localization of a sheaf of rings is reflective normalized unit counit isomorphism`.
   Eight hits: generic `Adjunction.derivedε_fac_app`, `derivedη_fac_app`, derived counits,
   and module sheafification adjunctions. None is the localized ring-sheaf reflection
   statement with all representative normalizations and the displayed inverse.
2. `loogle`: `"IsLocalization", "counit"`. Zero hits.
3. `grep` in `CategoryTheory`: `(localiz|Localization).*(counit|reflective)|(counit|reflective).*(localiz|Localization)`.
   Five hits in `Localization/Adjunction.lean` and `Localization/FiniteProducts.lean`;
   these localize an adjunction, without the ring-sheaf localization reflection assertion.
4. Direct project search: `rg -n 'localiz.*(counit|reflect)|counit.*localiz'` in
   `lean/WeilConjectures` and `lean/Sheaf`. Generic derived-comparison formulas and
   geometric special cases occur, but no declaration for this node's assertion.
5. Direct node-id search in `lean/WeilConjectures`, and exact candidate-name searches
   for `derivedScalarLocalization` / `scalarLocalizationReflection` in both source
   trees and `dag/lean_names_upstream.json`: no matching declaration.

Validation: the module compiled cleanly through `scompile.py` both as an isolated sandbox
module and under its final library module name. No warning remained; the proof is the
required `sorry`. Initial parser and namespace-resolution errors were repaired without
changing the node's statement. Delivery preflight and its own compile are run after the
final signature record is regenerated.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
