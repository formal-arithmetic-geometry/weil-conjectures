## Worker report

The module `Sheaf.CategoryTheory.ScalarLocalizationSheafExact` states
`CategoryTheory.scalarLocalization_sheaf_exact`, with its proof exactly `by sorry`.
No definitions, helper axioms, dependency repairs, or new nodes are introduced.
The node's mathematical statement, dependencies and proof are unchanged.

Clause-by-clause correspondence:

- A small site is encoded by `{C : Type uC} [Category.{vC} C]`,
  `[EssentiallySmall.{u} C]`, and `J : GrothendieckTopology C`. The site object,
  morphism and coefficient universes are independent. Essential smallness in the
  coefficient universe expresses the node's smallness relative to modules; it
  does not require objects and morphisms to live in the same universe. This is
  the project's recorded site/sheaf convention, not a pretopology with extra
  pullbacks or a scheme site.
- The commutative ring sheaf is `R : Sheaf J CommRingCat.{u}`.
  `[HasSheafify J CommRingCat.{u}]` supplies the sheafification structure used by
  the dependency's actual ring localization. Sheafification exists for these
  algebraic coefficients on a small site; the binder exposes the existing
  interface, rather than assuming a property of R or of the section s. Additive
  sheafification and the module abelian structures are inferred from the
  essentially small site. No enough-points hypothesis is used.
- The global section is `(s : (R.obj ⋙ forget CommRingCat).sections)`, a compatible
  family over all site objects, with no terminal object assumed.
- The ring R_s is exactly `ringedLocalizationRingOfUniverses R s`, the recorded
  localization dependency: the ring sheafification of sectionwise
  `Localization.Away (s.val V)` with localization-lift restrictions.
  Its canonical ring map is `ringedLocalizationRingUnitOfUniverses R s`.
- Both categories use the dependency's `ringedSiteModules` abbreviation for
  Mathlib's `SheafOfModules`, after forgetting commutative rings to rings.
  The target category is modules over R_s, not an endofunctor on R-modules.
- The existential `E` packages the actual change-of-rings objects and maps
  already constructed by the tensor dependency. `hE` identifies each object
  with `SheafOfModules.changeOfRingsOfUniverses` along the canonical ring map.
  The map equation identifies E(f), under those object identifications, with
  `SheafOfModules.changeOfRingsHomOfUniverses`, the sheafification of `1 ⊗ f`.
  This existential is the functorial packaging of the specified construction,
  not a choice of an arbitrary left adjoint. Its objects and all arrows are fixed.
- `E.Additive` is the additivity clause. `PreservesFiniteLimits E` and
  `PreservesFiniteColimits E` give exactly the node's chosen exactness formulation,
  equivalent in these abelian categories to preservation of short exact sequences.
- The final universal quantifier over F and `Nonempty (F ≅ E)` is the clause for
  every functor naturally isomorphic to actual change of rings. Its conclusion
  repeats additivity and both finite preservation properties.
- There are no point, enough-points, scheme, nonzero, characteristic, or complex
  boundedness parameters. No flatness of a general coefficient map is assumed.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its module retains the
  Grothendieck-topology/sheaf encoding used here. The theorem does not impose
  the additional data of a particular presentation by a precoverage.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` (transparent abbreviation for
  `SheafOfModules`; Mathlib supplies the abelian structure).
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `ringedSectionLocalizationPresheafOfUniverses`,
  `ringedSectionLocalizationOfUniverses`, `ringedLocalizationRingOfUniverses`,
  `ringedLocalizationRingUnitOfUniverses`, and their comparison. The actual
  carrier, localization restrictions and ring algebra map were read.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` (recorded
  tensor dependency) publicly retains
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`:
  `SheafOfModules.changeOfRingsOfUniverses` and
  `SheafOfModules.changeOfRingsHomOfUniverses`. The former sheafifies
  sectionwise `ModuleCat.extendScalars`; the latter sheafifies its map on
  module morphisms. The source explicitly retains the target-ring action.

All recorded, available proof-dependency modules are imported non-publicly when
not already public statement imports: `Mathlib.RingTheory.Flat.Localization`
(`IsLocalization.flat`), `Mathlib.RingTheory.Flat.Basic`
(`Module.Flat.lTensor_exact`/`rTensor_exact`), `Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`
(`PresheafOfModules.Monoidal.tensorObj`),
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
(`PresheafOfModules.sheafification`),
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`
(`PresheafOfModules.isFlat_sheafification_obj`),
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
(`SheafOfModules.IsFlatOnSite`),
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
(`SheafOfModules.tensorClosed`),
`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
(`SheafOfModules.restrictScalars`), and
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
(`CategoryTheory.moduleSheaves_colimits_forgetful`). Their source signatures
and the theorem docstrings were inspected. The proof docstring follows all six
steps of the node, including the finite-limit presheaf argument, the retained
scalar action, exactness detection after forgetting, and isomorphism transport.

Source read: `literature/stacks-project/sites-modules.tex`,
`lemma-flatness-sheafification` (03ET), the immediately preceding
`lemma-flatness-presheaves` (03ES), and the change-of-rings construction and
`lemma-adjointness-tensor-restrict`. These identify the scalar-extension
construction as sheafified sectionwise tensor, exactly as in the Lean dependency.

Edge cases checked before and while writing:

- Empty site: the global section is a compatible empty family and all sheaf and
  module categories retain their usual definitions; no object or point is selected.
- Zero ring and s = 0: `Localization.Away` allows the zero ring; the corresponding
  zero scalar-extension functor is additive and preserves finite limits/colimits.
- Nilpotent local sections: zero section localizations are flat, as the node's
  first proof step requires; no nonzero denominator condition appears in Lean.
- Unit section: the usual canonical equivalence is allowed, as are arbitrary
  functors naturally isomorphic to E. No equality to a chosen model is demanded of F.
- Empty finite diagram: preservation classes include the terminal and initial
  objects, hence finite limits/colimits include the zero-object cases.
- Unequal site object/morphism universes are retained; the tensor API's coefficient
  and module arguments are explicitly instantiated without equating either to uC/vC.

Searches for reuse (2026-10-21):

- `msearch.py ... leanfinder "Localization of a sheaf of commutative rings at a
  global section gives an additive exact change of rings functor on sheaves of
  modules"`: eight hits, on ordinary localized-module exactness and abelian
  categories of module sheaves; no theorem with this sheaf-valued scalar target.
- `msearch.py ... loogle "SheafOfModules,
  CategoryTheory.Limits.PreservesFiniteLimits"`: six hits for forgetful and
  sheafification functors, not scalar localization.
- `msearch.py ... grep "(changeOfRings|extendScalars|localiz).*(exact|finiteLimits)|
  [Ee]xact.*(changeOfRings|localiz)" Algebra/Category`: nine hits; ordinary
  `ModuleCat` localization and categorical localization of sheafification.
- `msearch.py ... leansearch "The scalar extension functor to the localization
  of a ring sheaf is additive and preserves finite limits and finite colimits"`:
  eight hits including `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`,
  ordinary localized-module additivity and unrelated category localization.
- `rg` in project `lean/WeilConjectures` and `lean/Sheaf` for scalar localization,
  exact localization, change of rings and extension of scalars found the existing
  construction above. `grep -rn` for this item's id in `lean/WeilConjectures`
  found no existing attachment. The proposed declaration name is absent from
  the project and `dag/lean_names_upstream.json`.
- Inspected partial matches: `CategoryTheory.scalarLocalization_exact` in
  `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` only treats the older
  `SmallCategory` interface and lacks the natural-isomorphism clause.
  The private theorem of the same basename in
  `Sheaf.CategoryTheory.LocalizationInverseImageCoherence` is about the tensor
  endofunctor on R-modules. Neither states this node, so neither can be bound
  as an exact existing declaration. No existing construction is redefined here.

No statement dispute or mathematical node fault was found. The retired
`Sheaf.CategoryTheory.CompactObject` example is empty on the current checkout;
its node points to `WeilConjectures.CategoryTheory.CompactObject`, whose current
header and definition were read instead.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
