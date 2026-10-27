## Worker report

The module `Sheaf.Algebra.Homology.OpenTensorScalarUnitAugmentation` states
`SheafOfModules.OpenTensorAugmentation.augmentation_exists`. Its only postponed
proof is this theorem, with the node's six-step proof and dependency references
in its docstring. All helper definitions contain actual data. The theorem supplies
strict transitions, the normalized total comparison, both unit augmentations,
and their commuting square, naturally in the two input complexes.

The statement is packaged as `Nonempty (Augmentation R V A)`. This is not a choice
of an unspecified comparison: every map is fixed by formulas on the actual
presheaf generators, and the supplied objects are the explicitly constructed
ordinary scalar-extension and signed direct-sum total tensors. The sheafification,
tensor, and direct-sum universal properties determine the maps from those formulas.
The supplied generator-normalized isomorphism therefore is the composite of the
coefficient-linear comparison and slice tensor comparison specified in the node.
No object is defined by choosing an arbitrary witness of this theorem.

Hypotheses and objects, clause by clause:

- The site is `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`.
  The independent levels `c`, `v`, `r` put modules and coefficient rings in
  `max c v r`, so the site is small relative to the module universe. `R` is the
  node's `B : Sheaf J CommRingCat`, and `V : C` is arbitrary. The standard
  `HasSheafify` and `WEqualsLocallyBijective` instances on this site and its slice
  expose the existing sheafification implementation; they are available in this
  small-site universe and impose no additional geometric condition.
- `R.over V`, `ringedOpenRestrictionOnComplexes R V`, and
  `ringedOpenExtensionOnComplexes R V` are the recorded restriction and exact
  extension-by-zero constructions, termwise. No substitute adjoint is introduced.
- `A : AlgebraTowers R` is the existing abbreviation `ℕᵒᵖ ⥤ Under R`.
  An object of `Under R` is a sheaf of commutative unital `R`-algebras; its
  morphisms commute with the structure maps and are unital. Functor laws give
  every identity and composite transition. Index `op k` represents the node's
  positive index `k+1`. `sliceAlgebras R V` gives `A_{n,V}`.
- `Inputs R V` consists of every pair `(Q,F)` of cochain complexes over `R.over V`
  and `R`, indexed by all of `ℤ`. The morphisms are pairs of chain maps. No
  boundedness, flatness or other property is part of this type.
- `scalarComplex a` is the existing ordinary scalar-extension functor `extend a`
  applied termwise. It gives `Q_n` and `F_n`. Its tensor presentation writes the
  scalar coefficient first, i.e. `a ⊗ x`; this is the standard scalar-extension
  presentation of the node's `x ⊗ a`, with its canonical commutative-ring tensor
  symmetry. `scalarExtensionSection` inserts precisely that pure tensor using
  the actual presheaf-to-sheaf unit.
- `source R V` is `G`, and `sliceSource R V` is `G_V`. Both use the already
  recorded `ringedOpenTotalTensor`, the signed direct-sum total tensor.
  `ringedOpenTensorι` supplies the `(p,q)` summand whenever `h : p+q=d`.
- `targetLevel R V (A.obj n)` is exactly the scalar restriction of
  `Tot((((j!Q) ⊗_R A_n) ⊗_{A_n} (F ⊗_R A_n)))`.
  `sliceTargetLevel` is exactly the scalar restriction of
  `Tot((Q ⊗_{R_V} A_{n,V}) ⊗_{A_{n,V}} j*(F ⊗_R A_n))`.
  Scalar restriction is the existing section-preserving `restrictScalars`.
- `extensionSection` is the direct-sum insertion indexed by `f : W ⟶ V`
  followed by the extension sheafification unit. `sourceSection`, `targetSection`,
  `sliceSourceSection`, and `sliceTargetSection` compose these actual units and
  pure tensors with total-summand insertions. They never identify sections of a
  tensor sheaf with a tensor product of groups of sections.

Conclusions, clause by clause:

- `StrictTotals.t` and `.s` are transitions between these fixed level functors.
  Their `t_generator` and `s_generator` fields apply `(A.map g).right` to both
  coefficient entries, for every index arrow and homogeneous total summand.
  `t_id`, `t_comp`, `s_id`, and `s_comp` give strict laws. `StrictTotals.T` and
  `.S` assemble the resulting genuine functors. These fields are conclusions of
  the existence theorem, not additional assumptions on the input tower.
- `Augmentation.gammaBase` is the ordinary `G ≅ j!G_V` chain isomorphism.
  `base_generator` fixes `[x]_f ⊗ y ↦ [x ⊗ j*y]_f` in each total summand.
  The recorded slice comparison's generator uniqueness identifies this with
  the comparison whose inverse is its open-unit transpose.
- `Augmentation.gamma` is a natural isomorphism of strict towers with exactly
  the fixed `T` and `j!S` endpoints. `gamma_generator` specifies its action for
  every coefficient pair `a,b`, sending `([x]_f ⊗ a) ⊗ (y ⊗ b)` to
  `[(x ⊗ j*a) ⊗ (j*y ⊗ j*b)]_f`. By the recorded coefficient-linear and slice
  generator universal properties, this specifies exactly
  `gamma^{A_n} ∘ Tot(r_{Q,n} ⊗ 1)`, including the identity-on-summands
  scalar-restriction identification. Its inverse is fixed by the isomorphism
  equations and hence agrees with that composite's canonical inverse.
- `cT` and `cS` are natural transformations from the constant towers.
  `cT_generator` and `cS_generator` insert `1` in both scalar-extension factors
  on precisely the homogeneous presheaf generators of the node.
- `square` is the equality `cT ≫ gamma.hom = lowerRoute ...` in the category
  of strict systems. `lowerRoute` spells out `Delta(gammaBase)` followed by
  `J_B(cS)`, using the standard constant/composition isomorphism. `extendInputs`
  and `extendTower` are actual whiskering by the recorded termwise extension.
- `common_value` is the displayed generator value
  `[(x ⊗ 1) ⊗ (j*y ⊗ 1)]_f`. Together with `square` it gives this value for
  both routes.
- Every component is a `CochainComplex` morphism, so the equality respects the
  signed total differential. Every tower morphism is a natural transformation
  in `ℕᵒᵖ`, so it respects every coefficient transition. The level objects are
  functors on `Inputs`, and all comparison and augmentation components are
  natural transformations there, encoding naturality in both `Q` and `F`.
- `atInput` evaluates at `(Q,F)` to obtain maps of strict complex systems.
  `localized_square` applies the actual localization functor `W.Q` to the
  two routes, for every morphism property `W`. In particular it covers the
  localization at levelwise quasi-isomorphisms. No inverse limit or product
  occurs anywhere in the construction or conclusion.

Dependency declarations used (all recorded statement-dependency modules are
publicly imported; the recorded proof-only modules are imported for stage 3):

| Node | Module and declarations |
| --- | --- |
| def-weil-pbc-sites-and-cohomology | `Sheaf.CategoryTheory.SiteCoveringAxioms`, `CategoryTheory.Precoverage.IsSiteForCoverings`; its Grothendieck topology/sheaf convention is used directly. |
| def-weil-size-convention | Metatheoretic convention: explicit independent universes, no declaration. |
| def-pur-localized-ringed-site | `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, `SheafOfModules.overFunctor`, `CategoryTheory.Sheaf.over`. |
| lem-pur-site-restriction-module-adjunction-exact | `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, `localizedSystemExtension`, `localizedSystemRestriction`, `localizedSystemExact`, `localizedSystemAdjunction`. |
| def-weil-inverse-system | `Mathlib.CategoryTheory.Functor.OfSequence`, the `ℕᵒᵖ`-functor convention of `Functor.ofOpSequence`. |
| def-weil-sheaf-of-modules-category | `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`. |
| def-pur-sheaf-tensor-product | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, `cochainModulesMonoidal` and its existing monoidal localization. |
| def-pc-cochain-complex-modules | `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex`. |
| def-pc-tensor-complex-sheaves | `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`, through the recorded total-tensor helpers. |
| lem-sf-ringed-slice-tensor-generators | `Sheaf.CategoryTheory.RingedSliceTensorGenerators`, `exists_ringedSliceTensorGenerators`, with normalized forward, unique comparison, inverse transpose, and unit formulas. |
| lem-sf-ringed-open-total-tensor-kflat | `Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat`, `ringedOpenExtensionOnComplexes`, `ringedOpenRestrictionOnComplexes`, `ringedOpenTotalTensor`, `ringedOpenTensorι`. Only its ordinary constructions are used, without a K-flatness premise. |
| def-weil-extension-by-zero-presheaf | `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`, `extensionByZeroPresheaf`. |
| def-weil-presheaf-modules-sheafification | `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, `PresheafOfModules.sheafification`. |
| lem-sf-cbc-slice-tensor-generator-coherence | `Sheaf.CategoryTheory.SliceTensorGeneratorCoherence`, `extend`, `Coherence`, `coherence_exists`; its publicly imported `LocalizedStrictTensor` helpers supply `Modules`, `AlgebraTowers`, `sliceAlgebras`, `scalars`, `pure`, `extensionSection`, and `scalarExtensionSection`. |
| def-pc-sheaf-restrict-scalars | `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, `SheafOfModules.restrictScalars`. |
| def-weil-abstract-derived-category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and the localization convention. The stronger pre-localization equality is stated explicitly. |
| lem-pur-derived-change-of-rings (added landed dependency) | `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, `SheafOfModules.DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`. Only the model's prescribed ordinary functor, object/map equations, and additivity instance are used. |

The last dependency supplies additivity of the actual ordinary scalar-extension
functor, needed for termwise application to complexes. `extensionAdditive`
transports that existing instance through its prescribed object and map equations;
it introduces no new postponed theorem and no derived or K-flat input. The model
is used only to obtain a proposition about the already constructed functor. This
is not choosing scalar-extension data from an unconstrained existence statement.
The node's only non-`lean` change is adding this already landed dependency to
`stmt_deps`, as permitted by brief-stage2 section 5.

Sources checked: `literature/stacks-project/sites-modules.tex`, Tag 0E8I,
`lemma-j-shriek-and-tensor`, and `sites-cohomology.tex`, Tag 0GL1, together with
the node's explicit strict scalar-unit refinement and proof. All dependency node
statements, records, and the recorded declaration interfaces/docstrings were read.
No statement correction or dependency-interface repair was needed.

Edge cases checked: the zero complex, zero module and zero coefficient ring are
allowed; there is no nontriviality hypothesis. The tower may be constant, and
identity/composite arrows are included explicitly. There is no tower level zero
being dropped: the `ℕ` convention renumbers the positive levels by `k+1`.
All positive, zero and negative cochain degrees and every decomposition `p+q=d`
are quantified, so unbounded complexes are retained without a finite-sum
assumption. An empty collection of arrows into `V` gives the empty direct sum
in the existing extension construction, with generator assertions vacuous there.
No choice of site object or morphism universe equates the independent levels.
The localization assertion also covers identity localizations.

Searches for an exact existing statement:

- Prescribed `msearch.py` LeanFinder query: "Extension by zero projection formula
  for total tensor complexes commutes with scalar unit augmentation of inverse
  systems" returned eight tensor/total-complex infrastructure hits, including
  `HomologicalComplex.ιTensorObj`, and no matching statement.
- LeanFinder query: "Extension by zero tensor comparison commutes with scalar
  unit augmentations for strict inverse systems of cochain complexes" returned
  eight unit/tensor-complex hits, including `HomologicalComplex.rightUnitor`,
  and no matching statement.
- LeanSearch query: "Extension by zero of module sheaves commutes with scalar
  tensor unit augmentation of strict inverse systems of total cochain tensor
  products" returned eight unrelated scalar/sheafification hits; no match.
- Loogle queries `SheafOfModules, CategoryTheory.NatTrans` and
  `SheafOfModules, CochainComplex` returned zero hits.
- Prescribed Mathlib grep query `scalarUnit|scalar_unit|augmentation` in
  `Algebra/Category/ModuleCat/Sheaf` and `Algebra/Category/ModuleCat` returned
  zero hits.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for scalar-unit,
  augmentation and open-tensor terms found the ordinary tensor, scalar extension,
  localization and slice-coherence infrastructure used here, but no statement
  of this strict augmentation square. The exact item id had no upstream match.
  The upstream declaration index had no `OpenTensorAugmentation` collision.
  These searches therefore led to a new statement module, using the existing
  notions and constructions, with no new definition node.

Validation: prescribed `scompile.py` passed both sandbox and named-module checks
with no errors or warnings (the theorem's `sorry` is intentional at stage 2).
The required delivery dry run and delivery wrapper follow this report.

No node fault or disputed statement was found.

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
