## Worker report

The item is stated by `CategoryTheory.scalarInternalHomAdjunction_exists` in
`Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`. The theorem supplies a
simultaneous normalized presentation of the existing derived operations, followed
by `ScalarInternalHomAdjunction`, whose fields spell out all the conclusions.
The coefficient-adjunction dependency landed during this work and is reused as
`SheafOfModules.sheafRingDerivedCoefficientAdjunction`, rather than duplicated.
Nothing is proved: the sole theorem `scalarInternalHomAdjunction_exists` has a
`sorry` proof and full source/proof docstring.
Definitions and structures have actual data or fields; there is no arbitrary
chosen isomorphism, assumed theorem, or hollow definition.

Sources read: the complete item and all its statement dependencies and records;
Stacks `sites-cohomology.tex` at `lemma-adjoint` (07A6),
`lemma-pullback-tensor-product` (07A4), `lemma-derived-pullback-composition`
(0D6D), `equation-internal-hom`, `lemma-internal-hom` (08J9), and
`lemma-section-RHom-over-U` (08JA); Bhatt--Scholze Remark 6.8.15 (the paragraph on
ambient derived operations); and the current main-20261015 blueprint
`lem-sfb-dc-hom-preserves.proof.md`, final paragraph. The node explicitly describes
its scalar comparison as an auxiliary formulation, rather than a verbatim theorem
of Bhatt--Scholze. Its eight proof steps are reproduced as a detailed proof plan
in the main theorem's docstring.

Hypothesis and conclusion correspondence:

- Site small in the module universe: `C : Type c`, `[Category.{v} C]`, and
  `J : GrothendieckTopology C`; coefficients and modules live in `max c v r`.
  `HasSheafCompose` names the standard sheaf-composition instance for forgetting
  commutativity, exactly as in the recorded change-of-rings declaration; making
  this infrastructure explicit avoids repeatedly synthesizing its long proof.
  `HasSheafify` and `WEqualsLocallyBijective` give the standard abelian
  module-sheaf infrastructure. No equality between c, v and r is imposed.
  The scalar helper section works more generally with an independent
  coefficient universe and `EssentiallySmall`.
- Ring-sheaf maps: every field quantifies over actual
  `R S : Sheaf J CommRingCat` and `a : R ⟶ S`; towers use actual composable
  `a : R ⟶ S`, `b : S ⟶ T`. Commutativity is part of these objects.
- Ordinary unbounded derived categories: `DerivedCategory (scalarModules J R)`.
  `scalarModules` transparently abbreviates the recorded `ringedSiteModules`
  and Mathlib `SheafOfModules`, not a replacement category. The family of
  `HasDerivedCategory.{w}` instances only chooses one common localization size;
  the standard localization supplies it in a sufficiently large common universe.
  No truncation, boundedness, finiteness or perfectness predicate appears.
- Actual derived scalar extension: `ScalarDerivedPair.extension_obj` and
  `.extension_map` fix the exact recorded `changeOfRings` and
  `changeOfRingsHom`. `.isLeftDerived` is the recorded universal property for
  the homotopy functor and localization, and `.computes` asserts its canonical
  comparison invertible on K-flat complexes. This is exactly the interface of
  `derivedChangeOfRingsIndependentCoefficients`, not an arbitrary left adjoint.
- Actual restriction U: `scalarRestriction a` is Mathlib's `restrictScalars`
  of `sheafCompose.map a`; `scalarDerivedRestriction a` is its exact termwise
  localization. `scalarRestrictionComparison` is Mathlib's canonical factorization.
- Actual derived tensor and Hom: `ScalarHomModels.closed` uses the recorded
  `derivedInternalHomOfUniverses`; `.model` is the landed
  `CoefficientTensorModels`. The latter fixes the total tensor on K-flat
  complexes AND its Hom-complex evaluation. It rules out twisted closed
  adjunctions. `ScalarHomTensorComparison` retains the chain comparison on
  actual total tensors, the pure-tensor generator formula, K-flat preservation,
  and the square with the universal scalar-derived comparisons.
- The displayed isomorphism for every K,N, natural in both: `.iso a` is a
  natural isomorphism `scalarHomSource M a ≅ scalarHomTarget a` between
  bifunctors on `D(R)ᵒᵖ × D(S)`. Its component is precisely
  `U H_S(F K,N) ≅ H_R(K,U N)`; the opposite first factor encodes the variance.
- Unique evaluation normalization: `.evaluation` transposes `.iso` through
  the actual R tensor-Hom adjunction to `scalarHomRestrictedEvaluation`.
  That map is tensoring by the actual scalar unit, then the counit mate
  `scalarHomRestrictionTensor` of the strong tensor comparison, then
  `U.map` of S-linear evaluation. `.unique` says any other natural
  isomorphism with this normalization is the same one. No evaluation map is
  supplied as an unconstrained arrow.
- Equivalent representing Hom description: `scalarHomBijection` explicitly
  composes inverse scalar transposition, inverse S tensor-Hom transposition,
  precomposition by the strong tensor comparison, scalar transposition, and
  R tensor-Hom transposition. `.representing` identifies this map with
  postcomposition by the stated comparison for EVERY testing object A and arrow t.
- Coefficient compatibility: `.composition` is the arbitrary R-to-S-to-T tower
  equation, including the contravariant internal-Hom transport by
  `scalarHomExtensionComp` and the covariant target transport by
  `scalarHomRestrictionComp`. The latter is induced by actual termwise scalar
  restriction. The former is Mathlib's unique left-adjoint comparison for that
  right-adjoint comparison, hence is normalized by the same units. `.identity`
  states the identity-ring-map case with both canonical transports explicitly.
- Conservativity: `.conservative` asserts `IsIso (U.map f) → IsIso f` for
  every morphism of arbitrary unbounded S-derived objects. There is no
  flatness of a, boundedness of K,N, or perfectness assumption anywhere.

Reused dependency declarations and modules:

- `CategoryTheory.ringedSiteModules`, `Sheaf.CategoryTheory.RingedSiteModules`;
  `DerivedCategory`, `DerivedCategory.Q`, `.Qh`, `.isIso_iff`, from Mathlib's
  derived category Basic/HomologySequence modules.
- `CochainComplex.IsKFlatIndependentCoefficients` and the recorded K-flat
  universe infrastructure, `Sheaf.Algebra.Homology.KFlat`;
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`, its recorded module.
- `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`,
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
  Its universal derived pair is the specification used in `ScalarDerivedPair`.
- `SheafOfModules.changeOfRings`, `.changeOfRingsHom`, from the public imports
  of `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`;
  `.IsFlatOnSite`, its recorded module.
- `SheafOfModules.restrictScalars`, Mathlib's sheaf ChangeOfRings;
  `Functor.mapHomologicalComplexUpToQuasiIso` and its factorization, Mathlib Localization.
- `CategoryTheory.derivedInternalHomOfUniverses`, its recorded module;
  `WeilConjectures.CoefficientClosedStructure`, `.CoefficientTensorModels`,
  `.coefficientTotalTensor`, `.coefficientTensorGenerator`,
  `Sheaf.Paper.CoefficientRingedTensorHomModel`. The latter already landed and
  is added to statement dependencies as an existing notion, not recreated.
- `SheafOfModules.sheafRingDerivedCoefficientAdjunction`,
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: the landed
  exactness and normalized ordinary/derived coefficient adjunction.
- `Adjunction.leftAdjointUniq`, Mathlib Adjunction.Unique;
  `Functor.mapDerivedCategoryNatIso`, `.mapDerivedCategoryCompIso`,
  `.mapDerivedCategoryIdIso`, the upstream ExactFunctor module. They supply the
  canonical coefficient-tower transports as real definitions.
- Stated proof dependencies are imported in the owning module; the
  tensor-pullback node's record explicitly retains the generic ringed-topos
  representative comparison by public reexport. This item directly imports that
  relevant generic module `RingedTopoiCanonicalTensorPullbackOfUniverses`, avoiding
  its unrelated completed-coefficient specialization.

Edge cases checked mathematically: identity maps (including their non-strict
localization transports), arbitrary coefficient towers, zero coefficients and
zero derived objects, the empty site, unbounded inputs, nonflat quotient maps
such as Z to F_p, and distinct object/arrow/coefficient universes. For Z to F_p
and K = Z/p both sides include the extra derived Tor/Ext contribution; neither
side has been replaced by ordinary tensor or Hom. Restriction is conservative
because it changes only the scalar action, not the underlying abelian sheaf.
No node fault, statement correction, or STATEMENT-DISPUTED issue was found.

Searches run (all before recording a match):

- `msearch.py leanfinder`, “Derived internal Hom restriction of scalars extension
  of scalars adjunction for sheaves of modules”: eight hits, including ordinary
  `SheafOfModules.PullbackConstruction.adjunction`, restriction, sheafification
  and module-category adjunctions; no full derived statement.
- `msearch.py loogle`, `"MonoidalClosed", "Adjunction"`: two hits,
  `MonoidalClosed.internalHomAdjunction₂` and its component theorem; generic
  closed-category infrastructure, not the ring-sheaf comparison with normalization.
- `msearch.py grep`, `(restrictScalars|changeOfRings).*(internalHom|rhom)|
  (internalHom|rhom).*(restrictScalars|changeOfRings)`: only irrelevant
  `TrivSqZeroExt` scalar-restriction hits; no exact statement.
- `msearch.py leansearch`, “Unbounded derived scalar extension of sheaves of
  modules is left adjoint to exact restriction of scalars with normalized unit”:
  ordinary `ModuleCat` adjunction hits only.
- `msearch.py loogle`, `CategoryTheory.Adjunction.derived`: the generic derived
  adjunction and its unit/counit lemmas; no ring-sheaf instantiation or normalization.
- `rg` in Mathlib, upstream `WeilConjectures`, and `lean/Sheaf` for
  restriction/change-of-rings/internal-Hom and the exact item id: no existing
  complete comparison. Reading the resulting generic framework led to reuse of
  the already landed `def-coef-ringed-tensor-hom-model`. Its full representative
  normalization and the exact recorded declarations were read.

The recorded coefficient-adjunction theorem supplies the exactness instances by
its existential projections. `ScalarDerivedPair` packages its canonical functors,
unit and transpose normalization for use in the conclusion of this item; it is
not a second theorem claiming that dependency. The sole module is owned by the
item, and every helper carries its blueprint tag. There are no dependency
repairs, new nodes, or statement corrections in this delivery.

## Second reading by N2

I independently read the item node, all ten `stmt_deps` records, the complete
`ScalarInternalHomAdjunction.lean` module, and the exact declarations used by the
module. The node's hypotheses are rendered by `C`, `Category`, `GrothendieckTopology`,
the sheaf-composition/sheafification/local-bijectivity instances, and the common
`HasDerivedCategory` instances. The theorem quantifies over actual commutative
ring-sheaf maps `a : R ⟶ S`; its `scalarModules` abbreviation is the recorded
sheaf-of-modules category, `scalarDerivedRestriction` is termwise restriction
localized to the ordinary unbounded derived category, and the `ScalarDerivedPair`
fields fix the recorded `changeOfRings` objects/maps and left-derived universal
property. Thus no flatness, perfectness, boundedness, nonzero, or characteristic
condition was added, and no universe equality was imposed.

The conclusion is rendered clause by clause: `scalarHomSource` and
`scalarHomTarget` have the component types
`U H_S(F K,N)` and `H_R(K,U N)` on the opposite-first-variable product; the
`iso` field supplies naturality in both variables. `scalarHomRestrictedEvaluation`
uses the actual derived scalar unit, the counit mate of the strong tensor comparison,
and the recorded S-evaluation. `evaluation` and `unique` give exactly the stated
transpose normalization and uniqueness. `scalarHomBijection` is the five-step
representing Hom chain, and `representing` quantifies over every testing object and
arrow. `composition` and `identity` include the canonical restriction and extension
transports for coefficient towers and identity maps. `conservative` is the requested
unbounded restriction-of-scalars conservativity statement.

I checked the dependency declarations against their records: the size convention,
module-sheaf category, derived category, total tensor, K-flat predicate, derived
change of rings, derived internal Hom, restriction of scalars, normalized scalar
adjunction, and canonical tensor-Hom representative model all provide the notions
used. The module uses those recorded declarations and does not introduce a private
copy or a pro-etale substitute. Every helper and structure has a source-place and
`(blueprint: lem-sfb-dc-hom-scalar-adjunction)` docstring; definitions contain actual
functors, maps, structures, or canonical mates, while the only postponed theorem
proof is the final `sorry`. No declaration has an unbound variable, and all lines
are within the stage convention.

I checked the edge cases named by the brief and report: identity and composable
coefficient maps, zero rings and zero objects, the empty site, arbitrary unbounded
complexes, nonflat quotient maps such as `Z → F_p`, and distinct site/object/arrow/
coefficient universes. No edge case is excluded by a hidden index, finiteness,
flatness, or positivity assumption. Searches in the immutable report and fresh
`rg` searches of the project/source trees found no existing declaration of this
complete normalized derived scalar internal-Hom comparison.

This section is the independent second reading required by H1/H11; no mathematical
or Lean-file change is needed. The only correction is replacing the placeholder
section in the report with this complete reading.
