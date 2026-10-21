## Worker report

The main module is `Sheaf.SixFunctors.OrdinaryProEtaleDirectImagePlusComparison`.
Its main theorem is
`AlgebraicGeometry.SfbOrdinaryComparison.ordinary_proEtale_direct_image_plus_comparison`.
It states the ordinary intrinsic module direct-image theorem, including its derived-unit
normalization and the specified bounded-below comparison. The three named theorems in
this module have `sorry` proofs and source/proof docstrings. All definitions have real
data. The structures package clauses of this node; they do not introduce alternative
sites, module categories, derived categories, or right-derived constructions.

The statement is unchanged. The intrinsic etale helpers are owned by this item and
listed in its `lean.declarations`. The `def-weil-pbc-direct-image` node is byte-identical
to the live repository, retaining both recorded upstream declarations. There are no
dependency repairs, new nodes, or statement disputes.

Hypotheses and ambient objects, clause by clause:

- Schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Quasi-compactness and quasi-separatedness: `[QuasiCompact f] [QuasiSeparated f]`.
- Finite commutative coefficients: `(B : Type u) [CommRing B] [Finite B]`.
  There is no `Nontrivial B` assumption. `ULift.{u+1,u} B` is the existing size lift
  for the fixed-coefficient presentation, not a restriction on the ring.
- The original small sites are `X.Etale`, `X.smallEtaleTopology`, `X.ProEt`, and
  `ProEt.topology X`, and similarly for Y. Their object universe is u+1, their hom
  universe u, and their ring and module universe u+1. No equality of site universes
  or additional smallness hypothesis is imposed. Published universe-general module
  Grothendieck instances are specialized to these exact levels.
- Intrinsic etale modules are `Etale.intrinsicConstantModules X B`, transparently
  `SheafOfModules` over the existing `Scheme.etaleConstantModuleRing X (ULift B)`.
  Intrinsic pro-etale modules are the existing `Scheme.proEtaleRingModules X
  (Scheme.proEtaleConstantRing X B)`, also transparently `SheafOfModules`.
- Full ordinary derived categories are Mathlib `DerivedCategory` with its standard
  `HasDerivedCategory` localization. The bounded-below category is exactly Mathlib
  `DerivedCategory.Plus`, whose membership means cohomology vanishes below some
  integer. No completion, torsion subcategory, or bound is imposed on the full input.
- Etale direct image is `Etale.intrinsicModuleDirectImage f B` in this item's
  module. Pro-etale direct image is the recorded
  `Scheme.proEtaleConstantModuleDirectImage f B`. Both are actual module pushforwards
  along the site's base-change functor with the sheafified constant-section ring map.

Conclusions and canonical maps, clause by clause:

- The witnesses `rE` and `rP : RightDerivedNormalization ...` supply K-injective
  resolutions with exactly the arbitrary-quasi-isomorphism hypothesis of the recorded
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`. Their `.full` is an abbreviation
  of that very declaration, using `.resolutions`. Its recorded unit, universal property,
  uniqueness, and invertibility on K-injectives apply without introducing a second RF.
- `RightDerivedNormalization.resolutionIso r s` is the existing
  `Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso r.resolutions s`. It applies
  to every `s : M ⟶ I` with `[QuasiIso s] [I.IsKInjective]`; there is no mono hypothesis.
  The map is RF applied to Q(s), then the inverse derived unit at I, with the standard
  Q/Qh identifications. Thus the assertion specifies the canonical resolution value.
- `.plusIso` is a natural isomorphism `Plus.ι ⋙ RF ≅ RPlus ⋙ Plus.ι` for each direct
  image. RPlus is exactly Mathlib `Functor.rightDerivedFunctorPlus` of that functor,
  not an independently supplied functor. `.unit_eq` identifies the full unit followed
  by this isomorphism with the bounded-below unit included in the full category, at
  every `HomotopyCategory.Plus` object. `.plus_computes` states invertibility of the
  bounded-below unit on every bounded-below complex with injective terms. The full
  computation follows from the recorded K-injective computation since such complexes
  are K-injective (Stacks 070J).
- `comparisonRingMap` is the actual constant-section map, obtained from the existing
  `finiteCoefficientIntrinsicScalarMap` using the sheafification adjunction.
  `comparisonPushforward` is exactly sectionwise module pushforward along `toProEt`.
  `comparisonPullback` is the associated Mathlib module left adjoint, whose existence
  is supplied by the named `comparisonPushforward_isRightAdjoint`. Its proof plan
  transports to equivalent AsSmall sites and back, retaining the original sites and
  sections. No arbitrary map replaces the ring morphism.
- `comparisonPullback_exact` states additivity and preservation of finite limits and
  finite colimits, so both full and Plus derived inverse images are the existing exact
  termwise localizations `mapDerivedCategory` and `mapDerivedCategoryPlus`.
- `transportedComparison` is the recorded fixed-scalar inverse image transported
  through the actual etale equivalence and pro-etale realization. `iX` and `iY` are
  `ComparisonIdentification` witnesses. `.adjunction` makes this functor a left adjoint
  to the very same `comparisonPushforward`; `.unit_sections` fixes its unit by the
  existing `ProEtale.comparisonAdjunction` unit and the actual coefficient-realization
  unit on sections. `.iso`, `.unit_eq`, and `.unique` give the unique isomorphism of
  these left adjoints carrying one unit to the other. The adjunction is not left
  unnormalized. `realizedComparisonIso` cancels the etale equivalence using its unit,
  and `realizedComparisonPlusIso` applies the actual termwise localization.
- `k : CoefficientNormalization f B` relates fixed-scalar and intrinsic direct images.
  `.etale_sections` fixes the etale change of presentation as the identity on sections.
  `.proetale_sections` fixes the pro-etale change of presentation on the image of the
  actual module-sheafification unit. `.etalePlus_eq` and `.proetalePlus_eq` specify
  exactly `Functor.rightDerivedFunctorPlusBaseChange` of these underived maps.
- The witness `plus` is a natural isomorphism between intrinsic D+ functors. The first
  component equation in the theorem says it is exactly the canonical map from
  `prop-weil-pbc-comparison-direct-image`, conjugated by the normalized coefficient
  identifications. Its middle factor is literally
  `rightDerivedFunctorPlusBaseChange (ProEtale.lowerStarComparisonUpperStarBaseChange
  f (ModuleCat (ULift B)))`, not an arbitrary isomorphism with the same endpoints.
  The equation is tested on all fixed-scalar D+ objects, which cover intrinsic D+
  objects under the existing etale realization equivalence.
- `fullComparison` is a natural isomorphism from `Plus.ι ⋙ rE.full ⋙ nuY.full` to
  `nuX.plus ⋙ Plus.ι ⋙ rP.full`. The second component equation specifies its arrow
  as nuY applied to `.plusIso`, then exact inclusion compatibility, then `Plus.ι`
  applied to the specified `plus`, then the inverse pro-etale `.plusIso`.
  This is precisely inclusion of the bounded-below comparison under the unit-preserving
  identifications. Its input is explicitly in D+; no comparison for unbounded-below
  etale inputs is asserted.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` (and its recorded companion declarations).
- `def-weil-pbc-scheme-conventions`: convention only; universes and scheme properties are explicit above.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: convention only; universes and scheme properties are explicit above.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` (and its recorded companion declarations).
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.lowerStar` (and its recorded companion declarations). The intrinsic helpers belong to this item; its record is preserved.
- `def-weil-proetale-module-direct-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage`.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `AlgebraicGeometry.Scheme.proEtaleSiteComparison` (and its recorded companion declarations).
- `lem-pe-coefficient-comparison-data`: `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData`, `AlgebraicGeometry.ProEtale.constructibleComparisonRingMap` (and its recorded companion declarations).
- `def-sfb-right-derived-functor`: `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` (and its recorded companion declarations).
- `def-weil-pbc-bounded-derived-subcategories`: `Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean`, `DerivedCategory.Plus`.
- `lem-pe-coefficient-comparison-derived-functor`: `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor`, `AlgebraicGeometry.ProEtale.constructibleComparison_derivedFunctor`.
- `def-weil-pbc-proetale-operations`: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback` (and its recorded companion declarations).
- `prop-weil-pbc-comparison-direct-image`: `Sheaf.AlgebraicGeometry.ComparisonDirectImage`, `AlgebraicGeometry.ProEtale.isIso_comparisonDirectImagePlus` (and its recorded companion declarations).
- `prop-pur-kinjective-resolutions-exist`: `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`, `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `lem-sp-grothendieck-enough-injectives`: `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean:380-381`, `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`.
- `lem-weil-pbc-kinjective-total-derived`: `Sheaf.CategoryTheory.KInjectiveTotalDerived`, `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
- `lem-weil-pbc-dplus-injective-representative`: `Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean`, `DerivedCategory.Plus.exists_injective_nonempty_iso`.
- `lem-weil-pbc-right-derived-plus-injective`: `Mathlib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`, `CategoryTheory.Functor.rightDerivedFunctorPlus`.
- `lem-weil-pbc-kinjective-hom-derived`: `Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean`, `CochainComplex.IsKInjective.Qh_map_bijective`.
- `lem-sc-bounded-below-injective-resolution-existence`: `Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean`, `CochainComplex.Plus.exists_quasiIso_injective`.
- `lem-pe-constant-left-module-inverse-image`: `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`, `CategoryTheory.constant_left_module_inverse_image` (and its recorded companion declarations).
- `lem-weil-pbc-module-inverse-image-unit-comparison`: `Sheaf.CategoryTheory.ModuleInverseImageUnitComparison`, `SheafOfModules.inverseImage_underlying_unit_of_ring_presentation`.

The module also uses the existing coefficient-realization declarations
`Scheme.etaleConstantModuleFunctor`, `Scheme.etaleConstantModuleFunctor_isEquivalence`
in `WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`, and
`ProEtale.finiteCoefficientIntrinsicRealization`, `finiteCoefficientIntrinsicComparison`,
`finiteCoefficientIntrinsicScalarMap`, and `finiteCoefficientModulePresheaf` in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison` / `ProEtaleFiniteModules`.
These are reused, not privately copied. Generic inverse-image and direct-image data are
Mathlib `SheafOfModules.pullback`, `pushforward`, and `pullbackPushforwardAdjunction`;
exact localization is the existing `Functor.mapDerivedCategory*` API. The coefficient-sized
AsSmall comparison data and derived theorem are imported as the recorded original-site
transport inputs. The proof docstrings explain the transport instead of equating site
universes.

Edge cases checked against the signature and constructions:

- The zero ring is allowed: all coefficient operations are unital ring/module operations
  with no nontriviality hypothesis, and the resulting module categories are zero.
- Empty schemes and the identity morphism are allowed. Ring maps are constructed from
  constant sections uniformly, without choosing a point, a cover member, or a nonempty
  object. The comparison map is the same canonical map for identity morphisms.
- A complex or sheaf concentrated in any integer degree is allowed. D+ has an existential
  lower cohomological bound, not a fixed bound or strict nonnegative degrees.
- The resolution comparison allows every quasi-isomorphism to a K-injective target,
  including nonmonomorphisms. Bounded-below injectives compute both units.
- The full total derived functors accept unbounded complexes, while fullComparison only
  accepts D+ etale inputs, in agreement with Bhatt--Scholze Remark 5.4.4.
- Site objects at u+1 and morphisms at u stay distinct; ULift moves only coefficient
  representatives and the published realization equivalence compares the presentations.

Searches for an existing statement (before introducing the owning declarations):

- `msearch.py ... leanfinder` with query
  `Intrinsic sheaves of modules over a constant finite ring: K-injective total right derived
  direct image agrees with bounded below derived direct image and etale proetale comparison`:
  eight results about Grothendieck sheaf categories, sheafification, and module pushforward
  sections; none stated this combined theorem or its unit-normalized intrinsic comparison.
- `msearch.py ... loogle` with query
  `Functor.rightDerivedFunctor, Functor.rightDerivedFunctorPlus, Adjunction.leftAdjointUniq`:
  no results, and `Functor.rightDerivedFunctor` was unknown to the Mathlib index. The
  project's arbitrary-quasi-isomorphism declaration was then read directly and reused.
- `msearch.py ... grep` with regexp `rightDerivedFunctor.*[Pp]lus|rightDerived.*[Ii]so`
  in Mathlib CategoryTheory: 22 general localization/derived isomorphism hits, no combined
  intrinsic direct-image/Plus/comparison statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for ordinary direct image, Plus,
  comparison, intrinsic etale module pushforward, and the exact new identifiers; also
  the item id in `lean/WeilConjectures`: no existing declaration of the full node.
  `dag/lean_names_upstream.json` and the Mathlib CategoryTheory tree have no collisions
  for `RightDerivedNormalization`, `intrinsicModuleDirectImage`,
  `intrinsicConstantRingMap`, or `SfbOrdinaryComparison`.
- The nearby `ProEtaleDirectImageComparison` statement concerns fixed scalar coefficients
  and a different comparison interface; it does not give this node's arbitrary-resolution
  total functors, unit normalization, and intrinsic coefficient identifications.
- Mathlib's `Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean` supplies the
  general actual module pushforward. It does not specialize the etale constant-section
  scalar map required by this node's intrinsic module clause.

Source reading: the local Bhatt--Scholze PDF, Lemma 5.4.3 and Remark 5.4.4, and local
Stacks `derived.tex` Tags 070K and 070J and `proetale.tex` Tag 099R were read. The main
docstring follows all seven DAG proof steps, including the derived-unit equation.
There is no source-based statement correction.

## Returned-delivery repair (H13)

The independent review of immutable head `f9a8a166fdc6` accepted the item mathematics
but returned the replacement of the landed `def-weil-pbc-direct-image` record. The
initial saved-packet dry run passed at `bbd877a8976`; that mechanical pass did not
resolve the review finding. This repair moves all eight intrinsic etale declarations
from `Sheaf.AlgebraicGeometry.IntrinsicEtaleDirectImage` into the item module, preserves
their bodies and signatures, retags their docstrings with this item's blueprint ID,
and records all eight under this item's `lean.declarations`. Their names are:

- `Etale.intrinsicConstantModules`
- `Etale.intrinsicBaseChange_continuous`
- `Etale.intrinsicConstantRingMap`
- `Etale.intrinsicModuleDirectImage`
- `Etale.intrinsicModuleDirectImage_additive`
- `Etale.intrinsicConstantModules_hasDerivedCategory`
- `Etale.intrinsicConstantModules_grothendieck`
- `Etale.intrinsicRightDerivedModuleDirectImagePlus`

All names above have prefix `AlgebraicGeometry`. The separate helper module is removed
from this packet. The dependency node is copied byte-for-byte from live, retaining
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `Etale.lowerStar`,
`Etale.rightDerivedLowerStarPlus`, and `sorry_free: true`. The item still imports and
uses those upstream operations through its coefficient normalization and comparison.
No theorem signature, helper body, hypothesis, or component equation changes.

Self-check: the same ordinary-site objects and distinct universes remain. Finite B
has no nontriviality assumption. The arbitrary quasi-isomorphism resolution formula,
unit-normalized D+ restriction, canonical derived comparison, and D+-only input of
`fullComparison` are unchanged. The helper declarations use the item blueprint tag.
There is only one delivered Lean file, owned by the item node. Independent second
reading remains the maintainer's review, as specified in the worker brief.

Validation: `scompile.py Q10 lem-sfb-ordinary-proetale-direct-image-plus-comparison`
compiled the consolidated module cleanly against the live server library, both as
the sandbox file (14.4 s) and at its library module path (14.1 s). No errors or
warnings were emitted. The repaired-packet dry run follows. No global build was run.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
