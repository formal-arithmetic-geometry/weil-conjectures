## Worker report

The module `Sheaf.SixFunctors.CoefDualizingSiteMates` states
`AlgebraicGeometry.ProEtale.CoefDualizingSiteMates.siteRealization` and the additional
identity, cocycle, tensor-coherence, concrete-transport and dualizing-normalization clauses.
All theorem proofs are `sorry`. Definitions have actual data: compositions of the
published functors and comparison maps, or the uniquely unit-normalized isomorphism
between two universal scalar-extension presentations. There are no new DAG notions,
no dependency-node edits, and no change to the item's natural-language statement.

The local node is stage-1 reviewed under Q31, with no `lean` record. That stage-1
review does not supply a Lean statement. There is no repair note for the item.
The initial dry run found no sandbox node; the new packet supplies it.

### Hypotheses and objects, clause by clause

* The fixed algebraic closure of the finite field is `D : FiniteFieldDatum`; `D.k`
  is the field used by `Spec (.of D.k)`, and `D.p` is its prescribed characteristic.
  The prime and its inequality are `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p`.
* The finite extension is `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]`. Its valuation-ring quotients are the existing
  `Padic.coefficientExtensionRing`. No new choice of valuation ring or uniformizer occurs.
* Positive levels are parametrized by naturals `m n` and `hmn : m ≤ n`: the node's
  actual levels are `m+1` and `n+1`. Every pair of positive levels arises uniquely
  this way, including equality and the residue-field level. Finiteness is obtained
  from `Padic.finite_coefficientExtensionRing` and `Nat.succ_pos`, not imposed as a
  new mathematical assumption. `ULift.{u+1}` is the existing coefficient-size
  convention for ModuleCat-valued sheaves, not a restriction on a coefficient field.
* Lean `X` is the node's `Y`, and Lean `Y` is the node's `Z`. Their structure maps
  are `aX`, `aY`. For each, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  express exactly separated finite type over k. The same three properties on `f`,
  together with `_hf : f ≫ aY = aX`, express the stated k-morphism.
* `c : Compactification f` retains the compactification used by compact support
  and all comparisons. It is not an extra existence assumption: the separated
  finite-type hypotheses give such compactifications by the published Nagata theorem.
* `Et` and `EtPlus` abbreviate the recorded ordinary module derived category and
  its bounded-below full subcategory. `F` and `Fplus` abbreviate the published
  ordinary `rightDerivedLowerShriekOfCompactification` and its D+ restriction.
  `GA`, `GB`, `adA`, and `adB` are exactly the two right adjoints and their specified
  ordinary-etale adjunctions. These are given in the node; no pro-etale adjunction
  is hypothesized.
* `N : EtPlus ... Y` and `_hN : finiteTorConstructibleEtale ... N.obj` express
  `N ∈ Dᵇ_ctf`. The latter predicate is the existing conjunction of
  `isBoundedConstructible` and existence of `a ≤ b` with `hasTorAmplitudeIn`.
  The former quantifies over every cohomological degree and its constructible
  cohomology sheaf, with vanishing outside a finite interval. The latter quantifies
  over every degree-zero module sheaf and every degree outside the Tor interval.
  Thus none of these conditions is replaced by boundedness alone or perfectness.
* `_hGA` is the assumed finite-Tor constructibility of `GA N`. `_hGB` is the assumed
  finite-Tor constructibility of `GB(T N)`. The latter appears after the universally
  quantified tensor presentation `MN`, since its underlying object represents `T N`.
* `coefficientMap l E m n hmn` is the actual quotient ring map, using
  `Ideal.Quotient.factor` and `Ideal.pow_le_pow_right`, with the canonical ULift.
  `Etale.CoefficientTensorModel` is the recorded universal presentation of derived
  tensor. `M`, `MN`, and `MF` present, respectively, `T(GA N)`, `T N`, and `T(F_A GA N)`.
  These presentations are unique up to the unit-preserving isomorphism, and their
  existence on the finite-Tor inputs is supplied by the recorded coefficient-change
  module. The theorem is for every `M` and `MN`, not a selected arbitrary object.
  It asserts existence of the needed `MF` and of the canonical comparison's
  invertibility, rather than postulating a free comparison arrow.
* `counitWord` is literally the inverse of
  `Etale.compactSupportCoefficientComparisonPlus c M MF`, followed by scalar
  extension of the actual `adA.counit.app N.obj`. The two D+ inclusion comparisons
  are displayed explicitly; they are the existing
  `rightDerivedLowerShriekOfCompactificationPlusCompatibility` maps. The equation
  `_hv` is precisely the hypothesis that v has this adjunct under `adB.homEquiv`.
* `S`, `U`, `P`, and `J` are abbreviations for the recorded exact comparison pullback,
  derived comparison direct image, pro-etale compact support, and `U ⋙ G ⋙ S`.
  `C : ComparisonClassAdjunction ...` is the specified transported Hom bijection,
  with `P = plusEtaleOrigin` and target property the bounded-below property. Its
  normalization is part of the existing record, so no arbitrary Hom equivalence
  or ambient exceptional adjunction is introduced.
* `alpha` is `(S A X).map (GA.map (derivedComparisonAdjunction.unit.app N))`, exactly
  the comparison unit specified in the node. The conclusion asserts its
  invertibility, and that of alpha_B, rather than assuming either.
* `modelIso M` is the unique scalar-unit-preserving comparison from the chosen
  left adjoint of exact restriction to the tensor model. Its arrow is obtained
  by the existing adjunction Hom equivalence, with invertibility from the two
  universal properties. `tensorSiteIso` composes its inverse under S with
  `pbcComparisonReduction.symm`, the recorded tensor/site comparison, hence is
  the B-linear map t of the node at these universal presentations.
* `sourceIso` is t_Y followed by `TP(alpha_A)`, the node's a.
  `realizedMate` is `sourceIso.inv ≫ S(v) ≫ alpha_B ≫ J_B(t_Z)`.
  In right-to-left mathematical notation this is exactly the displayed v^pro.
  `realizedWord` is `P(a.inv) ≫ d ≫ S(h) ≫ t_Z`, exactly h^pro in proof step 3.

### Conclusions, clause by clause

* The existential `hx`, `hh`, and `hj` assert that the actual tensor source, target,
  and exceptional target lie in the specified relative Hom domains. These are
  conclusions, not extra origin assumptions. In particular nonflat quotient
  reduction is covered.
* The first conjunct after those witnesses is `C.homEquiv ... realizedWord =
  realizedMate`. It uses the existing normalized Hom bijection itself.
* The second conjunct is `IsIso v → IsIso (realizedMate ...)`.
* The third conjunct is `P.map realizedMate ≫ E = realizedWord`, where E is
  `(C.homEquiv ...).symm (𝟙 _)`. Thus E is the actual transported counit, and
  compatibility is equality of arrows, not existence of an isomorphic counit.
* `CategoryTheory.CoefDualizingSiteMates.transport_identity` gives the identity
  clause under the specified identity tensor/unit comparisons, also when chosen
  scalar extension is merely isomorphic to the identity rather than definitionally
  the identity functor.
* `transport_cocycle` states the successive-coefficient cocycle for arbitrary
  specified coherent scalar identifications. Its `e`, `ep`, and `_ht` are the
  identifications and their coherence named in the node, not extra hypotheses on
  the geometry or on the coefficient maps. `tensorCoherence` supplies that
  coherence for the actual canonical `pbcComparisonReduction` and scalar
  composition identifications, without assuming flatness of either scalar map.
  `realizedMate_transport` identifies the concrete displayed map with the
  transport to which these identity/cocycle statements apply; its ordinary v is
  precomposed only by the unique tensor-presentation identification `modelIso`.
* `dualizingNormalization` states equality of the actual recorded
  `finiteDualityObjectMap` with alpha followed by J of the recorded constant-unit
  comparison. This is the structure-morphism specialization at N equal to the
  constant unit, after exactly the unit identification used by
  `lem-weil-finite-duality-site-comparison`. The published objects are unchanged.
* No statement asserts an exceptional adjunction on all pro-etale complexes.

### Dependency declarations read and used

* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification`, its Plus version and
  `rightDerivedLowerShriekOfCompactificationPlusCompatibility`.
* `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
  Its scalar specialization is the published `Etale.scalarExtension` and the
  unit-normalized `CoefficientTensorModel`, not a second tensor construction.
* `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: the reexported
  `Etale.DerivedCategory.hasTorAmplitudeIn`; the lower-bounded predicate is read
  but not used in place of finite Tor amplitude.
* `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded
  `ConstructibleExceptionalCoefficients.System` and its finite-stage interface.
  The finite transported functor is expressed literally as U ⋙ G ⋙ S, with the
  existing `ComparisonClassAdjunction` providing its precise Hom normalization.
* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `QuasiCompact` and `IsSeparated` are the existing scheme-morphism classes.
* `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, and the module-sheaf cohomology conventions.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` and upstream Comparison.Defs:
  `Scheme.proEtaleSiteComparison`, `comparisonUpperStar`, `comparisonLowerStar`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` and separatedness via
  the existing `IsSeparated` class, as required by the node's use of this notion.
* `Sheaf.Paper.EtaleCompactSupportCoefficientChange`:
  `Etale.CoefficientTensorModel`, `.map`,
  `compactSupportCoefficientComparisonPlus`, and its isomorphism theorem.
* `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `ProEtale.compactSupportSiteComparison`.
* `Sheaf.SixFunctors.FiniteDualitySiteComparison`:
  `finiteDualityObjectMap`, `finiteDualityEtaleObject`,
  `finiteDualityProEtaleObject`, and `finiteDualitySingleTransport`.
* `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  the canonical K-flat tensor comparison underlying the scalar/site isomorphism.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
* Additional existing interfaces used: `ComparisonClassAdjunction` in
  `EtaleOriginAdjointClass`, publicly available with `SpecifiedExceptionalClassHom`;
  `pbcFixedScalarExtension`, `pbcComparisonReduction`,
  `pbcFixedScalarExtensionComp` in `WitnessCompatibility`;
  `finiteTorConstructibleEtale` in `FiniteTorAmplitudeSites`;
  `Sheaf.IsDerivedBaseChange.isIso` and ordinary adjunction Hom equivalences.

### Searches and edge cases

* LeanFinder via msearch: “Site comparison transports a normalized coefficient
  change counit mate between exceptional inverse images, preserving the transpose
  and coefficient cocycle”: eight generic sheaf comparison/restriction hits; no
  declaration states the item.
* Loogle via msearch: `CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.Functor.map`: twelve hits, including the ordinary Hom formula,
  counit formula, and naturality. These are ingredients, not this two-site statement.
* Mathlib grep via msearch: `restrictFullyFaithful|homEquiv_naturality` in
  `CategoryTheory/Adjunction`: 25 hits, generic restriction/naturality results.
* rg of both `lean/WeilConjectures` and `lean/Sheaf` for the item id, dualizing
  site mates, coefficient/site transport and normalized mates found no declaration
  for this node. Read the closest `SiteClosedCounitTransport` (closed immersion
  only), `EtaleProEtaleScalarMate` (direct-image scalar mates),
  `EtaleProEtaleCoefficientTransport`, and finite duality comparison source.
  None contains this general exceptional coefficient-counit transpose assertion.
* Edge cases checked: equal coefficient levels (identity quotient), minimum level
  one, nonflat successive quotients (no flatness binder), zero complex and empty
  source/target schemes (no nonemptiness or positive dimension assumptions),
  identity structure morphisms, arbitrary ordinary adjunction choices normalized
  by their own counits, and all permitted site morphisms. The small pro-etale
  site retains object universe u+1 and morphism universe u; only coefficient values
  use the published u+1 lift. The local EssentiallySmall instance is its existing
  canonical instance, not an extra equality of universes.

No STATEMENT-DISPUTED finding. No node correction, new node, or dependency module.

### Validation

Every compile is through scompile.py against the published live server library,
in module mode. Temporary type probes are in the sandbox scratch directory only.
The complete final module compiled cleanly in both sandbox and module locations
(24.2 seconds and 16.2 seconds), including the general identity-unit clause.
The earlier prescribed deliver2.py --no-push dry run returned OK; the final packet
is checked again below by the same prescribed wrapper. No global build
or direct repository edits or Git commands were run.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
