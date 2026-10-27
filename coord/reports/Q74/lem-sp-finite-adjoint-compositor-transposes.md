## Worker report

The module `Sheaf.Paper.FiniteAdjointCompositorTransposes` states
`AlgebraicGeometry.ProEtale.finiteAdjointCompositorTransposes`, with one postponed
proof (`sorry`). Three elementary interface helpers belong to this same notion:
`finiteAdjointSupport` abbreviates the existing compact-support restriction;
`finiteAdjointSiteSupportIso` pastes the existing site comparison with the existing
bounded-below/ambient compatibility; `FiniteAdjointCompositorDatum` packages the
given three adjunctions and normalized left compositor. None chooses any data from
an existence proposition, and no definition contains `sorry`.

The source read is the CURRENT blueprint:
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md`,
paragraphs (1)-(2). The item's own statement and split are unchanged.

Hypotheses and clauses:

* Distinct primes and characteristic: `ℓ p`, `Fact ℓ.Prime`, `Fact p.Prime`,
  `_hpℓ : p ≠ ℓ`, `k`, `Field k`, `CharP k p`. Primality implies positive p.
* The separated finite-type k-schemes: the `Over (Spec (.of k))` instances for
  X, Y, Z, and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` of each
  structure morphism. These are exactly separated finite type over the field.
* Smooth k-morphisms: f, g, their `IsOver` instances, natural d and e, and
  `SmoothOfRelativeDimension d f` and `SmoothOfRelativeDimension e g`.
  The `QuasiCompact f` and `QuasiCompact g` binders express the quasi-compact
  part of finite type in the setting (also implied by its finite-type
  k-schemes); they are needed by the existing normalized compositor interface.
* Coefficient-independent compactifications: cf, cg, ch are bound BEFORE either
  coefficient ring, and are the SAME inputs in DA and DB. The factors are the
  genuine open/proper factors of `Compactification`.
* Arbitrary finite commutative ℓ-primary rings: `CommRing`, `Finite`, `_hA`,
  `_hB`; arbitrary unital ring map `φ : A →+* B`. There is no flatness,
  projective-dimension, field-coefficient or residue-field assumption.
* Ordinary intrinsic Dctf: `spFiniteConstructibleTorCategory T R` is the existing
  full subcategory of `Scheme.proEtaleDerivedCategory T R`, defined by bounded
  cohomology, intrinsic constructibility in every degree, and finite Tor
  amplitude. It includes all ambient derived morphisms. No completion or
  etale-origin condition is placed on this category or on K.
* Given F, H and counits: DA/DB have preservation witnesses `hFf`, `hFg`,
  `hFh` for the actual `reductionCtfCompactSupport`, right adjoints `Hf`, `Hg`,
  `Hh` and actual adjunctions `adjf`, `adjg`, `adjh`. The witnesses only let
  the existing ambient functors restrict to the full subcategories.
* The proper/open normalized alpha is `DA.alpha` / `DB.alpha`. Their
  `normalization` field states, on EVERY bounded-below etale witness in Dctf,
  the actual transport formula C_g, F_g(C_f), etale alpha, inverse C_gf.
  `finiteAdjointSiteSupportIso` uses `reductionSiteCompactSupportIso`, whose
  proper factor is the canonical counit mate and whose open factor is the
  specified extension comparison. Its last paste is
  `Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility`.
  Thus alpha is constrained by the recorded construction, not arbitrary.
  `coherenceEtaleCompositor` evaluates the canonical proper/open normalized
  etale compositor on the three supplied compactifications.
* Scalar extension: hSX/hSY/hSZ are the preservation witnesses required by
  `reductionCtfScalar φ T`, whose ambient functor is literally the recorded
  `scalarExtensionFunctor φ T`. They impose no condition on any object beyond
  membership in Dctf and are the preservation assertion already in its node.
* The isomorphisms bf, bg, bh are the b maps. `_hbf`, `_hbg`, `_hbh` equate
  their underlying components with `reductionDirectImageComparison φ c.i c.g`
  at EVERY Dctf object; a freely chosen isomorphism is not substituted for b.
* cfCoeff, cgCoeff, chCoeff are the c isomorphisms. hfCounit, hgCounit,
  hhCounit are exactly the three displayed individual counit equations.
  Those equations uniquely specify the maps under the given adjunctions, as
  in `reductionExceptional_isIso`; no arbitrary exceptional comparison remains.
* `hbComp` is precisely the assumed compact-support coefficient identity,
  written left-to-right in Lean composition order.
* First conclusion: existential natural isomorphisms thetaA and thetaB, with
  the displayed alpha/counit normalization, and uniqueness for each ring among
  all natural isomorphisms satisfying that normalization. This is uniqueness
  separately at A and B, not merely uniqueness of a chosen compatible pair.
* Composite counits: the next two conjuncts identify `adjf.comp adjg`'s counit
  with `Fg.map (epsilon_f(Hg K)) ≫ epsilon_g(K)` at each ring.
* Exact transpose: the next conjunct uses the INVERSE Hom equivalence of the
  composite B-adjunction on `cfCoeff(Hg_A K) ≫ Hf_B.map(cgCoeff(K))`.
  Its right side is `Fg_B.map(bf.inv(N)) ≫ bg.inv(Ff_A N) ≫ S_Z.map(E_A(K))`.
  This is precisely the requested inverse composite, since functors preserve
  inverses and a composite inverse reverses order.
* Final conjunct: `chCoeff(K) ≫ thetaB(S_Z K)` equals
  `S_X.map(thetaA(K)) ≫ cfCoeff(Hg_A K) ≫ Hf_B.map(cgCoeff(K))`.
  Both are actual morphisms in the full B-linear intrinsic derived category.

Recorded dependencies read and used:

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`; the
  setting is rendered as explicit geometric binders, while compactifications
  themselves are supplied, once for both coefficient rings.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `SmoothOfRelativeDimension`; the latter supplies the pure dimensions.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`
  and its derived/site-comparison presentation; accessed through the recorded
  intrinsic realization interfaces, not a new coefficient sheaf.
* `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, including its imported
  intrinsic `Scheme.IsConstructibleProEtaleModuleSheaf` used by Dctf.
* `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude` and the imported intrinsic
  `Scheme.HasFiniteProEtaleTorAmplitude`, used in the Dctf definition.
* `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`:
  `CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible`,
  providing the given restricted adjunction convention; the statement uses its
  ordinary presentation from ReductionExceptional.
* `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `Etale.unboundedEtaleLowerShriekCompIso`; its normalized bounded-below form
  on supplied compactifications is `coherenceEtaleCompositor`.
* `Sheaf.Paper.FiniteCompactSiteCoherence`: `finiteCompactSiteCoherence`,
  `finiteCompactSiteCompositionPlus` and the publicly imported
  `coherenceEtaleCompositor`, read with their full signatures and normalization.
* `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor`.
* `Sheaf.SecSmoothPurity.ReductionDirectImage`:
  `reductionDirectImage_isIso`, and its imported
  `reductionDirectImageComparison` / `reductionCompactSupport`.
* `Sheaf.SecSmoothPurity.ReductionExceptional`: `reductionExceptional_isIso`,
  `reductionCtfCompactSupport`, `reductionCtfScalar`, `reductionSite`,
  `reductionSiteCompactSupportIso`, `reductionCompactSupportFixedIso`.
* Mathlib proof leaves: `CategoryTheory.Adjunction.comp` with
  `comp_counit_app` in `Mathlib.CategoryTheory.Adjunction.Basic`, and
  `Adjunction.rightAdjointUniq` with its counit compatibility in
  `Mathlib.CategoryTheory.Adjunction.Unique`.

Edge cases checked: empty schemes; zero complexes and zero coefficient rings
(the n=0 annihilator permits them); d=0 or e=0; identity f or g; identity φ;
nonflat quotient coefficient maps and maps of infinite projective dimension.
No expression requires a nonempty scheme or a nonzero ring, any inverse is an
inverse of a supplied canonical isomorphism, and all coefficient operations are
derived. Ring and site universes are the existing intrinsic Type u coefficient
and Scheme.{u} interfaces with fixed-coordinate coefficients ULift.{u+1,u} R;
no equality of the small site's object and morphism universes is imposed.

Searches (2026-10-24):

* msearch.py leanfinder: "Counit transpose of coefficient change for composite
  adjunction and uniqueness of right adjoint compositor" — 8 hits, including
  rightAdjointUniq_hom_app_counit and transitivity. They supply uniqueness but
  not the explicit composite coefficient transpose and final b/alpha equation.
* msearch.py loogle: "CategoryTheory.Adjunction.comp,
  CategoryTheory.Adjunction.rightAdjointUniq" — 0 hits.
* msearch.py leansearch: "Coefficient comparison counit transpose for composite
  adjunctions" — 8 hits, principally comp_counit and comp_counit_app; not the
  full result.
* msearch.py grep: "rightAdjointUniq|comp_counit_app" in
  CategoryTheory/Adjunction — 9 hits; read Basic.lean and Unique.lean.
* rg of the same names and finite-adjoint/compositor names in
  lean/WeilConjectures and lean/Sheaf — many generic mates and proper/open
  specializations, including IntegrationTransposeComposition.rightMate;
  none has all three coefficient comparisons and this transpose formula.
* grep -rn for the item id in lean/WeilConjectures — no match.

No new DAG notion, dependency repair, statement correction or disputed statement.
The helpers only package and compose interfaces for this node's existing data.

## Second reading by Q74

Author's second reading (the dispatcher requires no other agents; independent
mathematical review is the maintainer's). Reopened the node and final file and
checked each displayed formula, including the inverse direction of all b maps.
The composite counit has Fg outside epsilon_f; the normalization has alpha before
epsilon_h, and theta goes Hh to Hg ⋙ Hf. The inverse Hom equivalence, rather than
its forward direction, expresses the transpose of D. Its inverse b_f comes first,
then inverse b_g; the final coefficient identity has chCoeff before thetaB.
All three b-normalization equations retain the canonical comparisons. The alpha
normalization retains the proper/open site comparisons and the actual etale
compositor on each etale witness. The first compile exposed a missing
bounded-below/ambient compatibility; the helper now inserts the existing
compatibility isomorphism explicitly. No mathematical hypothesis or clause was
changed to resolve that type mismatch. Separate uniqueness conditions at A and
B are included, and both composite-counit formulas are retained. No copied
constructibility, scalar extension, Tor predicate or site category was introduced.
