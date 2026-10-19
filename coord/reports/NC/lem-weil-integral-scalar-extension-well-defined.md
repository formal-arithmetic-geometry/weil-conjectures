## Worker report

The delivery states `WeilConjectures.integralScalarExtensionWellDefined` in
`Sheaf.Paper.IntegralScalarExtensionWellDefined`. All theorem proofs are `sorry`;
definitions contain actual constructions. No statement correction is made.

The earlier WAITING report is superseded. The canonical ambient scalar action is
now supplied in this item's module as a helper construction, as authorized by the
human's missing-helper instruction. It does not need the constructible subcategory
or the characteristic-dependent theorem `lem-weil-integral-constructible-linear`.
The construction specifies constant sections by every finite residue, their
multiplication natural transformation on complexes by its sectionwise formula,
and its derived natural transformation by the fully faithful localization API.
Thus the final equality uses the canonical action, without arbitrary linearity
structures as hypotheses. The helpers are part of the scalar-extension notion
being stated, and are listed individually in `lean.declarations`.

Hypotheses and setup, clause by clause:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extensions are fields `E`, `L`
  with `[Algebra ℚ_[l] E]`, `[Algebra ℚ_[l] L]` and the two finite-dimensional
  instances. The given inclusion is `ι : E →ₐ[ℚ_[l]] L`; an algebra homomorphism
  of fields is injective, so this presents precisely the subfield inclusion.
  The finite-field global datum and `l ≠ p` are not imposed by this node.
- `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionIdeal` and
  `coefficientExtensionRing` are the recorded coefficient constructions.
  `integralScalar_absoluteValue` states equality of the restricted absolute
  values. `integralScalar_integer_mem` and the actual `RingHom.codRestrict`
  construction `integralScalarIntegerInclusion` restrict the given inclusion.
  `integralScalar_quotient_kernel` states the required uniformizer-power
  containment in the exact form that defines a map of quotient rings.
  `integralScalarQuotientMap` is `Ideal.Quotient.lift` of the inclusion, not an
  unspecified map, and `integralScalarQuotientMap_transition` states its
  compatibility with both coefficient transitions.
- `Y : AlgebraicGeometry.Scheme.{t}` uses the small site `Y.ProEt`, topology
  `Scheme.ProEt.topology Y`. Its object size remains `t+1` and its morphism
  size remains `t`. Coefficients and modules have size `max u (t+1)`;
  `ULift.{t+1}` only enlarges coefficient types to that common size.
- Every index `n : ℕ` means the paper's positive index `m=n+1`; no zero-level
  quotient is inadvertently substituted for the first level.
- `integralCoefficientCommRingSheaf` is the recorded constant sheaf. Its
  functoriality is used literally in `integralScalarQuotientSheafMap`.
  `completedIntegralCommRingSheafUnrestricted` and
  `completedIntegralCommRingProjectionUnrestricted` are the actual limit and
  its projections. `integralScalarRho` is their composite with the preceding
  constant sheaf map, as in the node.
- `integralScalarReductionWitness` specializes the recorded canonical ordinary
  change-of-rings functor witness to that `rho`. It fixes objects to
  `SheafOfModules.changeOfRings rho M` and maps to the corresponding recorded
  `changeOfRingsHom` (with the witness's object equalities). Consequently its
  selected `integralScalarReduction` is determined, including its maps;
  it is not a choice from a bare existence assertion. `integralScalarFiniteComplex`
  applies it termwise. `integralScalarLevel` then uses the recorded restriction
  `integralOperationsRestrict` along the target completion projection.
- `integralScalarTensorSection` transports the sheafification of the actual
  sectionwise tensor `s ⊗ x` through that object equality. The unique transition
  theorem specifies the formula `s ⊗ x ↦ red(s) ⊗ x` in every degree and on
  every site object. Its proof plan explains the compatibility of `rho` and
  limit projections. Thus `integralScalarTransition` is canonically fixed,
  `integralScalarTowerFunctor` includes the strict transition maps and chain
  maps, and `integralScalarComplexFunctor` composes that tower with the existing
  `integralOperationsRoosFunctor`: termwise products, `1-s`, shifted mapping
  cone, and the diagonal map on its two summands.

The three conclusions:

1. `integralOperationsGoodComplex` is exactly `IsKFlat` for the completed
   commutative coefficient sheaf together with `∀ i, IsFlatOnSite (P.X i)`.
   The first conjunct quantifies over any two such complexes, any chain map
   `f`, and `QuasiIso f`; it asserts `QuasiIso` of every
   `integralScalarFiniteComplex.map f` and of `integralScalarComplexFunctor.map f`.
   No flatness of any coefficient quotient is assumed.
2. The existential functor has domain and codomain
   `DerivedCategory (integralTowerModules l E Y)` and its L analogue, precisely
   modules over the completed coefficient sheaves. `e` is a natural isomorphism
   on *all* K-flat flat-term representatives, with their actual maps.
   `F.Additive` and `Nonempty (F.CommShift ℤ)` state additivity and shift
   compatibility. For any other functor with its representative comparison `e'`,
   `∃! α : F ≅ F'` with `isoWhiskerLeft ... α ≪≫ e' = e` is exactly the
   qualified uniqueness in the node. It asserts no unqualified uniqueness of
   natural isomorphisms or of maps completing Roos triangles.
   For every model `P` and isomorphism `Q(P) ≅ K`, the next clause gives the
   isomorphism of `F(K)` with the explicit complex value and the recorded
   `integralOperationsDerivedLimitProperty` of its exact strict tower. This is
   literally `CategoryTheory.IsDerivedLimit`, with localized transitions and
   a distinguished Roos triangle. Choosing resolutions objectwise and
   transporting maps through `F(q)⁻¹` and `e_P` gives the chosen-value functor
   described by the node; the proof docstring spells this out and does not
   assume that arbitrary derived morphisms have chain-map lifts.
3. `integralScalarFiniteConstant` is the constant sheafification section
   represented by `a mod ϖ^(n+1)`. The unique section in
   `integralScalarConstant_existsUnique` has exactly these projections, hence
   is the constant section of the completed coefficient sheaf.
   `integralScalarChainAction` is multiplication by it in every degree.
   `integralScalarDerivedAction` is its uniquely descended endomorphism of
   the identity via `Localization.fullyFaithfulWhiskeringLeft.preimage`.
   Thus `action(a).app K ≫ f` is exactly `a f` for the constant-section action
   induced on the derived category (the action of the general derived-linearity
   dependency). The last conjunct is exactly
   `F.map (a f) = ι(a) F.map f`, with the target action using
   `integralScalarIntegerInclusion`. Naturality of these identity endomorphisms
   also gives the identical right-composition description of scalar action.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` imports the Padic
  coefficient constructions listed above; its finiteness declaration is
  `Padic.finite_coefficientExtensionRing`.
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`:
  `spectralNorm_unique_field_norm_ext`, `spectralNorm_extends`,
  `spectralMulAlgNorm`, `isNonarchimedean_spectralNorm` (via the coefficient
  module); these give the absolute-value identification in the proof plan.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, presenting the site
  and the constant coefficient category. The completed coefficient case uses
  the separately recorded completed sheaf, rather than discrete constants.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Paper.CompletedIntegralCoefficients`:
  `integralCoefficientSheaf`, `integralCoefficientCommRingSheaf`,
  `integralCoefficientSheafTransition`, `integralCoefficientSheafSystem`,
  `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted`,
  `completedIntegralCommRingProjectionUnrestricted`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses` and its
  imported `TensorProduct`: `changeOfRings`, `changeOfRingsHom`,
  `changeOfRingsPresheaf`, `siteSheafTensorRight` (in the flatness predicate).
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`;
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit`, `CategoryTheory.IsDerivedLimitTriangle`.
- `Mathlib.Algebra.Homology.DerivedCategory.Linear`:
  `DerivedCategory.instLinear`, `instLinearCochainComplexIntQ`,
  `instLinearShiftFunctorInt`. The intrinsic scalar endomorphisms specify
  the same constant-section action without introducing arbitrary instances.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.Paper.IntegralOperationsWellDefined`: `integralOperationsGoodComplex`,
  `integralOperationsGoodLocalization`, `integralOperationsRestrict`,
  `integralOperationsRoosFunctor`, `integralOperationsDerivedLimitProperty`;
  `Sheaf.Paper.IntegralReductionTowerUnrestricted`: `integralTowerModules`.
  The owning landed nodes of these additional reused interfaces are added to
  `stmt_deps`; a traversal of statement and proof edges found no dependency
  path from them back to this item.
- Proof imports retain `ChangeOfRingsKFlatQuasiIso`, `SiteDerivedTensorDescent`,
  and `DerivedLimitExistence`; localization descent/uniqueness uses
  `Mathlib.CategoryTheory.Localization.Predicate`, and the Roos triangle
  isomorphism criterion is the recorded Mathlib pretriangulated theorem.

Edge cases checked before drafting:

- `E=L` and identity inclusion: the same-index coefficient maps become identity,
  and the construction is the usual reduction/completion tower. It is not
  claimed to be the identity on non-complete objects.
- Ramified inclusions: only containment of uniformizer powers is used;
  same-index quotient maps need not be injective or flat. No cofinal-index
  substitution or unjustified exactness of ordinary extension is used.
- The empty scheme, zero complexes and zero morphisms: all constructions use
  the category of sheaves and its actual limits, so these remain meaningful.
  Neither sections nor the site are assumed nonempty.
- Unbounded complexes are allowed. There is no boundedness, constructibility,
  derived-completeness, Noetherian, or characteristic restriction.
- Arbitrary site and coefficient sizes retain the small site's unequal object
  and morphism universes; K-flatness and flatness refer to the recorded predicates.
- Scalar `0` and `1` reduce to zero and identity multiplication at every level.
  Their completed sections are fixed uniquely by the same residues, and the
  derived action is fixed by fully faithful precomposition with localization.

Searches and source checks:

- `msearch.py leanfinder`, query “Completed integral scalar extension on derived
  sheaves using K-flat resolutions and Roos homotopy limits”: returned Tor and
  presheaf differential declarations, no completed scalar-extension theorem.
- `msearch.py loogle`, query “SheafOfModules.restrictScalars, DerivedCategory.Q,
  Functor.Linear”: returned no hits because `Functor.Linear` was an unknown Loogle identifier. Query `CochainComplex.mappingCocone` returned the
  ordinary cone API, which the reused Roos helper already uses.
- `msearch.py leansearch`, query “Completed derived tensor product independent
  of K flat resolution”: unavailable with Internal Server Error (recorded in `searches.jsonl`).
- `msearch.py grep`, query `integralScalar|completedScalar|constant.*Linear`
  under `Algebra`: only unrelated constant-linear-map hits. Query
  `constant.*section|scalar.*action` under `CategoryTheory/Linear`: no hits.
- `rg` in Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no declaration for this item or its
  completed scalar-extension theorem. The upstream blueprint-id search had
  no hit. Existing integral operations/Roos and coefficient constructions
  were read in full and reused.
- `LisseAdicSheaves.lisseIntegerInclusion` was inspected: it fixes both fields
  in successor universe `u+1` in the lisse/etale setup. The helper here is the
  direct codomain restriction of the given field homomorphism for arbitrary
  coefficient universe `u`; its only postponed input is preservation of the
  recorded integer-subring membership. It does not redefine either integer
  ring or any lisse-sheaf notion.
- The source paper was opened at
  https://arxiv.org/pdf/1309.1198, Definition 3.4.10 (printed p. 22),
  Proposition 3.5.1(3) (p. 24), and Proposition 6.8.14(1) (p. 61).
  Completion is the derived inverse limit, and the scalar-extension functors
  in the coefficient colimit are used there without this explicit construction.
  The eight-step proof supplied in the node is included in the theorem docstring.

No mathematical statement fault or disputed assertion was found.

Validation: the two-file packet compiled via `scompile.py` with no errors or
warnings. Every individual file is compiled separately by that wrapper; no
library/global build is requested. The required `deliver2.py --no-push` printed OK for commit `ba4e529d79`:
the packet compiles and passes preflight except for the independent second reading,
which the second reader supplies. Nothing was pushed. This worker does not deliver
and does not write an independent second reading.

## Dependency modules

`def-pc-kflat-complex`: the initial prescribed compile failed in
`IntegralReductionTower` because the published compiled K-flat artifact had
specialized the coefficient size to the site size; the recorded source already
has the required independent sizes. The delivery supplies that current KFlat
source as a sibling overlay, with only two added module-documentation lines
explaining the scalar-extension consumer. All definitions, signatures, theorem
proof plans and mathematical inputs are unchanged. The copied node changes only
`lean`, with `lean.note` recording the artifact mismatch and the repair. This
keeps the coefficient/module size `max u (t+1)`, site object size `t+1`, and
morphism size `t`; it introduces no universe equality.

## Second reading by NC

Independent reading on 2026-10-16. I opened the item node, both delivered modules,
the dependency nodes and the source declarations used below. No mathematical or
Lean-signature mismatch was found. This reading adds this report section; the
Lean constructions, signatures and node records remain as the first worker wrote
them. There is no statement correction and no new definition node.

Source check: I read Bhatt--Scholze, [Definition 3.4.10, Proposition 3.5.1,
Definition 3.5.2, Lemma 6.8.2 and Proposition 6.8.14](https://arxiv.org/pdf/1309.1198),
including the surrounding setup. Section 3.4 assumes a replete topos and a locally
finitely generated ideal; Section 3.5 uses a constant Noetherian ring. Here the
coefficient rings are valuation rings of finite local-field extensions, and the
pro-etale product theorem supplies the required exactness. Proposition 6.8.14 is
about constructible categories; this node explicitly supplies the more general
ambient construction used before restricting to them. Its well-definedness does
not require constructibility or a topologically Noetherian scheme. I also read
the actual Stacks `sites-cohomology.tex` blocks `definition-K-flat`,
`lemma-K-flat-resolution`, `lemma-derived-tor-quasi-isomorphism-other-side`, and
`derived.tex` block `definition-derived-limit` from the official source. These are
[06YN](https://stacks.math.columbia.edu/tag/06YN),
[06YS](https://stacks.math.columbia.edu/tag/06YS),
[06YT](https://stacks.math.columbia.edu/tag/06YT), and
[08TC](https://stacks.math.columbia.edu/tag/08TC). The first three concern arbitrary
ringed sites and unbounded complexes; 08TC requires the displayed product and
Roos triangle. They impose no characteristic or scheme finiteness hypothesis.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Prime and finite coefficient fields: `(l : ℕ) [Fact l.Prime]`, the two
   `[Field]`, `[Algebra ℚ_[l]]`, `[FiniteDimensional ℚ_[l]]` instances, and
   `ι : E →ₐ[ℚ_[l]] L`. A homomorphism of fields is injective and identifies E
   with its image subfield containing the specified base field. Verdict: exact;
   no separate finite-field datum or condition on the characteristic of Y.
2. Absolute values, integer rings, uniformizers and quotients: the actual
   `Padic.coefficientExtension*` declarations in `CoefficientExtension.lean`
   use the spectral absolute value, its valuation subring and the chosen
   uniformizer ideal. `integralScalar_absoluteValue` identifies restriction;
   `integralScalar_integer_mem` justifies the actual `RingHom.codRestrict`
   inclusion. `integralScalar_quotient_kernel` is exactly the same-exponent
   ideal containment needed for `Ideal.Quotient.lift` in
   `integralScalarQuotientMap`. `integralScalarQuotientMap_transition` states
   the commuting reduction square. Verdict: exact, including ramified inclusions;
   no injectivity or flatness of the quotient map is asserted.
3. Scheme, site and constant sheaves: `(Y : Scheme.{t})`, `Y.ProEt` and
   `Scheme.ProEt.topology Y` are the recorded small pro-etale site. The
   constant coefficient sheaves are the recorded functorial `constantSheaf`
   construction, with `ULift` of the coefficient rings. Verdict: exact; no
   replacement by the small etale site or discrete integral coefficients.
4. Completion, projections, modules and derived categories: I read
   `CompletedIntegralCoefficients.lean` and `IntegralReductionTowerUnrestricted.lean`.
   `completedIntegralCoefficientSheafUnrestricted` is literally the limit of
   `integralCoefficientSheafSystem`; its commutative enhancement forgets to the
   same ring sheaf. `completedIntegralCommRingProjectionUnrestricted` is its
   actual coordinate projection. `integralTowerModules` is its module-sheaf
   category, with standard derived localization. Verdict: exact; the unrestricted
   interfaces remove irrelevant auxiliary data without changing the limit.
5. The coefficient map rho: `integralScalarQuotientSheafMap` is constant
   sheafification applied to the quotient inclusion, and `integralScalarRho`
   is the source projection followed by that map. Compatibility with the next
   level follows from the quotient square and the limit cone identities, and
   is used in the transition theorem. Verdict: the specified canonical map.
6. Finite change of rings: I read the complete signature of
   `derivedChangeOfRingsIndependentCoefficients`. Its ordinary witness fixes
   both objects to `changeOfRings rho M` and maps to `changeOfRingsHom`, with
   equality transports. `integralScalarReductionWitness` specializes that
   declaration; `integralScalarReduction` selects that determined functor,
   `integralScalarFiniteComplex` applies it termwise, and `integralScalarLevel`
   restricts through the target completion projection. Verdict: precisely
   the node's tensor and restriction, rather than an arbitrary functor.
7. Tower transitions: `integralScalarTensorSection` is the image of the
   sectionwise pure tensor under sheafification and the witness equality.
   `integralScalarTransition_existsUnique` fixes every natural chain map by
   `s ⊗ x ↦ red(s) ⊗ x` in every degree and on every object. Its chosen
   transition and `Functor.ofOpSequence` therefore fix the actual strict
   tower and its action on chain maps. Verdict: exact; uniqueness is justified
   by local generation under sheafification, not by an arbitrary choice.
8. Roos construction: I opened `integralOperationsRoos`, `integralOperationsRoosMap`
   and `integralOperationsRoosFunctor`. These use `mappingCocone` of
   `towerTransitionEndomorphism`, termwise products and the diagonal product
   map on both cone summands. `integralScalarComplexFunctor` composes the
   actual tower with that functor. Verdict: the specified Cone(1-s)[-1].
9. K-flatness and flat terms: `integralOperationsGoodComplex` is the conjunction
   of the recorded `CochainComplex.IsKFlat` and `∀ i, IsFlatOnSite (P.X i)`.
   The latter is exactness of the sheafified tensor functor, not sectionwise
   flatness. Verdict: exactly the node's good representatives.
10. Conclusion (1): the initial universal quantifiers range over two such
    representatives and any chain map; `QuasiIso f` implies both every
    finite-level `QuasiIso` and the Roos `QuasiIso`. Verdict: both assertions,
    with the same quantifier order and no flatness hypothesis on the quotients.
11. Conclusion (2), functor and comparisons: `∃ F e` has the specified completed
    source and target derived categories; `e` compares its restriction to all
    good complexes with the explicit localized Roos functor, naturally on maps.
    `F.Additive` and `Nonempty (F.CommShift ℤ)` give the two stated properties.
    `∃! α : F ≅ F'` is qualified by
    `isoWhiskerLeft ... α ≪≫ e' = e`. Verdict: precisely uniqueness compatible
    with representative comparisons, not uniqueness of arbitrary isomorphisms.
12. Conclusion (2), values and derived limits: for every good model P and
    isomorphism `Q(P) ≅ K`, the statement gives `F(K) ≅ Q(T(P))` and
    `integralOperationsDerivedLimitProperty` of the strict scalar tower.
    I read that predicate and the live source of `CategoryTheory.IsDerivedLimit`
    using `scompile.py --source`: the predicate uses the localized transitions
    and a distinguished Roos triangle. Verdict: the node's derived limit.
    Transport along the displayed model isomorphisms gives the chosen-resolution
    value and action on morphisms. No chain-map lift of every derived morphism
    is assumed. The eight-step proof docstring explicitly supplies this transport.
13. Conclusion (3), canonical action: `integralScalarFiniteConstant` is the
    sheafified residue of a; `integralScalarConstant_existsUnique` fixes the
    completed section by all its projections. `integralScalarChainAction_existsUnique`
    fixes multiplication by it in every degree. `integralScalarDerivedAction`
    uses the fully faithful precomposition-with-Q API, whose signature I read
    in Mathlib, to descend that actual natural transformation. The linearity
    equality is `F.map (action(a).app K ≫ f) = action(ι(a)).app (F.obj K) ≫ F.map f`.
    Verdict: precisely the constant-global-section action on Hom groups;
    Mathlib's derived-linear localization gives the same action. No unspecified
    linear structure or scalar map is an extra hypothesis.

Dependency-module review: `def-pc-kflat-complex` is the only delivered dependency
node. I read its statement, source and both K-flat definitions. `IsKFlat` quantifies
over every acyclic module-sheaf complex and asks for acyclicity of its total tensor;
`IsKFlatResolution` is `QuasiIso f ∧ IsKFlat K`. Both match 06YN/06YS. Its independent
object, morphism and coefficient universes are retained, using the recorded
relative-smallness infrastructure. A textual comparison with the current shared
source shows only the worker's two explanatory module-documentation lines were
added. The delivered node changes only `lean`, with the required artifact-mismatch
note; it introduces no stronger hypothesis, replacement tensor or definition.

Edge cases: `n = 0` is exponent one everywhere; no positive level is omitted.
The tower has the fixed nonempty countable index set of the node, so there is no
additional arbitrary-index nonemptiness hypothesis. Zero complexes, zero maps and
the empty scheme are admitted by the sheaf and limit constructions. Scalar zero
and one are fixed by their residues and multiplication formulas. The case E=L
and the identity inclusion is included; no erroneous assertion that completion
is identity on all complexes is added. Ramification uses only ideal containment.
Complexes are unbounded, and Y has arbitrary characteristic. The site object
universe is t+1, its morphism universe t, and the coefficient/module universe is
max u (t+1), with no equality imposed. The common universe u for E and L covers
the node's subfield inclusion in one ambient field; it does not bound their size.
All variables and universes are bound explicitly, with `autoImplicit false`.

Independent searches: I ran `msearch.py leanfinder` with “Completion of change
of coefficients for unbounded complexes of sheaves on a pro-etale site”: eight
hits about cochain induction, factorization and ordinary local cohomology, none
for this theorem. `msearch.py leansearch` with “Derived completion after extending
the coefficient ring of sheaves using a K flat resolution” returned the service's
Internal Server Error. `msearch.py loogle` with quoted scalar/DerivedCategory
terms reported a query parse error, so I do not count it as a negative search.
The successful LeanFinder search supplies the required semantic search alongside
the recorded earlier searches. `msearch.py grep` for completion/changeOfCoefficients/
scalarExtension gave ordinary completion hits. Direct `rg` searches of Mathlib,
upstream WeilConjectures and project Sheaf with completed-scalar and
coefficient-extension variants found ingredients and lisse specializations, not
this ambient completed derived scalar-extension statement. I opened
`lisseIntegerInclusion_exists` and `lisseIntegerInclusion`: they use fields in
successor universe u+1 in the lisse setup and do not supply the arbitrary-u
interface here. The delivered helper is the direct restriction of the given
inclusion and introduces no second integer-ring notion.

H5/H6/H8/H9 checks: all postponed proofs are named theorems, with proof plans and
the owning blueprint id. Choices used by definitions are fixed by object/map
equalities or uniqueness, and all other data are concrete constructions.
Every delivered theorem proof remains `sorry`. The main theorem docstring carries
all eight proof steps. There are no private notions, file-local notation, unbound
variables or overlong lines. Both recorded `lean.statement` fields match their
source signatures after whitespace normalization, as required by preflight.

Validation: the two delivered files compiled separately through the prescribed
`scompile.py` packet, with no errors or warnings. The wrapper also compiled the
four needed side dependencies separately; each file stayed below 60 seconds.
