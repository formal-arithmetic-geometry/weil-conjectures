## Worker report

The delivery states `def-weil-constant-weil-structure` in
`Sheaf.Paper.ConstantWeilStructure`. Every definition has real data. All postponed
proofs are named theorems with source, owning blueprint tag and a natural-language
proof. No theorem is proved in this stage. The item's natural statement and its
statement dependencies are unchanged. Two direct dependency interfaces are repaired
under §1(B), as detailed below; no new DAG notion is introduced.

Hypotheses and conventions:

- `D : FiniteFieldDatum.{u}` retains p, a, q=p^a, the field of q elements,
  its chosen algebraic closure and its inclusion.
- `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` retain the coefficient prime condition.
  `Padic l` is Q_l; the coefficient valuation, integers, uniformizer and all quotient
  rings and reductions are precisely the recorded `Padic.coefficientExtension*` data.
- `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]` describe the finite coefficient extension.
  At common stages E is the recorded `Coefficient.{u} l Ω L`, with its canonical
  algebra equivalence to the actual intermediate field L in Ω. Thus no equality of
  scheme and closure universes is assumed. The rational construction itself does not
  depend on which embedding in Ω is used; it is available for every finite E.
- `Y₀ : Over (Spec (.of D.k₀))`, `[LocallyOfFiniteType Y₀.hom]` and
  `[QuasiCompact Y₀.hom]` are exactly a finite-type k₀-scheme, without separatedness.
  `D.geometricFiber Y₀` is the recorded base change, and
  `(D.geometricFrobenius Y₀).hom` is the recorded geometric-Frobenius isomorphism.
- `sfWeilPrimeInvertible` is a defined inverse to l in each residue field, obtained
  from the named theorem `D.geometricFiber_coefficientPrimeInvertible`, which proves
  it is a unit from these hypotheses. No prime-invertibility assumption is added.
- `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`,
  `[IsAlgClosure (Padic l) Ω]` allow any fixed algebraic closure independently of u.
  The arbitrary u used for E and the scheme is a common ambient universe; finite
  coefficient stages have canonical small models in every such universe.

Clause-by-clause rendering:

1. At positive exponent n+1, `constantWeilFiniteComparison` is exactly
   `proEtaleIsoConstantRingComparison g` on the lifted quotient coefficient ring.
   Its hom is the recorded `proEtaleConstantInverseImageMap`, adjoint to the
   constant-section map, rather than an arbitrary equivalence. ULift only changes size.
   `constantWeilCoefficientReduction` is constant sheafification of the actual quotient
   transition, conjugated through ULift.ringEquiv.
   `constantWeilFiniteComparison_reduction` states exactly
   c_(n+1) followed by r_n = inverse-image(r_n) followed by c_n, in Lean composition
   order. The comparisons are bundled isomorphisms; exponent one is included by n=0.
2. `constantWeilIntegralComparison` reuses
   `isomorphismCompletedCoefficientComparison`. Its uniqueness specification says
   c_O followed by every finite projection is inverse-image(projection) followed by
   c_n. These jointly monic equations specify exactly the composite in the node:
   the limit comparison followed by the limit of the c_n. Its source and target are
   the actual completed commutative-ring sheaves, whose underlying ring sheaf is
   `limit (integralCoefficientSheafSystem ...)`. Both constituent arrows are
   invertible by `proEtaleIso_inverseLimitComparison` and the finite comparisons.
3. `constantWeilIntegralComplex` is the regular completed module in degree zero;
   its localization is the already recorded `integralConstantCoefficientObject`.
   `constantWeilIntegralObject` merely wraps that actual object in the current full
   constructible subcategory using the existing membership theorem.
   The regular complex is K-flat with flat terms (`constantWeilIntegralComplex_good`).
   The canonical strict map `constantWeilChainUnit` into the recorded pullback Roos
   complex is chosen only from a uniqueness theorem: its finite-level image of one is
   the actual module pullback adjunction unit of the actual reduction unit 1 tensor 1,
   and its shifted component is zero. On a scheme isomorphism these equations determine
   the map on every site object; no arbitrary lift to a homotopy limit is used.
   `constantWeilChainUnit_isIso` states invertibility after localization.
   `constantWeilIntegralRoosComparison` uses the recorded
   `integralDerivedPullbackComparison` on this good representative and inverts that unit.
   `constantWeilTermwiseUnitMap` is Mathlib's actual pullback-of-unit map on the small
   site model, transported back and with scalars restricted along c_O inverse.
   `constantWeilRestrictionUnitMap` is the actual ring-map unit, defined by its global
   section one through Mathlib unitHomEquiv; their ratio is
   `constantWeilTermwiseUnitIso`, namely c_O on regular modules. The exact functor's
   single comparison gives `constantWeilDerivedCoefficientComparison`.
   `constantWeilIntegralLambda` is the derived-to-termwise comparison normalized by
   those same strict unit equations. Finally `constantWeilIntegralTheta` is explicitly
   lambda followed by the derived c_O, exactly c_O composed with lambda in the node.
   This normalization refines the existing termwise-comparison dependency's bare
   `Nonempty` comparison; it never selects an unspecified natural isomorphism.
   `constantWeilConstructibleIntegralTheta` lifts this iso through the full inclusion.
4. `constantWeilRationalObject` is precisely the recorded raw rationalization of the
   completed integral object. `constantWeilRationalTheta` is the image of the integral
   iso under that functor (tensor one on Hom), with the source identified by the recorded
   rational pullback's integral-object formula. `constantWeilRationalComplex` is the
   fixed pair (E_Y,theta_E). `constantWeilRationalObject_mem_heart` supplies the degree-zero
   heart condition, and `constantWeilRationalSheaf` wraps the same pair in the full Weil
   sheaf subcategory. `constantWeilRationalForget` states For of the pair is E_Y.
5. `constantWeilAlgebraicallyClosedComplex` applies the actual stage-inclusion
   construction to the rational constant pair at `Padic.finiteCoefficientBase l Ω`.
   This is the least field Q_l in Ω, using the recorded Shrink coefficient model.
   The structure iso is the class of theta_Q_l, its inverse the class of its inverse;
   the inclusion already carries the normalized self-transition associators.
   `constantWeilAlgebraicallyClosedObject_mem_heart` gives heart membership and
   `constantWeilAlgebraicallyClosedSheaf` is the requested canonical Weil sheaf.
   `constantWeilAlgebraicallyClosedForget` explicitly states that For is the literal
   pair (Q_l,(Q_l)_Y), with no independence-of-stage assertion added to this definition.

Dependency declarations read and used (including reexports):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `.geometricFiber`.
- Mathlib: `Padic`, `PadicInt`, `IsAlgClosure` and `AlgebraicClosure`; the arbitrary
  closure is represented by IsAlgClosure, rather than fixed to the canonical model.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public import
  `CoefficientExtension`: `Padic.coefficientExtensionRing`, `.coefficientExtensionTransition`,
  `.coefficientExtensionIntegers`, `.coefficientExtensionUniformizer`, and the positive-level
  finiteness theorem. Scheme-morphism-properties is a convention node; its finite-type
  notions are Mathlib `LocallyOfFiniteType` and `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`, via its inverse-image public
  imports: `proEtaleSheafInverseImage`, `proEtaleModuleInverseImage`,
  `proEtaleModelRingUnit`, `proEtaleModuleFromModel`, and the canonical finite pullback.
- `Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage`:
  `proEtaleIsoConstantRingComparison`, `proEtaleIso_constantComparison`,
  `proEtaleIso_inverseLimitComparison` and its equivalence theorem.
- `Sheaf.Paper.CompletedIntegralCoefficientGerm` and `CompletedIntegralCoefficients`:
  `integralCoefficientCommRingSheaf`, `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted`, their actual quotient projections.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Limits.limit`, its projections/comparison.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full category.
- `Sheaf.Paper.ConstantCoefficientObjectsConstructible`:
  `integralConstantCoefficientObject`, `integralConstantCoefficient_constructible`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `commonStageDerivedPullback`, and their actual object formulas.
- `Sheaf.Paper.IsomorphismDerivedPullback` (read with `scompile.py --source` before the
  concurrent shared checkout refresh): `isomorphismCompletedCoefficientComparison`,
  `isomorphismTermwiseModuleInverseImage`, `isomorphismIntegralTermwiseInverseImage`,
  `isomorphismIntegralDerivedPullback_termwise`. The latter states preservation and natural
  comparison on the full integral constructible subcategory. Its coefficient object exists
  but its comparison has no normalization; the construction here supplies that normalization.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`; no Karoubi envelope is introduced.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the actual intrinsic category,
  `GeneralAlgebraicallyClosedCoefficients.inclusion`, literal stages and representative maps.
  `AlgebraicallyClosedCoefficients.Coefficient` and `Padic.finiteCoefficientBase` retain the
  exact small finite-field model and least stage.
- The two repaired dependency modules below supply the heart and fixed-pair interfaces.
  Their imported original modules and full signatures/docstrings were read before repair.
- Mathlib `SheafOfModules.pullbackObjUnitToUnit`, `unitHomEquiv`, and
  `Functor.mapDerivedCategorySingleFunctor` provide the canonical termwise module map
  and its degree-zero derived identification. The existing upstream
  `CategoryTheory.Endofunctor.IsoAlgebra`, `.mk`, `.forget`, `.carrier`, `.str` implement
  the fixed-pair notion without a private copy.

Edge cases checked before and while writing:

- n=0 denotes exponent one, never an omitted level or the zero quotient at exponent zero.
- The empty scheme is permitted. All constructions and joint-projection uniqueness hold
  there, and no nonemptiness or choice of a geometric point is assumed.
- For g=id, the finite and integral maps preserve one and all coefficients; the strict
  Roos unit is the normalized completeness unit. Thus its inverse is canonical, not an
  arbitrary scalar automorphism. The construction works for general scheme isomorphisms
  before specialization to geometric Frobenius.
- A nonzero scalar rescaling fails the finite generator normalization. The uniqueness
  theorem therefore determines the object up to the exact equality used downstream.
- No restriction to separated, smooth, proper or nonempty Y₀ was introduced.
- The least coefficient field is included and Ω may have an unrelated universe.
- Fixed pairs and the derived category of Weil sheaves differ already at Spec k₀:
  a Jordan-block extension produces Ext^1 of Weil sheaves but no such ambient geometric
  Hom to a shift. The supplied dependency repair uses the former category exactly as
  the current natural-language dependency explicitly requires.

Searches for an existing declaration:

- `msearch.py leanfinder "canonical Weil structure on the constant coefficient sheaf
  geometric Frobenius"`: eight Witt-vector/isocrystal results, no match.
- `msearch.py leanfinder "canonical Weil structure on constant sheaf"`: eight results,
  including Mathlib constantSheaf and SheafOfModules.unit; neither constructs the Weil data.
- `msearch.py loogle "CategoryTheory.constantSheaf, CategoryTheory.Functor.mapIso"`:
  zero hits (both attempts).
- `msearch.py grep "constant.*[Ww]eil|[Ww]eil.*[Cc]onstant"` and
  `"constantWeil|ConstantWeil|constant_weil"`: zero Mathlib hits.
- `rg` and the specified node-id search in the upstream WeilConjectures tree and
  project Sheaf tree found no constant-Weil construction. The upstream WeilSheaf.Category
  file was inspected fully around its definitions and design: its derived-of-pairs
  category cannot be used for the dependency's fixed-pair derived-category statement.
- Searches of project Lean for IsoAlgebra/fixed-pair constructions found PbcWeilCategory,
  but its PBC coefficient categories, separatedness hypothesis and Frobenius pullback are
  not the present arbitrary finite-type intrinsic constructible categories. The underlying
  existing IsoAlgebra construction is reused directly here.
- Direct searches for all proposed constantWeil, sfRationalHeartProperty, sfWeilComplex,
  and sfCommonStageHeartProperty names found no declaration in either existing tree.

No mathematical statement is disputed, and no statement correction is required.
All three delivered files compile separately through scompile.py with the supplied
sibling overlay, with no errors or warnings. Each passed both its sandbox and named-module
check. The final deliver2.py check uses --no-push; delivery and the independent second
reading remain with the second reader.

## Dependency modules

`def-weil-constructible-heart`: `Sheaf.Paper.SfConstructibleHeart` imports the original
ConstructibleHeart module unchanged. Its old rational/common-stage heart interfaces use
the legacy integral subcategory, whereas current recorded rationalization and derived
pullback use sfIntegralConstructibleCategory and the general common-stage category.
The new interface gives exactly the same cohomological standard classes and full hearts
on those current categories, together with bounded standard t-structures, both truncation
criteria and abelianity. Its standard-t-structure assertions retain the finite-field,
prime-distinctness and finite-type geometric hypotheses by explicit included binders.
The dependency node changes only its lean record, with a note; its statement is unchanged.

`def-weil-weil-sheaf-complex`: `Sheaf.Paper.SfWeilSheafComplex` replaces the unusable
recorded binding to upstream WeilComplex with the node's expressly stated fixed-pair
category. It specializes the existing IsoAlgebra construction to the recorded rational
and common-stage pullbacks, supplies the faithful forgetful functors and full subcategories
on heart carriers, and constructs every finite-stage pair with its normalized representative
structure map. It uses the exact geometric-fibre and Frobenius declarations, with coefficient
prime invertibility obtained from the finite-field datum. The dependency node changes only
its lean record, with a note; no natural statement is changed.

## Second reading by ND

I opened the item node, its Stacks/blueprint source place, all three Lean files, and
the two dependency node copies. The item fixes the finite-field datum
`D : FiniteFieldDatum`, a prime `l` with `[Fact l.Prime]` and `hl : l ≠ D.p`, an
algebraically closed coefficient field `Ω`, and a finite coefficient extension `E`
with its field, `Padic l`-algebra, and finite-dimensional hypotheses. The scheme is
`Y₀ : Over (Spec (.of D.k₀))` with `[LocallyOfFiniteType Y₀.hom]` and
`[QuasiCompact Y₀.hom]`; `D.geometricFiber Y₀` is `Y`, and
`(D.geometricFrobenius Y₀).hom` is `g_Y`. No separatedness, smoothness, properness,
nonemptiness, or universe equality is assumed.

The five conclusion clauses render as follows, with no mismatch found.

1. The finite coefficient rings and their transitions are
   `Padic.coefficientExtensionRing` and `Padic.coefficientExtensionTransition`.
   `constantWeilFiniteComparison` is the canonical
   `proEtaleIsoConstantRingComparison` (its hom is the structure map from constant
   sections), `constantWeilCoefficientReduction` is the actual constant-sheaf
   reduction, and `constantWeilFiniteComparison_reduction` gives the required
   compatibility for every `n : ℕ`; the `n + 1` indexing includes exponent one.
2. `constantWeilIntegralComparison` is the completed inverse-limit comparison
   `isomorphismCompletedCoefficientComparison`, whose projection equations are those
   of the node. `constantWeilIntegralComplex` is the completed regular module in
   degree zero, and `constantWeilIntegralObject` is its current intrinsic
   constructible object.
3. `constantWeilIntegralComplex_good`, `constantWeilChainUnit_existsUnique`,
   `constantWeilChainUnit`, and `constantWeilChainUnit_isIso` supply the specified
   K-flat representative, normalized finite-level unit, and its localized
   quasi-isomorphism. `constantWeilIntegralRoosComparison`,
   `constantWeilTermwiseUnitMap`, `constantWeilRestrictionUnitMap`,
   `constantWeilTermwiseUnitIso`, `constantWeilDerivedCoefficientComparison`,
   `constantWeilIntegralLambda`, and `constantWeilIntegralTheta` render the
   derived pullback identification and the composite `c_{\mathcal O_E} \circ λ`.
   `constantWeilConstructibleIntegralTheta` lifts it to the full constructible
   category.
4. `constantWeilRationalObject` is the raw rationalization,
   `constantWeilRationalTheta` is the image of the integral comparison,
   `constantWeilRationalComplex` is the fixed pair, and
   `constantWeilRationalObject_mem_heart` and `constantWeilRationalSheaf` give the
   constructible-heart object and sheaf. `constantWeilRationalForget` is the exact
   underlying rational object.
5. `constantWeilAlgebraicallyClosedComplex` applies the literal least stage
   `Padic.finiteCoefficientBase l Ω`; the heart theorem and
   `constantWeilAlgebraicallyClosedSheaf` give the requested common-stage sheaf, and
   `constantWeilAlgebraicallyClosedForget` identifies its carrier with that stage and
   the rational constant object.

Edge cases were checked independently: `n = 0` is the exponent-one stage; the empty
scheme and empty site make all section and projection conditions vacuous; the zero
object is not excluded by any definition; `g_Y = 𝟙` preserves the unit and all
transitions; no characteristic case beyond `l ≠ D.p` is added; and the coefficient
closure universe `Ω : Type v` is independent of the scheme/coefficient universe.
The finite-stage index has a least stage, so the algebraically closed construction
does not require a nonempty-choice hypothesis.

For the duplicate-definition check I ran `msearch.py` LeanFinder for “canonical Weil
structure constant coefficient sheaf geometric Frobenius” and “constant Weil sheaf
Q_l” (only Witt-vector/constant-sheaf results), `msearch.py` Loogle for the
`IsoAlgebra`/constant-sheaf pattern (no result), and `rg` over Mathlib, the upstream
`WeilConjectures`, and the repository `lean/Sheaf`. The upstream source does contain
`AlgebraicGeometry.WeilSheaf.adicConstant` in `WeilSheaf/Constant.lean`; I opened it.
That declaration is a Qbar-l adic sheaf on the older `AdicSheaf`/derived-of-Weil-sheaves
category, with no finite `E` level, completed integral tower, rationalized intrinsic
category, or fixed-pair statement required here. It therefore does not say this node's
statement exactly, so the item module is required rather than recorded as existing.
The upstream `WeilComplex` declaration was likewise read and is the incompatible
Ext-valued derived-of-pairs notion; the dependency module records this §1(B) repair.

I found no Lean/node mismatch and changed no declaration or node statement. The only
delivery changes are the reviewed item/dependency `lean` records and this independent
reading; the dependency modules retain their node statements and add only the required
interfaces. All three modules compile cleanly through `scompile.py` with no errors or
warnings, and every declaration has its source and owning blueprint tag in the docstring
required for this stage.
