## Worker report

The module `Sheaf.Paper.PurityZeroSupportRetractionTriangle` states
`WeilConjectures.PurityFiniteSetting.zero_support_retraction_triangle` with `sorry`.
Its other declarations construct its actual objects, comparison maps and proposition;
there are no additional postponed theorems. The natural-language statement, proof,
source, and dependency lists of the node are unchanged. No dependency repair or new
node is needed.

Source read: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md`, first paragraph, through the
triangle obtained by applying Rp_*. The assigned node deliberately uses the ordinary
supported-kernel right derived functor, as its text stipulates, and does not identify
that functor with the transported exceptional functor used later in the blueprint.

Hypotheses and objects:

- The binder `P : PurityFiniteSetting.{u}` retains the fixed finite-field datum,
  different coefficient prime, finite coefficient extension, uniformizer construction,
  positive level, and quotient ring. `P.Ring` is precisely O_E/(varpi_E^n), and
  `P.Coefficient` is its published ULift for coefficients on the small site. The
  fields `P.level_pos`, `P.coefficients.different`, and the finite-extension instance
  carry the standing hypotheses; none is replaced by an extra assumption.
- `h : P.ramificationIndex ∣ P.level` is e|n. The setting's `kummerLevel` is n/e.
- `Y`, `a : Y ⟶ Spec (.of P.field.k)`, and the three instances `IsSeparated a`,
  `LocallyOfFiniteType a`, `QuasiCompact a` say separated finite type over the fixed k.
- `Line Y`, `lineProjection Y`, `zeroSection Y`, `Punctured Y`, `openImmersion Y`
  and `puncturedProjection Y` are the recorded affine-line datum, not replacements.
  In particular the punctured projection is definitionally j followed by p.
- `ZeroSupportSheaves P T` abbreviates ordinary `Sheaf (Scheme.ProEt.topology T)`
  valued in `ModuleCat.{u+1} P.Coefficient`. This is the native constant-coefficient
  presentation already used by the recorded twist, support and localization
  dependencies. No constructibility or Tor restriction is imposed. The coefficient
  module node's intrinsic realization is not a new definition of these sheaves.
- `zeroSupportInput` is `DerivedCategory.Plus.singleFunctor ... 0` applied to
  `P.twist h (Line Y)`. Its underlying object is F=A_X(1)[0]. `zeroSupportValueFunctor`
  is exactly `(finiteClosedUpperShriek ...).rightDerivedFunctorPlus` followed by
  the full inclusion, so its value at this input is B0=Rs!_0 F.
- `zeroSupportMiddleFunctor.obj` at this input is P=Rp_*F. `zeroSupportQ` is exactly
  Q=Rpi_* A_U(1)[0].

Conclusion clauses:

- The first conjunct is `Finite P.Ring`. Finiteness of its standard size lift is
  constructed by `zeroSupportFinite` from `Padic.finite_coefficientExtensionRing`.
- `IsNoetherian Y`, `IsNoetherian (Line Y)`, `IsNoetherian (Punctured Y)` assert all
  three Noetherian conclusions. Mathlib's scheme predicate includes quasi-compactness
  and local Noetherianity. The two pairs `LocallyOfFiniteType (...) ∧ QuasiCompact (...)`
  say that X and U are finite type over k.
- The existential proof `hq : QuasiCompact (openImmersion Y)` is a conclusion, not
  a new hypothesis. The accompanying `hPair` identifies the actual ranges as a
  complementary pair; it is a proof needed to instantiate the published support
  localization construction, not an arbitrary geometric replacement.
- `zeroSupportClosedExact` is the existing closed-exact theorem specialized to this
  pair. It supplies the exactness instance inside the proposition definition.
  `ZeroSupportRetractionTriangle` asserts the natural isomorphism between the
  termwise `mapDerivedCategory` and the ordinary right derived functor. Its next
  two conjuncts are natural isomorphisms of functors for every integer shift and
  every integer cohomology degree. Thus they cover every complex L and q, rather
  than just the degree-zero input.
- `zeroSupportAdjunction` selects the localization theorem's adjunction with its
  specified injective-model counit normalization. This is not a choice from a
  bare existence of an arbitrary right adjoint. `zeroSupportLocalTriangle` has
  exactly that counit as first arrow and the derived open unit as second arrow.
- The local boundary `d` is a natural transformation on the entire bounded-below
  input category. The existential `I,hI,hq,eB,eL` in the proposition fixes its
  value at the displayed input by an isomorphism from the dependency's actual
  signed support cone, with all three components equal to its published model
  comparisons. This records the canonical boundary, not just an unspecified
  completion of two arrows to a triangle.
- `zeroSupportCollapse` is Rp_*s_* -> R(ps)_* -> id. Its actual factors are the
  exact/right-derived comparison, the inverse of `finiteDirectImageComposition`,
  the congruence for `AffineSpace.zeroSection_comp_over`, the derived identity
  comparison, and `mapDerivedCategoryIdIso`. `zeroSupportAlpha` evaluates it at B0.
- `zeroSupportBeta` uses bounded/unbounded right-derived compatibility, the
  inverse compositor for j followed by p, and coefficient restriction. The latter
  is an isomorphism `c` whose forward map is constrained to be exactly
  `zeroSupportOpenCoefficient`: the derived single comparison, the site comparison,
  and the recorded root-tensor map `P.twistEtalePullback h j`.
- `zeroSupportTriangle` is B0 -> P -> Q -> B0[1]. Its first map is alpha inverse
  followed by Rp_* of the support counit. Its second map is Rp_* of the open unit
  followed by the inverse composition comparison and the specified coefficient
  restriction. Its third map is beta inverse, Rp_*(d), the specified Rp_* shift
  comparison, and alpha shifted by one.
- The proposition asserts that both the original and final triangles are
  distinguished. It also supplies an isomorphism from `Rp_*.mapTriangle` of the
  original to the final triangle, fixing its components as alpha, identity, beta.
  Thus it expressly identifies the image triangle, including its boundary.
- Naturality uses natural transformations for the counit, unit, retraction
  comparison and local boundary; the other comparisons are natural isomorphisms
  of functors. The coefficient identification is fixed by the published root
  pullback and site-comparison maps. No transported exceptional identification
  occurs in any conclusion or in any support-value definition.

Recorded statement dependencies used (signatures and docstrings read):

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Ring`, `Coefficient`,
  `ramificationIndex`, `kummerLevel`, `twist`, `derivedSheaf`.
- `Sheaf.Paper.PurityAffineLineDatum`: the six geometric objects/maps above and
  `twistEtalePullback` with its unique root-tensor characterization.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`
  and its intrinsic module-sheaf realization; the other dependencies already use
  the native `ModuleCat`-valued presentation.
- `Sheaf.Paper.SfDerivedDirectImage`: finite ordinary total right-derived direct
  image; this item uses only that finite part, not its integral tower.
- `Sheaf.AlgebraicGeometry.ProEtalePairFlasque`: the existing
  `finiteClosedUpperShriek` and supported-kernel construction.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated`,
  `distTriang`; the derived categories carry the usual triangulated structures.
- `Sheaf.AlgebraicGeometry.SupportLocalizationTriangle`:
  `supportLocalizationTriangle`, `supportClosedDerivedPlus`,
  `supportFirstModelComparison`, `supportThirdModelComparison`.
- `Sheaf.Paper.FiniteDirectImageComposition`: `finiteDirectImageComposition`,
  on all ordinary unbounded finite-coefficient derived objects.

All recorded proof-dependency modules that exist are also imported. The old
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion` path is
superseded by the finite-coefficient module exposed by SupportLocalizationTriangle;
importing the retired duplicate would mix two copies of the star functors.
`Functor.mapDerivedCategory` and its exact-functor shift structure are used through
Mathlib and the upstream exact-functor interface. The other proof-only imports are
FiniteKummerLevel, AffineLineSupportGeometry, ExactFunctorDerivedFunctor,
ProEtaleRingedClosedKernelAdjoint, RingedSiteKInjectiveResolutionsOfUniverses,
ProEtaleModuleDirectImageLeftExact and RightDerivedFunctor.Triangulated.

Edge cases checked: Y may be empty or disconnected. No dimension, nonemptiness,
connectedness or integral-domain assumption was introduced. The level is positive
by P, while N is the existing quotient n/e under h; no equality of site object and
morphism universes is imposed. The coefficient type is the standard u+1 lift,
with sites of objects in u+1 and morphisms in u. Shifts and cohomology cover all
integers, including zero and negative degrees. The original triangle is unrotated,
and comparison to the signed cone prevents a boundary-sign change. No assertion
about a general non-quasi-compact complement is used.

Searches actually performed:

- `msearch.py leanfinder`: "For the zero section of the affine line the support
  localization triangle pushes forward along the projection to the support adjoint,
  affine line direct image and punctured line direct image". Eight hits, concerning
  affine localization and Proj; no matching pro-etale retraction triangle.
- `msearch.py leansearch`: "Applying a derived direct image to a support localization
  triangle along an affine line projection". Eight hits, concerning affine scheme
  localization and stalk maps; no matching statement.
- `msearch.py loogle`: `CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.Triangle`.
  Zero hits, with diagnostic unknown identifier `CategoryTheory.Triangle`.
- `msearch.py grep`: `supportLocalization|retractionTriangle|zeroSupport`, restricted
  to Mathlib CategoryTheory. Zero hits.
- `rg` in `lean/WeilConjectures`: `supportLocalization|zeroSupportRetraction|`
  `zero_support_retraction|retractedSupport`; found the ordinary etale support-cone
  modules, which do not state this pro-etale affine-line result. A literal node-id
  search there found no declaration.
- `rg` in `lean/Sheaf`: `zeroSupportRetraction|zero_support_retraction|zeroSupportTriangle`
  found no pre-existing declaration. Broader reads found RetractedSupportLocalizationComparison,
  PurityGysinStructure and PurityKummerTriangleConcentration. These concern transported
  exceptional values or concentration of a supplied triangle, rather than this
  ordinary supported-kernel triangle. Their reusable constructions were inspected;
  the item is not re-recorded as an existing theorem.

No STATEMENT-DISPUTED issue and no statement correction. Validation uses only scompile.py
and the prescribed deliver2.py checks; the live repository was read only.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
