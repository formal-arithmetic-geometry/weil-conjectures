## Worker report

Item: lem-sfb-integral-quotient-projection-comparison. Group: N5. Stage 2 only.
The module is `Sheaf.Paper.IntegralQuotientProjectionComparison`, namespace
`AlgebraicGeometry.ProEtale.IntegralQuotient`.

The primary theorem states the displayed equality of the actual two projection
morphisms in the ordinary unbounded quotient-coefficient derived category. Its proof
is `sorry`. The auxiliary theorem `scalarTensorIso_existsUnique` states the existence
and unique representative normalization of the canonical comparison b already
specified in the item's statement; its proof is also `sorry`. Both theorems have
source references and complete proof plans. All definitions contain actual data.
The `scalarTensorIso` definition selects from an existence-and-uniqueness theorem
that determines the entire natural isomorphism, not from bare existence of a map.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  The existing `integral l E`, `finite l E n`, and `reduction l E n` use the
  recorded valuation ring, its recorded uniformizer, and its actual quotient map.
- Positive exponents are indexed by `n : ℕ` with actual exponent `n + 1`, precisely
  the convention of IntegralQuotientCoefficients and the direct-image dependency.
  Thus index 0 is the source's n=1, and every positive exponent occurs.
- `R_T` is `condensedRingObj (integral l E) T`, i.e. the pulled-back continuous
  condensed ring of integers. The integral-limit dependency identifies this with
  the completed inverse limit. No coefficient sheaf is replaced by a new one.
- `S_T` is `condensedRingObj (finite l E n) T`, where the finite quotient has its
  discrete topology; this is the constant finite quotient, as in the dependency.
- `DerivedCategory (Modules (integral l E) T)` and its finite counterpart are the
  ordinary unbounded derived categories of the existing internal module categories.
  The tensor notation is their existing relative K-flat derived tensor. There is
  no completion or bounded-subcategory predicate.
- `D (reduction l E n) T` is the existing derived extension of scalars. It retains
  the target quotient action and is not replaced by an endofunctor after restriction.
- `{X Y : Scheme.{u}} (f : X ⟶ Y)` allows every scheme morphism, without a base
  field or finite-type, proper, quasi-compact, or separated restriction.
- `L`, `F`, and `adj` are exactly the dependency's named derived pullback, direct
  image, and specified adjunction. The argument `c` has type
  `D_Y ⋙ L_S ≅ L_R ⋙ D_X`, so its forward component is the source's lambda.
  `_hc : PullNormalized (reduction l E n) f c` fixes it to precisely the dependency's
  scalar/pullback comparison. This is a parameterization of the specified canonical
  map, not a hypothesis that an arbitrary map is compatible: the dependency supplies
  such a c for every f and positive level, and the representative normalization fixes
  its components. The conclusion holds for every such normalized c.
- `rho (reduction l E n) f c` is used verbatim. It is the dependency's adjunction
  mate, with the actual counits. The theorem does not assume or cancel its inverse.
- `actualTensorPull` is the existing `CondensedRing.leftDerivedUpperStarTensor`
  with L unfolded in its expected type. `actualProjection` is the actual
  `rightAdjointProjectionMap` of `adj` and that tensor comparison. Unfolding these
  names returns exactly `CondensedRing.moduleObjectProjectionMap` before component
  evaluation. The adjunction, counit, and tensor map are all the recorded ones.
  These are typed accessors for the same data, not new projection choices.
- `ScalarTensorIso l E n T` is an isomorphism of curried bifunctors, with source
  `D_T(U ⊗ V)` and target `D_T U ⊗ D_T V`. `scalarTensorTotal` is the signed total
  of the EXISTING scalar-unit normalized ordinary tensorator. In right-scalar
  notation its formula is `(u ⊗ v) ⊗ s ↦ (u ⊗ 1) ⊗ (v ⊗ s)`; moving s to the
  other factor gives the library's left-scalar convention by S-balancing, without
  permuting u and v or introducing a Koszul sign.
- `ScalarTensorNormalized` composes b at the localizations of P,Q with the two
  canonical scalar computation maps and the localization's lax tensor map. The
  result is required to equal D of the localization tensor map, followed by the
  scalar computation map of the total tensor and localization of scalarTensorTotal.
  On flat-term K-flat representatives these are invertible computation maps, so
  this is exactly the specified representative normalization. The all-complex
  equation is its universal derived-counit form, not an exactness assumption.
- `scalarTensorIso_existsUnique` states the b existence and uniqueness implicit in
  calling b canonical. `scalarTensorIso` names that uniquely determined object.
  These helpers belong to the b clause of the item and are all in lean.declarations.
- K and M have precisely the two unbounded integral-module object types stated.
  The left side is b_Y, then `rho_K ⊗ₘ 𝟙`, then the actual quotient projection.
  Lean's `≫` follows composition from left to right, reversing the display's `∘`.
- The right side is D_Y of the actual integral projection, then rho at
  `K ⊗ (L_R f).obj M`, then F_S of b_X followed by
  `𝟙 ⊗ₘ c.inv.app M`. The inverse therefore appears only on lambda, as specified.
- Both sides have source `D_Y(F_R K ⊗ M)` and target
  `F_S(D_X K ⊗ L_S(D_Y M))`. These are actual arrows in D_S(Y), not equalities
  only after forgetting the quotient action or passing to cohomology.
- Naturality in both inputs is retained: b is an isomorphism of bifunctors, c and
  rho are natural transformations, actualProjection is the recorded
  projection bifunctor transformation, and the equality quantifies over all K,M.
- No hypothesis of properness, completeness, boundedness, constructibility,
  exactness of scalar extension, or invertibility of a projection appears.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its imported CoefficientExtension gives
  the integers, uniformizer, quotient ideal and quotient ring constructions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `condensedPullbackHom` and
  `coefficientPullbackIso` in `AlgebraicGeometry.ProEtale`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`:
  `AlgebraicGeometry.ProEtale.sfb_integral_coefficient_limit`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward` and `moduleObjectDerivedPullback`;
  the imported derived upper/lower-star module supplies their derived adjunction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and `.Tensor`:
  existing `CondensedRing.derivedHom`, `derivedTensor` and localization tensor maps.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` is the recorded general
  section-module change-of-rings interface, imported through the coefficient module;
  the actual internal extension is the dependency's `QuotientChange.D`.
- `Sheaf.Paper.IntegralQuotientDirectImageComparison`:
  `integral_quotient_direct_image_comparison`; its public coefficient and scalar
  modules give `integral`, `finite`, `reduction`, `Modules`, `D`, `L`, `F`, `adj`,
  `PullNormalized`, `rho`, `compute`, and `extension`.
- `Sheaf.Paper.ModuleObjectProjectionMap`:
  `CondensedRing.moduleObjectProjectionMap` is the actual map on both sides.
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`:
  `AlgebraicGeometry.Scheme.proEtaleProjectionFormulaMate` is the recorded section
  presentation; the theorem uses its internal-module counterpart as the node requests.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.
  ringedTopoiCanonicalDerivedTensorPullback` supplies the general comparison used
  in the existence/uniqueness proof plan, with distinct site object/Hom universes.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
  The standard framework uses site objects at u+1, arrows at u, and coefficients
  at u+1. No equality between site object and arrow universes is introduced.
- Added existing statement dependency `def-sfb-internal-scalar-tensor-comparison`:
  `Sheaf.Paper.InternalScalarTensorComparison` supplies
  `CondensedRing.internalScalarMonoidal`. Only the ordinary uniquely normalized
  structure is used, defined BEFORE that module's exact-extension assumption.
  Its exact-only derived scalar comparison is deliberately not specialized to the
  nonflat quotient. No dependency record or definition is changed.
- Proof-dependency modules for internal/section tensor and derived pushpull/tensor
  normalization and ringed derived monoidal comparisons are imported as proof-only
  imports, as stage 2 requires. The coefficient morphism dependency is already
  publicly available through the canonical module-object framework.

Edge cases checked before drafting and on rereading: f the identity (the mate and
balancing reduce to identity constraints); K=0 and M=0; empty X or Y (no nonemptiness
assumption); the first quotient (Lean index 0); E=Q_l and the nonflat map Z_l→F_l;
unbounded K,M; l=2 (no division by 2 or characteristic exclusion); arbitrary scheme
morphisms and universes permitted by the published internal framework. In particular
nonflat reduction exposes why the exact-only pre-existing derived scalar comparison
cannot be used. Tensor factors are never swapped, so odd degrees add no extra sign.
No node statement correction and no STATEMENT-DISPUTED finding.

Searches made with the prescribed wrapper and local read-only source searches:

1. leanfinder: "Scalar extension of the actual derived projection formula map
   commutes with the quotient coefficient direct image comparison". Eight results
   about cotangent modules, regular sequences, and scalar algebra maps; no match.
2. loogle: `"rightAdjointProjectionMap"`. Zero Mathlib hits. The upstream project
   does define the generic one-adjunction map, used by the existing actual projection
   definition; it does not state the quotient-coefficient two-adjunction equality.
3. grep via msearch, CategoryTheory:
   `projectionFormula|projection_formula|rightAdjointProjectionMap|map_μ_comp_counit_app_tensor`.
   Four hits, in Mathlib's Monoidal/NaturalTransformation and Monoidal/Functor,
   including `Adjunction.map_μ_comp_counit_app_tensor`; no specified quotient square.
4. leansearch: "Reduction modulo a uniformizer of the unbounded derived projection
   formula map is compatible with the canonical scalar extension direct image mate".
   Eight hits about module reduction, adic-completion transitions, localization and
   ModuleCat scalar adjunctions; no match.
5. `rg` of project WeilConjectures and Sheaf for scalar tensor/extension monoidality,
   `PullNormalized`, `TensorNormalized`, projection maps, and the item id. Found the
   existing exact-scalar CoefficientProjectionSquare and InternalScalarTensorComparison,
   the direct-image dependency, and ordinary normalized scalar monoidal structure.
   CoefficientProjectionSquare imposes exact scalar extension and geometric hypotheses,
   so it is not the present unbounded quotient statement. No existing declaration
   states this node's equality. A direct item-id search in WeilConjectures had no hit.
6. DAG concept search found `def-sfb-internal-scalar-tensor-comparison`, which was
   read and reused for its ordinary comparison. No new definition node is needed:
   the auxiliary declarations expose the canonical b and actual projection notation
   explicitly specified by this item, under the missing-helper authorization.

Validation: every compile uses the prescribed scompile.py server wrapper. Compilation diagnosed opaque F/L interface mismatches and expensive kernel
checking after specialization to concrete coefficients. The final source exposes
the existing tensor comparison and projection as whole natural transformations.
`ProjectionComparisonEquation` writes the full equality with general coefficient
parameters; the main theorem specializes that definition to the actual reduction
and the uniquely normalized b maps. This is a definition of the displayed equation,
not a proposition supplied as a hypothesis. Tensor maps in one input are written
using derivedTensor.map / .obj.map, exactly rho tensor identity and identity tensor
lambda inverse. Both sandbox and library module compilation passed cleanly, in
36.1 and 33.2 seconds respectively. The original 60-second cap is unchanged. No local build,
shared source edit, Git mutation, or launcher-script change was performed.

## Second reading by N5

A separate full rereading of the node and final Lean source was performed in this
worker, without another agent (the dispatcher's explicit no-agent instruction).
The maintainer's review remains the independent review; this does not claim a second
person read the delivery.

The rereading checked each term of the displayed equation and its intermediate
objects. On the left, b has inputs F_R K,M, rho changes only the first factor, and
pi_S receives D_X K,D_Y M. On the right pi_R lands in F_R(K tensor L_R M), rho is
therefore evaluated at that tensor, and the final map uses lambda inverse, with
source D_X L_R M and target L_S D_Y M. Both endpoints retain the S_Y action.

The main subtlety is that `PullNormalized` fixes the supplied lambda to the exact
comparison of the dependency, whose theorem guarantees existence. There is no
arbitrary compatible comparison hypothesis. The scalar b is supplied by a unique
universal normalization theorem, so selecting it introduces no unspecified data.
I rechecked that `internalScalarMonoidal` needs no exactness hypothesis; only the
later derived interface of its owning module does. The exponent n+1 includes the
first positive quotient and every further quotient. All nine new declarations
carry this item's source and blueprint identifier, and both postponed theorems
have full proof plans. The whole-transformation accessors unfold only the named functors and return the
existing tensor comparison and its actual adjunction projection. The named equation
expands to exactly the two composites checked above, retaining the inverse on lambda
and the S_Y-linear category. This avoids repeated specialization in kernel checking.
No mathematical mismatch or missing source hypothesis was found.

The final rereading additionally opened `ProjectionComparisonEquation` and checked its
full body: bY at F_R K,M; the first-variable derived tensor map of rho; pi_S; D_Y(pi_R);
rho at the integral tensor with L_R M; and F_S of bX followed by the second-variable
tensor map of c.inv. No map was replaced by an arbitrary variable in the theorem: a
is the actual reduction, bX/bY are scalarTensorIso, and c is PullNormalized. The general
equation definition has parameters only to share the same mathematical expression
before specializing to the given coefficient ring. The main theorem is thus exactly
the displayed source claim after unfolding the equation.
