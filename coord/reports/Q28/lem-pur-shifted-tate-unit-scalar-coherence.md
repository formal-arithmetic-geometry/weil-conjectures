## Worker report

The module `Sheaf.Paper.PurShiftedTateUnitScalarCoherence` states
`WeilConjectures.PurityFiniteSetting.shiftedTateUnitScalarCoherence`. Its proof alone is
`sorry`. All seven supporting definitions have actual data and source/blueprint docstrings.
The natural-language proof follows all seven steps of the node. The node's statement,
proof, proof_deps, source, status and other existing fields are unchanged.

Hypotheses and objects, clause by clause:

- `P : PurityFiniteSetting.{u}` is the recorded purity convention datum. `P.field`
  carries p,a,q,k_0,k; `P.coefficients.l` is prime by its recorded instance and
  `P.coefficients.different` is ell != p. Its finite extension and positive finite level
  are the fixed convention choices, not extra hypotheses on E or F.
- `E F : Type u` with Field, Algebra (Padic P.coefficients.l), and FiniteDimensional
  instances are finite coefficient extensions. `ι : E →ₐ[Padic P.coefficients.l] F`
  is the coefficient inclusion (a field algebra map is injective). The valuation rings,
  uniformizers, quotient rings and completed ring inclusions are the published constructions.
- E_0 is `ULift.{u} (Padic P.coefficients.l)`, with its standard algebra equivalence
  `ULift.algEquiv` to Q_ell. `PurShiftedTate.baseInclusion` is the canonical algebra map
  composed with this equivalence. The direct E_0 to F inclusion is the composite with ι,
  hence is the canonical Q_ell inclusion; it is not an additional extension parameter.
- `S : Scheme.{u}` with `S.Over (Spec (.of P.field.k))` is the k-scheme.
  Named instances `hft : LocallyOfFiniteType`, `hqc : QuasiCompact`, and
  `hsep : IsSeparated` on its structure morphism express separated finite type. The
  theorem explicitly includes all three section instances via `include hft hqc hsep in`.
  `d : ℕ` is exactly the nonnegative integer in the node, cast to integers for shifts.
- No invertibility hypothesis is added. `P.shiftedTateResidueInverse S` maps the recorded
  `P.coefficientPrime_isUnit_stalk` through the local-ring residue map and obtains the
  required inverse. This includes all points and is valid on the empty scheme.
- The site is the actual `S.ProEt`, with object universe u+1 and morphism universe u.
  Its module universe is u+1; the completed sheaf is
  `completedIntegralCoefficientSheafUnrestricted`, not the discrete constant integer ring.
  All objects can be placed in a common arbitrary universe u. The lift of Q_ell ensures
  that its original universe 0 does not restrict this u.
- U_H is the existing `integralConstantCoefficientObject ... H S`, the regular completed
  coefficient sheaf placed in degree zero. No second coefficient unit is defined.
  `P.shiftedTateUnit H S d` only abbreviates its recorded twist
  `sfIntegralTwistingFunctor ... (d : ℤ)` followed by the standard shift `2 * (d : ℤ)`.
- A, B, D are respectively `completedDerivedScalarExtension` along baseInclusion,
  ι, and their composite. These are ordinary derived change of completed rings.
  Their identification with the strict tower is the exact `completedScalarComparison` chi.
- Alpha is `(CompletedLineTensor.associatorData ...).derived`, fixed uniquely by its
  `IsAssociatorNormalized` pure-tensor formula and K-flat universal-counit equation.
  Thus no arbitrary natural isomorphism or tower-coherence assumption is an input.
- `PurShiftedTate.unitIso` is `asIso chi` on the complete regular unit followed by the
  canonical `constantCoefficientIntegralScalarIso`. The latter is the inverse strict
  Roos unit with quotient coordinates 1 tensor pi_n and zero shifted coordinate, after
  its universal resolving comparison. Composing with chi cancels this inverse unit,
  giving ordinary coefficient multiplication x tensor b maps to iota(x)b. This uses
  the exact existing normalizations, rather than an existential unnormalized isomorphism.
- `PurShiftedTate.shiftIso` selects the ordinary coherent shift structure from the
  published `completedScalarComparison_commutesWithShift`. Its
  `completedScalarShiftOrdinaryNormalization` fixes every component by termwise
  `mapCochainComplexShiftIso` and the invertible K-flat counit, which determines the
  structure. The whole theorem retains the chain normalization and commutation with chi.
- Beta is exactly the named `integralTwistOrdinaryBeta`, evaluated at
  `constantWeilIntegralObject`, whose underlying object is U_H and whose proof of
  membership is the published constant-coefficient theorem.
- `P.shiftedTateScalarIso ... d` is q, defined by the shift comparison followed by
  `(shiftFunctor _ (2*d)).mapIso` of beta followed by the twist of unitIso. `≪≫`
  means first left then right, so this is precisely `(u(d) ∘ beta)[2d] ∘ s`.
- `P.shiftedTateUnitDomain H S d` packages four assertions, without extra conditions:
  finiteTorConstructibleIntegral of U_H; of T_H; Tor [0,0] for every derived reduction
  of U_H; Tor [-2d,-2d] for every derived reduction of T_H. Its reduction index n ranges
  over all naturals and denotes positive exponent n+1. The theorem asserts this exactly
  at E_0, E, F (not at additional coefficient stages). The finite-Tor predicate includes
  sfIntegralConstructible, hence completeness, constructibility and uniform boundedness.
- The next conjunct is precisely finiteTorConstructibleIntegral of A(T_0) over E.
- The next conjunct is `alpha.hom.app U_0 ≫ u_F.hom = B.map u_E.hom ≫ v.hom`.
- The final conjunct is `alpha.hom.app T_0 ≫ theta_F.hom = B.map theta_E.hom ≫ a.hom`.
  These have exactly the order and endpoints of the two displayed equations in the node.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its recorded field/coefficient
  data, `coefficientPrime_isUnit_stalk`; this imports the existing finite-field datum.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its CoefficientExtension
  import: the recorded Padic valuation/quotient constructions and positive-level finiteness.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the unchanged completed
  coefficient sheaf and independent site/coefficient universe interface.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: `sfIntegralTwistingFunctor`,
  using the recorded `integralSheafTwist` and completed signed line.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`;
  ordinary extension and universal K-flat computation are retained by the scalar witness.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`,
  `integralScalarExtensionComparisonOfUniverses`, used by chi and the normalized unit.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: `completedDerivedScalarExtension`,
  `completedScalarComparison`, `finiteFreeCompletedScalarComparison`, coefficient maps.
- `Sheaf.Paper.IntegralTwistDerivedScalarCanonical`: `integralTwistOrdinaryBeta`;
  its imported theorem pins the pure-tensor and counit normalization.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, its full subcategory.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleIntegral`, reexported from
  FiniteTorAmplitude, and its actual positive-level Tor-amplitude predicate.
- `Sheaf.Paper.ConstantCoefficientScalarNormalization`: `constantCoefficientIntegralScalarIso`;
  reexports `integralConstantCoefficientObject`, `integralConstantCoefficient_constructible`,
  `constantWeilIntegralObject` and the exact strict-unit coordinate normalization.
- `Sheaf.Paper.CompletedScalarShift`: `completedScalarComparison_commutesWithShift`,
  with `completedScalarShiftOrdinaryNormalization` from the same module.
- `Sheaf.Paper.CompletedLineTensorCoherence`: `CompletedLineTensor.associatorData`,
  `.derived`, `IsAssociatorNormalized`, and `associatorData_existsUnique`.
- Proof imports preserve `TwistPreservesFiniteness`, `IntegralCtfTriangulated`,
  `CompletedScalarChainShift`, `KFlatIndependentCoefficients`, `IntegralTwistBaseChange`.
  The modules of every recorded statement and proof dependency are directly imported.

The three already-landed interface nodes for the constant object normalization, canonical
shift and ordinary associator are added to stmt_deps, as authorized by brief-stage2 §5.
Their statement/proof dependency closures do not reach this item (checked by traversing
both edge types in the DAG). No new independent notion or dependency repair is needed.

The existing downstream `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` was also read.
Its UnitMultiplication is an interface supplied as a parameter and its theorem concerns
traces; neither proves this node. Importing that consumer here would make this prerequisite
depend on its consumer. This module instead assembles q from the upstream normalized maps.
The constructors for the displayed shifted object and q are source formulas; they do not
introduce another tensor, twist, coefficient category, site, scalar functor or unit notion.

Edge cases checked before writing and again after compilation:

- d=0 uses the canonical zero twist and zero shift, without assuming either strictly equal.
- E=E_0, F=E and all identity inclusions are permitted: no strictness/degree inequality,
  ramification bound, or nonidentity hypothesis occurs. Q_ell's lift is an equivalence.
- The empty scheme and zero objects satisfy the containing Tor intervals. No nonvanishing
  or equality with a singleton cohomological support is claimed.
- Arbitrarily ramified finite inclusions are included. No quotient coefficient flatness is
  assumed; computations are derived tensor products of the correct completed ring sheaves.
- The sign convention is cochain shift: degree zero moves to -2d. The comparison respects
  the shifted differential, so no extra sign is inserted in either tower equation.

Searches actually run:

- msearch leanfinder: `Canonical multiplication on derived coefficient units and shifted
  Tate twist scalar extension comparisons commute in a tower of finite l adic fields`.
  Eight results, including cyclotomicCharacter declarations, a cotangent comparison,
  Hilbert 90 and Fontaine theta; none states this result.
- msearch loogle: `ModuleCat.extendScalarsComp`. Eleven results about ordinary module
  scalar associativity, its unit/associativity laws and the module-category pseudofunctor;
  none includes completed pro-etale units, Tate twists or the uniform Tor clauses.
- msearch grep: `shiftedTate|[Uu]nit.*[Ss]calar.*[Cc]oher|[Ss]calar.*[Uu]nit.*[Cc]oher`.
  Zero Mathlib hits.
- msearch leansearch: `The canonical coefficient-unit multiplication and shifted Tate twist
  comparisons commute with a tower of finite l adic scalar extensions`. Eight results
  about scalar towers and Hom-complex shift/smul; none is this statement.
- rg over both lean/WeilConjectures and lean/Sheaf for shiftedTate, unit/scalar comparisons,
  scalar associators and canonical shifts found the interfaces used above and the downstream
  trace consumer. No declaration has both tower equations and all membership/Tor clauses.
- grep for the exact node id in lean/WeilConjectures found no declaration.
- rg for `shiftedTateUnitScalarCoherence|namespace PurShiftedTate|def shiftedTateUnitDomain`
  found no collisions in either published source tree before this delivery.

Validation: scompile.py compiled the final module in its isolated sandbox and under its
library module name with no errors or warnings. No local/global build was run. No source
statement fault or STATEMENT-DISPUTED issue was found. The only writes are in this sandbox;
the required delivery wrappers perform their authorized bookkeeping themselves.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
