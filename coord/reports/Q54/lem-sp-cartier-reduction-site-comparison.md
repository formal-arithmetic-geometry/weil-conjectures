## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison`, with
main declaration
`AlgebraicGeometry.ProEtale.cartier_reduction_site_comparison`. All theorem proofs
are `sorry`. Definitions contain real constructions. No statement correction or
dependency repair is made. One integral-boundary definition node is added.

The relative extension presentation is used for the pole boundary. It records the
frame torsor of the actual dual ideal, its lift over supported +1, and the actual
canonical section on the complement. Local frames are inverse equations. Sending
such a frame into the extension and taking its integer powers reconstructs the
local sections u t^(-a). Conversely the pole extension supplies exactly this
relative presentation. The extension class, rather than a representative middle
sheaf, is selected from an existence-and-uniqueness theorem. Thus changing an
isomorphic representative cannot change the boundary. This is the permitted
uniqueness case of AGENTS.md section 5, not selection of arbitrary data from a
mere existence statement.

The finite reduced arrows are likewise selected only from `ExistsUnique`
statements. Their specifications are full supported-sheaf scalar-adjunction
equations. The main theorem additionally asserts the universal properties of
both source and target scalar units against EVERY unbounded complex. Consequently
the adjunct equations characterize actual module-derived scalar extensions; they
are not a criterion for equality after forgetting scalars. This presentation
avoids choosing another derived functor or replacing a canonical map by an
unconstrained isomorphism.

Hypotheses, one by one:

- Prime ell: `(ℓ : ℕ) (hℓ : ℓ.Prime)`.
- Positive exponent: `(r : ℕ) (hr : 0 < r)`; `pow_pos hℓ.pos r` supplies the
  positive integer modulus needed by the Kummer and reduction interfaces.
- R = Z/ell^r: `cartierResidueRing ℓ r`, a universe lift of that exact ZMod ring.
  `cartierResidue_cast` states its annihilation by the modulus.
- A finite commutative R-algebra: `(A : Type (u + 1)) [CommRing A] [Finite A]`
  with `(hA : ((ℓ ^ r : ℕ) : A) = 0)`. The unique possible R-algebra map is
  explicitly `cartierResidueAlgebra ℓ r A hA`. This is equivalent to supplying
  the R-algebra structure, since a unital map from Z/n is fixed by integer casts.
- Schemes and divisor: `{D Z : Scheme.{u}} (i : D ⟶ Z)
  [IsClosedImmersion i] (hI : i.ker.IsInvertible)`, precisely the recorded
  effective-Cartier-center encoding. The line is the existing dual ideal module.
- Invertibility: `hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))`. Because r > 0,
  invertibility of ell^r is equivalent to invertibility of ell. Global and local
  invertibility agree for the integer section. No finite-type, reducedness,
  connectedness, smoothness, properness, or coefficient-flatness hypothesis occurs.

Constructions and clauses, one by one:

- Ordinary etale/pro-etale module derived categories: `DerivedCategory` and
  `Ext` in fixed-ring module sheaves. `Ext.hom` is the standard bijection to
  the displayed shifted derived Hom, so Ext degree two is the exact arrow
  i_* A_D -> A_Z(1)[2]. No condensed or completed coefficients occur.
- Integral pole extension and quotient t inverse -> +1:
  `Etale.CartierPoleBoundarySpec`, `cartierPoleBoundary_existsUnique`, and
  `Etale.cartierPoleBoundary`. The specification requires a short exact extension
  with kernel `Z.gmSheaf`, quotient the actual `Etale.lowerStar` of the integral
  constant, an equivariant frame map lying over supported one, and the canonical
  complementary frame mapping to zero. Its class is exactly `hE.extClass`, hence
  its derived arrow is the negative-cone-projection `singleδ` from Mathlib.
- Exact inverse image: the existing `comparisonUpperStar`; its `mapExactFunctor`
  on Ext applies its exact termwise derived functor. This is the underlying
  unbounded functor of the recorded `siteComparisonDerivedPullbackPlus`, restricted
  there to bounded-below objects. All objects being compared here are sheaves and
  their shifts, hence bounded below; there is no boundedness assumption on tests
  of the scalar adjunction.
- B = nu inverse Gm and its map to full units: `cartierUnitsComparison` is the
  transpose of identity on units of etale objects. Its codomain is the existing
  `Scheme.proEtaleUnitsSheaf`, whose sections are lifted additive units of Gamma(U,O).
  No isomorphism from the whole B to full units is assumed.
- Canonical supported integral source identification:
  `cartierIntegralSourceComparison`, composed from the existing direct-image
  comparison mate and the constant adjunction comparison. Its isomorphism theorem
  uses qcqs comparison at degree zero. `cartierIntegralSourceIso` has exactly this
  underlying map. `geoCartierSourceComparison A i` is the existing finite version,
  and the main theorem asserts its invertibility.
- The full boundary beta = a[1] nu inverse beta_et:
  `cartierProBoundary` precomposes the pulled Ext class with the inverse supported
  mate and postcomposes with the units map. It does not precompose by the map
  from the global constant sheaf to the supported sheaf.
- Quotient source normalization and reduction of supported restriction:
  `Etale.supportedIntegralGenerator A i` is the actual coefficient unit on the
  entire supported sheaf. `cartierProIntegralGenerator` is its transport under
  the canonical integral and finite mates and the scalar-forgetting comparison.
  `CartierScalarUnit` in degree zero asserts the derived scalar universal property
  for these exact units. Thus the source identification sends reduction of one to
  one and transports the existing restriction unit, not an arbitrary source iso.
- Kummer target normalization and positive sign:
  `cartierEtaleKummerUnit` uses the existing Kummer sequence's `extClass`, followed
  by the existing pure-root tensor map. `cartierProKummerComplex` uses precisely
  the existing roots kernel inclusion and actual power map on full units;
  `cartierProKummer_exact` states epimorphy using Kummer on each test scheme.
  `cartierProKummerUnit` is its positive boundary followed by `cartierProRootMap`.
  The main theorem's degree-one `CartierScalarUnit` clauses say exactly that
  these connecting arrows are the scalar-extension units to the shifted Tate
  lines. For A = R this is the prescribed Kummer identification of L_R(G).
- Roots-induced target identification: `cartierRootsComparison` is a literal
  kernel lift of the pulled etale inclusion followed by the units comparison.
  Its defining kernel equation fixes the map; its isomorphism theorem follows
  from comparison sections and etale roots pullback. `cartierProRootMap` uses
  its inverse and the pulled pure-root map, followed by
  `cartierForgetComparison`. The latter is itself the adjoint of the module
  comparison unit after forgetting scalars. Thus no unnormalized roots iso is used.
- Entire finite R-linear arrow equality: the main theorem equates
  `(Ext.mk₀ (geoCartierSourceComparison A i)).comp (cartierReducedPro ...)`
  with `(cartierReducedEtale ...).mapExactFunctor (comparisonUpperStar ...)`.
  This equation is in module Ext before forgetting coefficients and before any
  restriction to global one. Instantiate A with `cartierResidueRing ℓ r` for
  the R assertion. Its definitions specify exactly the normalized reductions
  of the entire integral boundaries. The source and target Hom universal
  properties justify this model-independent rendering of L_R(beta).
- Derived extension R -> A and canonical supported-source/Tate-line units:
  `GeoCartierScalarCompatibility (cartierResidueAlgebra ℓ r A hA) ...`
  relates the reduced R arrow to the reduced A arrow. This is the existing
  definition, including sectionwise 1 -> 1 and pure-root normalizations,
  universal derived scalar units on source and line, and equality of the entire
  supported classes. There is no flatness assumption on A over R.
- Identification with c_D of sk-lem-geo-cartier: the main theorem supplies
  `Etale.SupportedKummerBoundary` for the etale reduced arrow,
  `GeoCartierChernEquation` for the pro-etale reduced arrow, and the exact
  supported-mate comparison equation. Its final clause identifies EVERY class
  satisfying the existing sk-lem-geo-cartier relative-boundary/comparison
  specification with `cartierReducedPro`. This applies to the classes provided
  by `exists_geoCartierCycleClass`; it does not choose an unspecified member of
  that theorem's existential family. The relative boundary fixes both the
  supported map and its positive Chern-class composite.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules` and the dual ideal.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, with the existing comparison adjunction.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `ProEtale.siteComparisonDerivedPullbackPlus`, whose unbounded underlying functor
  is `comparisonUpperStar.mapDerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.SingleTriangle`:
  `DerivedCategory`, `ShortComplex.ShortExact.singleTriangle_distinguished`, and
  `singleδ`; `.Ext.ExtClass` relates its arrow to `ShortExact.extClass`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`:
  `directImageComparison` and the canonical lower-star comparison mate.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem.
- `Sheaf.Paper.DivisibleExtensionDerivedReduction`:
  `DivisibleReduction.divisible_extension_derived_reduction`, `identifications`,
  `boundary`, `boundary_natural`, and `inverse_image_natural`; their normalization
  is retained through the scalar-unit specifications.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `Scheme.proEtaleRootsOfUnitySheaf`, its actual power map, and kernel inclusion.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `Scheme.finite_etale_torsion_twist_line` and the existing finite Tate line.
- `Sheaf.AlgebraicGeometry.GeoCartierCycleClass`:
  `GeoCartierClass`, `geoCartierSourceComparison`, `geoCartierLine`,
  `GeoCartierScalarCompatibility`, `GeoCartierChernEquation`, and
  `exists_geoCartierCycleClass`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.lowerStar`; `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleConstantModuleDirectImage`, the intrinsic constant-ring
  pushforward. The statement uses the same fixed-scalar presentation as the
  recorded Cartier-class interface: `ProEtale.lowerStar` is precomposition on
  these sheaves, and `finiteCoefficientRealization` extends that scalar action
  to the constant ring sheaf by sheafification. This is the canonical equivalence
  of module-sheaf presentations, not a definitional equality of the two functors.
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`:
  `proEtaleComparisonPullbackSections`; and
  `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback`, including its roots-inclusion equation.
- The additional proof-plan imports are the recorded finite stalks, constant
  stalks, conservative geometric stalks, finite direct-image exactness,
  Grothendieck/enough-injectives and degree-zero resolution results, K-flat tensor
  comparison, line-torsor correspondence, and torsor-to-H1 boundary correspondence.

Edge cases checked mathematically before writing:

- Empty Z and empty D: the supported sheaf and supported class are zero where
  appropriate. The relative specification still has the complementary canonical
  frame, and all unit and comparison maps are the canonical zero/identity maps.
- Nonreduced Z is allowed; only Cartier regularity is used for the pole exponent.
- No exclusion of disconnected or non-quasi-compact Z occurs. The morphism i is
  finite and thus qcqs, even when Z is not quasi-compact.
- The zero coefficient ring is allowed by `CommRing` and `Finite`, and every
  comparison specializes to the zero derived module category.
- R -> Z/ell, with r > 1, is a nonflat coefficient extension included verbatim.
- Positive r excludes the unintended r = 0 case of the stated prime-power setup;
  no other characteristic restriction is imposed beyond invertibility of ell.
- Schemes have universe u, their sites retain the existing object/morphism size
  convention, and coefficients live in u+1. The generic scalar-unit predicate has
  independently bound category, morphism, Ext, and localization universes. No
  equality of site object and morphism universes is imposed.

Searches performed with the prescribed wrappers:

- LeanFinder, `Effective Cartier divisor pole extension derived reduction Kummer
  boundary etale proetale comparison`: eight standard-etale algebra results, none
  about pole-boundary site comparison.
- Loogle, `ShortComplex.ShortExact.singleδ, Functor.mapDerivedCategory`: no hits;
  the service reported the unknown short identifier. The actual Mathlib sources
  were then read directly for their complete signatures and sign conventions.
- Mathlib grep, `Cartier|Kummer|pole` in AlgebraicGeometry: zero hits.
- LeanSearch, `Cartier divisor pole extension units integral boundary`: eight
  unrelated fractional-ideal, meromorphic analytic divisor, and constant-sheaf hits.
- The further integral-boundary searches are recorded verbatim in the new node:
  LeanSearch and LeanFinder returned only algebraic relative Picard/fraction and
  constant-sheaf declarations; Loogle no hits; Mathlib grep zero hits.
- `rg` of both project source trees found no existing pole-comparison declaration;
  the item id is absent upstream and in the upstream name index. DAG search finds
  the item and its ancestor, with no separate integral pole-extension definition.
  `blueprint_refs.py search 'relative extension'` returned zero nodes.

## New nodes

`def-sp-cartier-pole-boundary`, module
`Sheaf.AlgebraicGeometry.CartierPoleBoundary`, declares
`AlgebraicGeometry.Etale.CartierPoleBoundarySpec`. It is the integral relative
extension-class specification of (G1), using the actual dual ideal frame torsor,
its complementary canonical section, and supported +1. The existing
`SupportedKummerBoundary` specifies the finite degree-two class and its Kummer
composite; it does not give this integral degree-one class. Its existing
supported section and generator constructions are reused, rather than redefined.
The new node cites those constructions and the existing divisor, site,
direct-image and derived-category definitions. Its source, three search kinds,
blueprint ancestry, independent universes and full Lean definition are recorded.

## Validation

Both delivered files are checked individually through `scompile.py`, in import
order, with the prescribed 60-second per-file limit. Final compiler and delivery
preflight outcomes are recorded below after the checks complete.

The final `scompile.py` invocation returned exit code 0 for both delivered modules,
including their sandbox and library-name checks, with no errors or warnings.
The wrapper's prescribed limits were not changed. Its earlier missing `Finite`
instance diagnostic was repaired using the named prime-power finiteness statement
and the explicit local instance inside `cartierResidueReducedPro`.

`deliver2.py --no-push` returned OK: the five-file packet passed server preflight
and compilation. No preflight repair was required.

## Second reading by Q54

Independent maintainer reading of immutable delivery
e09ba1c3b0d3ad79da13c50cea9b4382f30ef67d, performed on 2026-10-18.
This replaces the delivered placeholder saying that no second reading occurred.
The reviewer read packet.md, the snapshot item and all sixteen statement dependencies,
both delivered modules, their declaration docstrings, the report, and the actual
source construction (G1). No Lean statement or mathematical node is changed.

Hypothesis and conclusion checklist:

- Prime and exponent: `ℓ`, `hℓ`, `r`, `hr` express precisely prime ℓ and r > 0.
  The helper positivity proof uses `pow_pos hℓ.pos r`; the main binder retains hr.
- Coefficients: finite `CommRing A` with `hA : (ℓ^r : A) = 0` is exactly a finite
  commutative Z/(ℓ^r)-algebra: its unital algebra map is unique.
  `cartierResidueRing`, `cartierResidueAlgebra` and `cartierResidue_cast` use that
  actual residue ring and coefficient map, with an innocuous universe lift.
- Geometry: `[IsClosedImmersion i]` and `i.ker.IsInvertible` are the recorded
  effective-Cartier-center interface, not merely an arbitrary invertible module.
  `hZ` is equivalent to invertibility of ℓ since r > 0. No Noetherian, smooth,
  reduced, finite-type, connectedness, properness, or base qcqs assumption is added.
- Integral extension: `CartierPoleBoundarySpec` requires a real short exact
  extension with kernel G_m and supported integral quotient, plus its equivariant
  dual-ideal frame torsor over supported +1. The canonical complementary frame
  maps to zero. Locally these data reconstruct the sections u t^(-a), with
  t inverse mapping to +1. `cartierPoleBoundary_existsUnique` fixes the class,
  so choosing it does not introduce arbitrary extension data.
- Derived boundary and sign: `hE.extClass.hom` is `hE.singleδ`, by Mathlib's
  `ShortExact.extClass_hom`. `singleδ` uses the short-exact triangle; its cone
  arrow agrees with the negative projection convention. Kummer units use this
  very extension class, not an unrelated connecting arrow. The docstring's
  identity homotopy gives u v + k p = 0 and hence k inverse u = -p v inverse.
- Sites and categories: the statement uses ordinary `DerivedCategory` and module
  `Ext`, with exact termwise `comparisonUpperStar`. The recorded bounded-below
  comparison is its restriction; all sheaves and their shifts here lie there.
  The underlying small pro-etale site is retained. The intrinsic direct image
  and the fixed-scalar `lowerStar` are the usual equivalent presentations,
  sectionwise precomposition with the same base-change functor and coefficient
  action. No condensed coefficient or substitute site is used.
- Full units: `cartierUnitsComparison` is the adjoint of identity on etale units,
  landing in the actual `Scheme.proEtaleUnitsSheaf`. Its sections are the lifted
  additive presentation of Gamma(U,O_U) units. There is no assertion that the
  entire inverse image of etale G_m equals the full units sheaf.
- Supported source: `cartierIntegralSourceComparison` uses the existing
  `lowerStarComparisonUpperStarBaseChange` adjunction mate followed by the
  constant-sheaf left-adjoint comparison. Its inverse is used in
  `cartierProBoundary`; the boundary then postcomposes with the units map.
  `geoCartierSourceComparison` is the existing finite-coefficient mate.
- Roots target: `cartierRootsComparison` is the kernel lift of the actual pulled
  roots inclusion followed by the units map. It is fixed by that equation.
  Its isomorphism theorem uses comparison sections and the roots-inclusion
  normalization of `etaleFiniteTwistPullback`, so the identification preserves
  powers and the residue-ring action.
- Reduction: `CartierScalarUnit` tests the specified unit against every unbounded
  derived object. Its degree-zero source and degree-one Kummer clauses identify
  the displayed objects with derived scalar extensions. The two reduction
  specifications are equations on the ENTIRE supported integral sheaf. With
  these universal properties they uniquely specify module-derived arrows.
  Thus they do not infer equality from a Chern-class composite or from forgetting
  coefficients. The main equality itself is in module Ext degree two.
- R and finite extension: specialize the theorem to `cartierResidueRing` for the
  requested R assertion. `cartierResidueReducedPro` supplies its finite instance.
  `GeoCartierScalarCompatibility` then gives derived extension to A, including
  the canonical supported-constant and roots-tensor units and the full-arrow
  equation. No flatness of A over R is assumed; the Tate line is locally free.
- Identification with c_D: the last clauses supply the existing relative
  `SupportedKummerBoundary`, its actual Chern equation, and uniqueness for every
  class with that relative boundary and canonical source comparison. This applies
  to the family from `exists_geoCartierCycleClass`. The conclusion identifies the
  supported morphism and its restriction/sign, rather than just its composite.

Dependency and construction audit:

All statement-dependency records were read, including the Mathlib match of
`lem-sf-derived-ses-triangle` (which needs no new dependency module). The exact
`singleTriangle_distinguished`, `singleδ`, and `extClass_hom` declarations were
opened in Mathlib. The recorded site comparison, derived pullback, change-of-rings
cochain model, divisible reduction and its naturality/normalization, full roots,
finite Tate line and roots pullback, section comparison, Cartier class, divisor
line and direct-image declarations were opened in the read-only group/source
clones. The pro-etale framework was checked in the group clone, including its
module-object direct image; the delivery uses fixed scalar sheaves, not that
condensed-ring construction. The helper declarations are listed in the item's
`lean.declarations` and belong to its canonical comparison/reduction constructions.
They are permitted helpers under the missing-helper rule, not missing independent
DAG prerequisites. No §1(B) repair or §1(C) statement correction is necessary.

The new definition node has its own real module, self-contained statement,
source/place, definition dependencies, worker-created metadata, empty proof fields,
null mathlib match, required search records and blueprint ancestry. Its statement
matches its source's relative integral pole class. The existing finite
`SupportedKummerBoundary` is not an integral degree-one pole-boundary definition.
Independent rg searches for pole extension, pole boundary, CartierPoleBoundary,
cartierPoleBoundary, CartierScalarUnit and the main theorem in the project,
upstream and Mathlib sources found no exact duplicate. `GeoCartierScalarUnit`
is the existing degree-zero ring-map specialization; the generic shifted
`CartierScalarUnit` is needed also for abelian sheaves and the degree-one unit.
The worker's LeanSearch, LeanFinder/Loogle and grep search records were read.

Both new module docstrings and every declaration name source places and blueprint
ids. The main proof docstring covers the nine proof steps, including stalk/source
normalization, pushout, exact inverse image, full-boundary naturality, sign,
coefficient extension and relative Cartier identification. Every theorem body is
`by sorry`; definitions use actual constructions or choices from explicit unique
specifications. There is no local theorem proof or data-valued sorry. Both
`lean.statement` strings are verbatim prefixes of their declarations, ending
immediately before `:=`; every Lean line is at most 100 characters. All variables
and universes are explicitly bound with autoImplicit false.

Edge cases:

- Empty Z and empty D are included; the complement and its prescribed frame
  still exist, and the supported sheaf/class is zero when D is empty.
- Disconnected, nonreduced and non-quasi-compact schemes are included. Closed
  immersions are finite and qcqs even over a non-quasi-compact base.
- The zero coefficient ring and nonflat coefficients Z/(ℓ^r) -> Z/ℓ for r > 1
  are included. No nontriviality or coefficient flatness instance is present.
- r = 0 is excluded exactly as the node requires. General helper n = 1 causes
  zero residue coefficients and no inconsistency; the main n is a positive prime
  power. No n = 0 assertion is made by the main theorem.
- Sites keep the original object universe u+1 and morphism universe u; schemes
  are Scheme.{u}, coefficients are in the standard u+1 sheaf universe. The generic
  scalar predicate binds category, Hom, localization and Ext universes separately.
  No universe equality or silently restricted test category is imposed.

Route pivot: the recorded statement/proof dependencies have empty intersection
with origin/newtargets-dag:coord/route-pivot-dropped.txt. No item repair note is
present at that ref. The construction uses the ordinary derived/K-flat route and
no enhanced localization, Quillen, dg, coherent-sections or operadic machinery.

Findings and corrections:

H11: the delivered second-reading section was a placeholder, not an actual reading.
The complete replacement report retains the Worker report and supplies this actual
independent reading. No mathematical or Lean correction was found necessary.

Independent compile reproduction on 2026-10-18: the prescribed scompile.py wrapper
was invoked on both immutable delivered files together and returned exit code 0,
with no errors or warnings. It checked a private overlay, the pole module's
preliminary compile, and both modules under sandbox and library names. The final
library checks reported 10.0 s for CartierPoleBoundary and 59.4 s for
CartierReductionSiteComparison. Displayed times include compile-slot waits; the
60-second limit starts after slot acquisition and was not changed. The installed
wrapper is now the server-side overlay port, using nt_srv_compile.py
--wire-confirm; the older local-only wording does not describe this installed
version. No direct SSH, lake/global build, repository mutation, live Lean write,
claim, merge, delivery or preflight command was run by the reviewer. Full compiler
output and the exact invocation are recorded in the accompanying review.md.
