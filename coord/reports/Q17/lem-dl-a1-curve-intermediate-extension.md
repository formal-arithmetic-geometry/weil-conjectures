## Worker report

This delivery states `WeilConjectures.qbarCurveIntermediateExtension` in
`Sheaf.Paper.CurveIntermediateExtension`, with its proof `sorry`. It characterizes
ordinary sheaf direct image shifted by one as the perverse extension having no
boundary perverse subobject or quotient. The characterization uses a unique
isomorphism with prescribed open restriction, includes naturality for geometric
sheaf maps, and states the Frobenius intertwining equation. The seven-step proof
from the node is included in the theorem docstring. The node's mathematical
statement, proof and proof dependencies are unchanged.

The statement interfaces needed three dependency repairs, detailed below. There
are no new DAG nodes. The item gains the already existing definition nodes
`def-per-support-condition` and `def-a1-common-stage-lisse-lattice` in `stmt_deps`.
The latter is the published finite-stage completed-lattice presentation of the
same lisse adic condition; it does not ask for a Frobenius-stable lattice.

Hypothesis and conclusion correspondence:

- The global finite field, its fixed algebraic closure, and their inclusion are
  `D : FiniteFieldDatum.{u}`. Its fields contain p prime, a positive, q=p^a,
  the cardinality of k₀, and the chosen algebraic closure k. Geometric schemes
  are the actual `D.geometricFiber` objects, not unrelated models.
- The coefficient prime is `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`.
  `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, and
  `[IsAlgClosure ℚ_[l] Ω]` give the arbitrary chosen algebraic coefficient
  closure. The scheme and coefficient universes u and v stay independent.
  Invertibility on geometric fibres is supplied by `sfWeilPrimeInvertible`;
  the base-field unit for the perverse predicates is the existing
  `finiteFieldDatumPrimeUnit D l hl`. No invertibility hypothesis is added.
- The base curve and dense open are `c : Scheme.MiddleExtensionCurve D`, the
  existing bundle from `def-wf-middle-extension`. Its `C`, `U` and `j` are
  objects and a morphism over Spec k₀. Its fields give finite type as locally
  finite type plus quasi-compact, separatedness, an open immersion, density,
  `Smooth c.C.hom`, and `c.C.left.IsPureDimension 1`. The finite-type and
  separatedness properties of U are consequences of the node's dense open
  in a noetherian separated finite-type curve, not additional mathematical
  restrictions. The item's extra geometric-connectedness assumption is
  `[GeometricallyConnected c.C.hom]` on the theorem.
- The geometric open map is `qbarCurveGeometricOpen D c`, literally the map
  obtained by the fixed `Over.pullback` along Spec k → Spec k₀.
  `qbarCurveDerivedRestriction` is the recorded `commonStageDerivedPullback`
  on that map, with its original finite stages and residue-field inverses.
  Geometric finite type and quasi-compactness reuse the published
  `zlGeometricFiberLocallyOfFiniteType` and `zlGeometricFiberQuasiCompact`.
  The elementary separated base-change instance is supplied explicitly.
- `F₀ : sfCommonStageWeilSheaf D l hl c.U Ω` is precisely a fixed Frobenius
  pair whose carrier is in the standard constructible heart. Its lisse
  hypothesis is `HasCommonStageLisseLattice ... F₀.obj.carrier`, the recorded
  equivalent finite-field adic presentation. `qbarCurveWeilCarrier` forgets
  only Frobenius, yielding F as a standard-heart object, not a new sheaf.
- `QbarPerverseHeart` is the intersection of `QbarPerverseLE ... 0` and
  `QbarPerverseGE ... 0`. These are the support and cosupport conditions
  applied after shift by n, exactly the node's middle-perversity classes.
  The support is closure of the nonzero completed geometric cohomology-fibre
  locus after inverting the coefficient uniformizer. The nonempty guard and
  `0 ≤ i` implement dimension minus infinity for empty support. Cosupport
  tests actual `IntegralVerdier.dual`, hence RHom into the dualizing object;
  it uses its natural exceptional-adjunction representing property to avoid
  choosing a noncanonical object. Yoneda identifies all representatives,
  and support is invariant under those identifications. This is the same
  rational Verdier dual, computed on its integral representative.
- `qbarCurveOrdinaryPushforward` is ordinary j_* in the intrinsic standard
  heart, defined by the right-adjoint universal property of the actual
  sheaf inverse image. Its named existence theorem identifies it with the
  sectionwise direct image V ↦ F(V ×_C U), including coefficient actions.
  `qbarCurveShiftedOrdinaryImage` composes that functor, the full heart
  inclusion, and `shiftFunctor _ (1 : ℤ)`. This is (j_*F)[1]. It does not
  replace ordinary j_* by Rj_* or discard higher derived direct images.
- `QbarCurveIntermediateExtensionAssertions` starts with existence of `hA`,
  asserting exactly that this shifted ordinary image is perverse. Its next
  conjunct is `QbarCurveBoundaryMinimal ... hA`.
- Boundary minimality quantifies over every Q in the full *geometric*
  perverse subcategory. For every monomorphism Q → A, and independently for
  every epimorphism A → Q, zero open restriction implies `IsZero Q.obj`.
  Thus both the subobject and the quotient clause are present. Neither is
  replaced by a statement about standard-heart subobjects or only about
  Weil-equivariant subobjects.
- `β` is a natural isomorphism from open restriction of the shifted ordinary
  image to `qbarCurveShiftedSource`, which is F[1]. The theorem fixes each
  component of β to the pullback/shift comparison followed by the shift of
  the **ordinary sheaf adjunction counit**. This is the identity
  normalization on the open, not an unspecified identification.
- For every perverse P and specified identification `α : j*P ≅ F[1]`, the
  next conjunct is an iff: boundary minimality is equivalent to existence
  of a **unique** `e : P ≅ (j_*F)[1]` satisfying
  `R.mapIso e ≪≫ β.app F = α`. It includes existence of the comparison,
  uniqueness with its restriction, and the converse characterization.
  Taking P to be any object denoted j_!*(F[1]) gives the canonical iso in
  the node. No separate definition presupposes this uniqueness theorem.
- Naturality quantifies over F₀', its lisse condition, any two characterized
  extensions P,P', and every *geometric* sheaf arrow f:F→F'. The unique
  extending arrow g has restriction f[1] under α,α' and satisfies
  `g ≫ e'.hom = e.hom ≫ shiftedOrdinaryImage.map f`. This is the naturality
  square for the canonical comparisons; f need not commute with Frobenius.
- The Frobenius square equality w is for the actual base-changed j. The
  comparison `rΦ` is normalized at every coefficient representative by
  `qbarCurveRationalFrobeniusComparison`. That helper is the inverse first
  pullback-composition comparison, transport across w, and the second
  composition comparison. It is the same canonical construction as the
  published `zlRationalFrobeniusComparison`, with the closure universe made
  independent of the scheme universe.
- The final conjunct supplies a Frobenius structure θA on the shifted
  ordinary image, normalized by β and the shifted structure of F₀. For
  every perverse Weil extension (P,θP) whose α is equivariant, the unique
  comparison satisfies
  `θP.hom ≫ e.hom = FrobeniusPullback.map e.hom ≫ θA.hom`.
  Consequently it is an isomorphism of the fixed pairs, and its inverse is
  equivariant. All perverse triangles and subobjects in the statement are
  geometric; no triangulation of the category of Weil pairs is assumed.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, its `geometricFiber`
  and coefficient convention; `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`; `Sheaf.AlgebraicGeometry.PureDimension`:
  `Scheme.IsPureDimension`.
- `Sheaf.Paper.LisseIntegralSmallCoefficients` and its imported
  `LisseAdicSheaves`: the small integral inverse-system, stalk quotient and
  finite-extension conventions. The consumer uses the already landed
  `Sheaf.Paper.CommonStageLisse.HasCommonStageLisseLattice` for this exact
  condition in its intrinsic common-stage category.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`,
  `sfCommonStageWeilFrobeniusPullback`, `sfWeilFrobeniusPullback`,
  `sfWeilPrimeInvertible`; the imported `IsoAlgebra` has the actual carrier
  and structure iso. The upstream derived category of Weil sheaves is not
  used as the geometric carrier.
- `Sheaf.Paper.CurveWeilMiddleExtension` and its imported
  `CurveMiddleExtension`: existing ordinary-image realizations and
  `Scheme.MiddleExtensionCurve`. The additional intrinsic-heart interface
  is the dependency repair below.
- The recorded finite-coefficient `Etale.DerivedCategory.IsPerverseLE`,
  `IsPerverseGE`, `IsPerverseHeartCandidate` were read in full in
  `WeilConjectures.SixFunctors.Etale.Perverse.Basic`. Its own docstring says
  those coefficients are not a discrete Qbar étale realization.
  `Sheaf.Paper.PbcSupportCondition.PbcSupportCondition` was also read; it
  takes the older PBC pair category. These interfaces are retained by
  public imports and extended to the intrinsic category in this delivery.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; the actual induced common-stage shifts come from
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- Support evaluation reuses `purCoefficientModel`,
  `pbcActualCompletedPull`, `DerivedCategory.homologyFunctor`,
  `PerAdic.pointSections`, `PerAdic.integerToField` from the published
  completed-coefficient/fibre modules. Duality reuses
  `IntegralVerdier.dual`, `integralDualizingLimit`, and the normalized
  `exists_compactSupportReductionTower` construction. Its point unit is
  the actual coefficient sheaf in degree zero.
- `Sheaf.Paper.IntegralPullbackComposition.localPullbackComposition` supplies
  the canonical rational composition factors used in the Frobenius map.
  `ConstructiblePullbackTExact` supplies the current pullback and heart
  conventions, and `ZlImmersionWeilLocalBehavior` supplies the existing
  geometric base-change instances and the normalized comparison pattern.
- Published proof-dependency modules are imported: the dense-open finite
  complement theorem, upstream curve-perverse module, and the abstract
  `TStructure.Homology`/short-exact-triangle module. The two proof-only
  nodes `lem-a1-qbar-open-closed-cohomology` and
  `lem-dl-a1-boundary-hom-vanishing` have no recorded Lean modules to import.
  Their arguments are retained by name in the seven-step proof docstring;
  no statement notion waits on them or takes them as extra hypotheses.

Edge cases checked before writing and again against the final signatures:
F=0; j the identity, hence empty boundary; a nonempty finite boundary; the
constant sheaf on G_m in A^1; rank zero and varying finite local ranks; integral
torsion disappearing after rationalization; vanishing cohomology in arbitrary
negative or positive degrees; and empty cohomology supports. The helper
interfaces also admit empty or disconnected schemes; geometric connectedness
on the item's theorem imposes exactly the node's nonempty connected-curve
case. All geometric perverse P and Q, including zero, remain quantified.
No rank, irreducibility, purity of a sheaf, properness, or Frobenius-stable
integral lattice is assumed. No statement dispute or correction was needed.

Searches for an existing statement (2026-10-18):

- `msearch.py ... leanfinder`, query: “On a smooth curve the perverse
  intermediate extension of a shifted lisse sheaf is its ordinary direct
  image shifted by one”. Eight hits concerned sheaf-module pushforward
  comparisons and ordinary derived-category single-object criteria; none
  gives this characterization, naturality and Weil compatibility.
- `msearch.py ... loogle`, query `IsPerverse, middleExtension`: no hits;
  unknown identifier IsPerverse.
- `msearch.py ... grep`, query
  `intermediateExtension|middleExtension|IsPerverse`: no Mathlib hits.
- `msearch.py ... leansearch`, query: “The ordinary direct image of a
  lisse adic sheaf shifted by one is the intermediate extension on a smooth
  curve, with no perverse subobjects or quotients on the boundary”. Eight
  hits concerned O_X-module restriction adjunctions, sheaf images and
  dense-subsite comparisons, not this l-adic theorem.
- `rg` of the upstream `WeilConjectures` tree for the item id returned no
  declaration. The middleExtension/curve-perverse search found only the
  affine-line basic-perversity theorem and the Fourier/middle-extension
  results. Reading their signatures confirms they do not state the
  general curve boundary-minimal characterization.
- `rg` of `lean/Sheaf` for perverse/intermediate-extension found the existing
  PBC support and support-preservation interfaces, not the item. Searches
  of `dag/lean_names_upstream.json`, Mathlib, upstream and side Lean for
  the new full declaration names found none. The existing common-stage
  lisse-lattice node was reused rather than copied.

All source and repository reads were read-only. Every edit is in the assigned
sandbox. Validation uses only scompile.py and the prescribed delivery dry run;
all theorem proofs in this packet are `sorry`, and definitions contain real data.

## Dependency modules

`def-wf-middle-extension`: `Sheaf.Paper.QbarCurveOrdinaryImage` publicly retains
`CurveWeilMiddleExtension` and `CurveMiddleExtension`. Neither old carrier is
the currently recorded fixed-pair geometric category. The new module states
the identical ordinary j_* as the right adjoint of the actual sheaf inverse
image on the intrinsic common-stage standard heart. This is a universal
property fixing the functor and adjunction up to their unique compatible
isomorphism. The two postponed helper theorems are
`qbarCurveRestriction_mem` (heart membership) and
`qbarCurveSheafRestriction_isLeftAdjoint` (ordinary constructible adjunction);
each has its full natural-language proof and the owning node tag. The shifted
functor is constructed in full from this ordinary image and the existing shift.
The dependency node changes only its lean record, with the required note.

`def-per-support-condition`: `Sheaf.Paper.QbarPerverseSupportCondition`
publicly retains the former PBC support module, hence also the upstream
finite-coefficient support/cosupport definitions. It supplies the same two
conditions for the intrinsic common-stage category used by the current Weil
pair interface. Geometric fibres are actual completed pullback/cohomology/
point-sections/inversion functors. Cosupport uses ambient RHom and the natural
exceptional-adjunction property of the dualizing object; it quantifies over
its representatives instead of choosing any data from mere existence. The
compact-support helper uses the existing normalized reduction-tower
construction and Roos limit and works over arbitrary base fields with
invertible l. No finite-field restriction is imposed on this definition.
There is no `sorry` in this module. The dependency changes only its lean record.

`def-per-perverse-subcategories`: `Sheaf.Paper.QbarPerverseSubcategories`
uses the repaired dependency's support and cosupport conditions, after the
actual shift by n, and intersects the zero classes. It retains the old
finite-coefficient and PBC interfaces by public import. No alternate
curve-heart criterion is substituted for the defining support/cosupport
formulas. There is no `sorry` in this module. The dependency changes only its
lean record, with the required note.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
