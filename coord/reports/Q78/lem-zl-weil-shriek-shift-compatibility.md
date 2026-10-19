## Worker report

The item is stated by `WeilConjectures.weilShriek_shift_compatibility` in
`Sheaf.Paper.WeilShriekShiftCompatibility`. The original statement, proof and
proof dependencies are unchanged. A new definition dependency supplies the absent
finite-stage canonical exchange and the normalized shifts of the existing functors.
All theorem proofs in this delivery are `sorry`; all definitions have actual data.

Hypothesis and clause correspondence:

- The global p,a,q,k₀,k datum is `D : FiniteFieldDatum.{u}`. Its prime, exponent,
  cardinality and chosen algebraic closure are fields of the recorded structure.
  `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give precisely the distinct coefficient
  prime. `E` with its field, Padic algebra and finite-dimensional instances is a
  finite extension of Q_l. `Ω` with its field, Padic algebra and `IsAlgClosure`
  instances is the chosen closure; `ι : E →ₐ[Padic l] Ω` realizes E inside it.
- `X₀ Y₀ : Over (Spec (.of D.k₀))` are schemes over the finite field. Each
  `LocallyOfFiniteType` plus `QuasiCompact` structure morphism is finite type.
  Each `QuasiSeparated` structure morphism gives the stated quasi-separatedness.
  `f₀` is a morphism in this over category; its `IsSeparated`, locally-finite-type
  and quasi-compact instances say it is separated finite type. There is no
  `IsSeparated X₀.hom` or `IsSeparated Y₀.hom` assumption.
- The actual geometric fibres are `D.geometricFiber`, and their morphism is the
  existing `zlFiberMap`. The Frobenius pullbacks use the recorded
  `D.geometricFrobenius`, not the absolute Frobenius or a k-linear replacement.
  Prime invertibility is constructed by `sfWeilPrimeInvertible`, never assumed.
- The E branch quantifies over every `sfWeilComplex D l hl X₀ E`; its carrier
  is in the actual raw rationalization `sfRationalConstructibleCategory`.
  The Ω branch quantifies over every `sfCommonStageWeilComplex D l hl X₀ Ω`;
  its carrier is the actual finite-stage-pair common-stage category. The
  separate conjuncts render the two possible values of Λ, with no change of
  the fixed-pair Hom sets to Ext groups of Weil sheaves.
- `c : Compactification f₀.left` is universally quantified presentation data.
  The compact-support operation is open extension followed by proper image.
  In the E branch this is `fieldWeilShriek`, with its specified adjunction-mate
  exchange `fieldWeilShriekExchange`; `fieldWeilShriek_recorded` identifies the
  underlying operation with the recorded normalized compact-support action for
  any geometric compactification. In the Ω branch both operation and exchange
  are reused literally as `zlCommonStageShriek` and `zlShriekFrobenius`, whose
  owning node already supplies the corresponding recorded-action comparison.
- `r : ℤ` covers all shifts. Every shifted Weil map is the Frobenius pullback's
  `commShiftIso r` followed by `K.str.hom⟦r⟧'`. The pullback comparisons are
  fixed by the existing signed Roos formulas, restriction, localization and
  finite-stage classes; shriek's comparison is the composite proper/open
  adjunction shift. No arbitrary exchange or independent shift hypothesis is
  supplied to the theorem.
- Read Lean composition left to right: the left side is
  `Ex_(K[r]) ≫ Rf!(theta_(K[r])) ≫ sigma_K,r`, which is precisely the node's
  `sigma ∘ theta_(Rf!(K[r]))`. The right side is
  `Lg_Y*(sigma) ≫ pullbackShift ≫ (Ex_K ≫ Rf!(theta_K))[r]`, precisely its
  `theta_(Rf!K)[r] ∘ Lg_Y*(sigma)`. The target is `(Rf!K)[r]` in each branch.
  Since sigma is a component of a natural isomorphism, this equation is exactly
  its being a Weil isomorphism, including its inverse. No triangulated structure
  on the fixed-pair category is imposed.

Recorded dependencies read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `.geometricFiber`.
- The scheme-morphism-properties node is a convention record; its named Mathlib
  properties `LocallyOfFiniteType`, `QuasiCompact`, `QuasiSeparated`, and
  `IsSeparated` are used directly.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius` and its actual semilinear construction.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, their recorded shifts and comparisons.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `inclusion`,
  its identity-normalized shift comparisons and representative shift formula.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `integralDerivedPullback`,
  `constructibleIntegralPullback`, `rationalDerivedPullback`,
  `commonStageDerivedPullback` and their specified object/map actions.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`,
  `sfCommonStageWeilComplex`, the two Frobenius pullbacks and
  `sfWeilPrimeInvertible`.
- `Sheaf.Paper.QcqsCompactSupportRealization` and its reexports:
  `sfCompactSupportFiniteFunctor`, `sfQcqsCompactSupportRealization` and the
  projection-normalized integral action.
- `Sheaf.Paper.FieldShriekLowerBound`: `fieldShriek_lowerBound`, the exactness
  input in the proof plan. Its existential unnormalized CommShift witness is
  not chosen as if it uniquely specified canonical comparison data.
- `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius`:
  the recorded `isWeilPairing_mixedSupportCupProduct` was read. It is a finite
  etale cup-product assertion and does not itself give the rational/common-stage
  compact-support comparison. Its module is retained as the recorded proof
  dependency. The needed canonical proper/open maps are instead obtained from
  the already landed `def-zl-common-stage-weil-shriek` and the finite analogue
  supplied by the new definition node. No claim is made that the cup-product
  declaration states all of lem-fix-weil-operations.

Additional existing constructions reused by the new node:
`IntegralCompletedComparison.ShiftCoordinates` and `.ShiftDescent` from
`Sheaf.Paper.IntegralPullbackCompletedComparison`,
`integralPullbackComposition` from `Sheaf.Paper.IntegralPullbackComposition`,
`zlFiberMap` and `zlFrobenius_naturality` from `Sheaf.Paper.WeilIndSheafCategory`,
the compactification arrows from `Sheaf.Paper.WeilCompactSupportCohomology`,
and all existing common-stage proper/open adjunctions and exchanges from
`Sheaf.Paper.CommonStageWeilShriek`. Mathlib's
`Adjunction.leftAdjointCommShift`, `.rightAdjointCommShift`,
`Functor.CommShift.ofComp`, and `mateEquiv` supply the actual constructions.

Edge cases checked: r=0 is the canonical zero-shift comparison; negative shifts
are covered by CommShift over ℤ; successive and mixed-sign shifts obey its
addition laws. Empty schemes and zero complexes are allowed and both composites
are their unique relevant maps. Identity morphisms and equal coefficient fields
are included. No smoothness, weights, purity, coefficient flatness, scheme
separatedness over the base, or t-exactness assumption was added. Scheme universe
u and algebraic-closure universe v are independent. The finite coefficient model
lives in u as in the recorded rational category; all finite subextensions have
such small coefficient models. There is no claim that geometric Frobenius is
k-linear or that the fixed-pair category has its own triangulation.

Searches actually run through msearch.py:

- LeanFinder: "The Frobenius Weil structure on compact support derived direct
  image commutes with cohomological shifts" returned eight hits, led by
  `Functor.mapCochainComplexShiftIso`, with generic shift and underived sheaf
  comparisons; no field-coefficient Weil shriek assertion.
- LeanSearch: "Weil structures on compact support functors commute with integer
  shifts" returned eight generic exact-derived and CommShift declarations,
  including `NatTrans.CommShift₂Int`; no requested assertion.
- Loogle: "Functor.commShiftIso, NatTrans.CommShift" returned zero hits and
  an unknown-identifier diagnostic for Functor.commShiftIso, so it was not
  treated as evidence of mathematical absence.
- Mathlib grep: "Weil|lowerShriek" in CategoryTheory returned zero hits.
- The three searches of the new node are recorded with their exact queries
  and actual results in its mathlib_searches.
- Local rg searched WeilConjectures and lean/Sheaf for Weil/shift/shriek and
  the proposed declaration names. Upstream has finite etale shiftWeilDatum
  and isWeilMorphism_shift_lowerShriek, and a derived-of-Weil-sheaves shriek;
  neither is this raw-rational/common-stage fixed-pair statement. The existing
  CommonStageWeilShriek construction was found and reused. Search by this
  item's id in upstream yielded no exact attachment.
- DAG search and `blueprint_refs.py search 'compact support shift'` found no
  missing-definition duplicate (zero blueprint matches). The existing
  def-weil-frobenius-square-exchange was read: it describes the full
  finite/integral/rational/common-stage system construction, but currently has
  no Lean binding. The new node supplies the narrower proper/open field model
  and shift data on the already normalized pullbacks, reusing the already
  landed common-stage operation. It does not introduce an arbitrary exchange.

## New nodes

`def-zl-field-weil-shriek-shift-data` supplies the finite-stage mate construction
and the canonical shift interface needed to type the item. Its source is the
first two paragraphs of lem-fix-weil-operations.proof.md together with the
exact-functor shifts required in the first paragraph of the composition-weight
proof. Its statement specifies the integral Roos normalization, its good-resolution
descent, rational localization and common-stage components; these determine the
shift data uniquely. It then defines rational proper/open adjoints, their actual
Frobenius mates, their composite and its adjunction shifts. The common-stage
operation and exchange are imported unchanged. Existence and invertibility are
named theorems with complete proof docstrings; no definition contains sorry or
chooses comparison data from an uncharacterized Nonempty. The natural
recorded-action comparison is an assertion, not a chosen replacement exchange.
The new node's statement dependencies explicitly cite each of these existing
notions. Searches are the exact logged LeanSearch, LeanFinder and grep queries
recorded in the node, plus local source and DAG searches detailed above.

## Second reading by Q78

I reread the original node, its two proof steps, the new definition node, and
both Lean files. This is an author self-check: the dispatcher explicitly forbids
starting another agent, and the maintainer performs the independent delivery
review. The finite-field, prime, coefficient-extension and closure hypotheses
are all present. Both coefficient choices occur as separate conjuncts. The
finite-type and quasi-separated structure morphisms and the separated
finite-type f₀ are present; separatedness of either structure morphism is absent.
Both shifted Weil maps include their pullback shift before theta[r], and both
exchange maps have the required Lg_Y*Rf! to Rf!Lg_X* direction. Sigma is used in
the forward direction Rf!(K[r]) to (Rf!K)[r]. The right side shifts the entire
output Weil map, rather than only theta. The new helper file was checked to
reuse the existing common-stage exchange and the published integral shift
predicates and composition. The initial compiler failure exposed a missing
explicit integral inclusion CommShift instance and two line breaks in field
notation; these were corrected without changing the mathematical statement.
A further compile check required explicitly naming both geometric-fibre schemes and
the geometric map in the recorded finite-functor comparison, so typeclass search
uses the published base-change instances rather than an unfolded pullback type.
No mathematical hypothesis was added. No statement correction or disputed
mathematical assertion is needed.

Validation: the prescribed scompile.py invocation on both delivered files completed
with exit code 0, compiling each file separately in dependency order in the private
overlay, sandbox and library confirmation modes. No errors or warnings were emitted.
