## Worker report

The module `Sheaf.Paper.SfLocalizationAllStages` states supported localization at
all four coefficient stages. `WeilConjectures.sfLocalizationAllStages` is the
main existence statement; `sfLocalizationAllStages_weil` states the final Weil
clause. The only postponed proofs are the named statements of this node.
Every helper definition contains actual data; the records package conclusions
of this proposition, rather than hypotheses replacing its canonical operations.
No statement, proof plan, dependency list or dependency record is changed.

### Hypotheses and coefficient stages

| Node text | Lean rendering |
| --- | --- |
| Field k, prime l invertible in k | `(k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))` |
| Finite extension E/Q_l | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` |
| Valuation ring, chosen uniformizer, positive quotient levels | The recorded `Padic.coefficientExtensionRing l E (n + 1)`; `n : ℕ` covers precisely all positive exponents, with `Nat.succ_pos n` |
| Algebraic closure Qbar_l | `(Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`; v is independent of the scheme universe |
| Separated finite-type k-scheme X | `(X : Scheme.{u}) (t : X ⟶ Spec (.of k)) [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]` |
| Closed i and complementary open j | `(i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] (hij : Set.range j = (Set.range i)ᶜ)` |
| Finite stage | `SfLocalizationFiniteCategory`, exactly the full subcategory of the recorded intrinsic finite-torsion predicate |
| Integral stage | The recorded `sfIntegralConstructibleCategory`; no extra boundedness of an integral representative is imposed |
| Rational stage | The recorded raw `sfRationalConstructibleCategory`; no Karoubi completion |
| Algebraically closed stage | The recorded `generalAlgebraicallyClosedConstructibleCategory` with its genuine common-stage Hom groups |

`sfLocalizationResidueMap` is the composite of the canonical field/global-section
map and evaluation at a point. `sfLocalizationPrimeInvertible` transports the
given unit through that ring map, so the recorded pullback APIs require no
additional invertibility hypothesis on X, Z or U.

### Clauses (1)--(4)

`SfSupportedLocalization` uses the actual constructible categories and their
full inclusions into their ambient derived categories. At field stages the
inclusions are identity functors. Its fields are conclusions, existentially
quantified by the main theorem, and are not additional mathematical premises.

1. `jPush : U ⥤ C` is the constructible open direct image. In
   `SfFiniteLocalization.open_push` it is identified as a natural functor with
   `proEtaleConstantDerivedDirectImage j A`. In the integral stage `open_push`
   identifies it with the ordinary completed-ring derived image and `open_limit`
   supplies its recorded Roos presentation and the canonical projection-adjoint
   reduction comparisons. In the rational stage `open_push` is a natural
   comparison with the rationalized integral operation. In the algebraically
   closed stage the stage comparisons identify it at every actual finite field.
   The right adjunction to the recorded pullback determines direct image up to
   the unique compatible adjoint isomorphism, including its Hom action. The finite
   `open_unit` and `closed_unit` fields
   normalize the restricted adjunction units to `finiteRecollementDerivedAdjunction`,
   the existing actual derived sectionwise adjunction.
2. `exceptionalAdjunction : iPush ⊣ exceptional` states the right adjoint, and
   `exceptional_comparison` at the finite stage identifies it with the dependency's
   actual `ProEtale.sfFiniteExceptional A (Compactification.ofIsProper i)`.
   This uses the identity compactification of the closed immersion, hence the
   specified transported etale exceptional inverse image, not an ambient
   pro-etale adjunction for that comparison formula. Integral
   `exceptional_reduction` identifies every positive reduction with that finite
   operation. `exceptional_counit_reduction` fixes the comparison by the actual
   exceptional counit; together with the quotient maps this retains transition
   coherence. `sfLocalizationExceptionalTerm`, `...Comparison` and
   `...Transition` display the restricted finite-exceptional tower, with its
   transitions conjugated from the actual canonical reduction transitions.
   `sfLocalizationExceptionalLimit` states the Rlim formula using precisely the
   reduction units followed by those comparisons as its projections. Rational
   `exceptional` and common-stage `exceptional` identify the operation with the
   prescribed integral rationalization and finite-stage operations, respectively.
3. `distinguished` is exactly `Triangle.mk` of the exceptional counit, open unit,
   and `boundary.app K`. `orthogonal K m` asserts that the displayed shifted
   closed-to-open Hom is a subsingleton, for every K and every integer m. In an additive category this is
   precisely the zero
   Hom group. `unique_boundary` states uniqueness with the first two maps fixed.
   `boundary` is a natural transformation; naturality of both adjunction maps
   and this boundary gives the asserted functorial triangle. No cone with
   arbitrary first or second maps is substituted. Rational and common-stage
   counit/unit fields retain the maps under coefficient passage.
4. `exceptional_open_zero` states `Ri! Rj* G = 0` as `IsZero` after the faithful
   full inclusion, and `exceptional_unit` states that the actual adjunction unit
   Q -> Ri! iPush Q is an isomorphism.

The extra `closedAdjunction : iPull ⊣ iPush` and
`openAdjunction : jPull ⊣ jPush` record the adjunctions of the already specified
operations, so that the maps in (3) have their prescribed meanings. Functors
are constrained by these universal properties and by the explicit canonical
operation comparisons; no arbitrary map is assumed, and no data is selected
from a mere nonempty existence statement.

### Finite-Tor clauses and bounds

The finite and integral `tor` fields quantify over d,c with the separate
hypotheses `(IsEmpty U ∧ d = 0) ∨ (Nonempty U ∧ topologicalKrullDim U = d)` and
`HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c`. The latter is the
recorded finite upper-bound encoding of torsion cohomological dimension. It
retains every allowed finite c; a larger upper bound gives the corresponding
larger interval. No finite-cd hypothesis is attached to (1)--(4).

- (1') `open_preserves` preserves the exact recorded finite-Tor constructible
  predicates. `open_interval` has output `[r,s + (2*d+c)]`.
- (2') `exceptional_preserves` preserves those predicates and
  `exceptional_interval` has output `[r,s + (2*d+c) + 1]`.
- (3') `closed_preserves`, `closed_pull_preserves`, `open_pull_preserves` and the
  respective three `..._interval` fields preserve the same endpoints. Together
  with (1') and (2') this places every vertex of the triangle in the full
  finite-Tor subcategory.
- (4') The zero and invertible-unit fields restrict to those full subcategories,
  since all the relevant functors preserve their predicates. Fullness means
  they are exactly the same zero object and isomorphism internally.

Finite interval tests are `HasProEtaleTorAmplitude` on intrinsic constant-ring
modules, not merely a stalkwise or etale-origin replacement. Integral interval
tests in `SfLocalizationIntegralInterval` demand the SAME ordered interval for
EVERY positive reduction; preservation uses
`finiteTorConstructibleIntegral`. At E and Qbar_l the dependency defines
`finiteTorFieldCoefficientCategory` as the original constructible category
itself, so (1)--(4) are precisely the field-stage finite-Tor assertions.

### Weil clause

`sfLocalizationAllStages_weil` uses the actual `FiniteFieldDatum D`, `l ≠ D.p`,
and finite-type objects X0,Z0,U0 over `Spec D.k₀`. Closed i0 and open j0 are
complementary before base change. `sfLocalizationFiberMap` is literally the
map of `Over.pullback (Spec.map (algebraMap D.k₀ D.k))`, so the PAIR, not only
the three individual schemes, descends. The rational and common-stage
pullbacks are fixed to these actual maps.

`SfWeilLocalization` is a lift into the dependency's `IsoAlgebra` categories
for the actual `sfWeilFrobeniusPullback` and
`sfCommonStageWeilFrobeniusPullback`. These are precisely `sfWeilComplex` and
`sfCommonStageWeilComplex`. The five underlying-functor equalities retain the
same operations and shift. Its two adjunctions lift the closed-exceptional
and open adjunctions. `counit_underlying`, `open_unit_underlying` and
`closed_unit_underlying` specify their actual underlying maps.
`boundaryLift` and `boundary_underlying` lift the SAME third arrow. Therefore
all three arrows and the unit are Weil-equivariant. No triangulated structure
on the category of fixed pairs is asserted or assumed.

### Dependency declarations used

- `Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement`:
  `Scheme.finiteRecollementDerivedAdjunction`, the existing canonical
  exact-inverse-image/right-derived-direct-image adjunction.

- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full
  category, exactly the recorded integral definition.
- `Sheaf.Paper.SfRationalizationKaroubi` (publicly available through the pullback
  module): `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the general category,
  `Stage`, `inclusion`, and the actual finite coefficient models.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `constructibleIntegralPullback`, `rationalDerivedPullback`,
  `commonStageDerivedPullback`.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfCompletedDerivedDirectImage`,
  `SfIntegralDirectImage`, `sfDirectImageTerm`,
  `sfDirectImageReductionComparison`; its public intrinsic finite image
  `Scheme.proEtaleConstantDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`:
  `ProEtale.sfFiniteExceptional`; the chosen compactification is the canonical
  `Compactification.ofIsProper i`.
- `Sheaf.Paper.FiniteTorAmplitudeProEtaleModule`: reexports the recorded intrinsic
  `finiteTorConstructible`, `finiteTorConstructibleIntegral` and field alias.
  The theorem uses the intrinsic category required by the dependency rather
  than copying the fixed-scalar presentation's predicate.
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`:
  `Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
- `Sheaf.Paper.SfWeilSheafComplex`: the actual rational/common-stage Frobenius
  functors, their `IsoAlgebra` fixed-pair categories, and `sfWeilPrimeInvertible`.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and `geometricFiber`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the existing coefficient
  ring and its positive-level finiteness, publicly imported by the finite
  exceptional and finite-Tor modules.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.

The module imports the published proof-dependency modules without `public`,
as required for the stage-3 plan, with the compatibility exception below. The full node proof plan is in the main theorem's
docstring. Its smaller integral-formula and Weil statements each have their
own source, blueprint tag and complete proof plan.

### Searches

- LeanFinder, query `closed immersion complementary open supported localization
  distinguished triangle exceptional inverse image all coefficient stages`:
  eight unrelated Mathlib hits (derived t-structure, truncation and scheme
  facts), no all-stage statement.
- Loogle, query `Triangle, Adjunction`: no hits; the service reported unknown
  identifier `Triangle`, so this did not establish an absence by itself.
- LeanSearch, query `closed support localization triangle derived categories`:
  eight generic derived-triangle/localization hits, no geometric all-stage
  operation statement.
- Mathlib grep through msearch, query
  `supportedLocalization|localization.*[Tt]riangle`: zero hits.
- Direct `rg` of the upstream and side `lean/Sheaf` sources for
  `localization_all|supportedLocalization|sfLocalization|LocalizationAll`:
  the upstream etale localization theorem and its downstream uses, no matching
  statement for the specified four coefficient categories and bounds.
- Direct `grep -rn prop-sf-localization-all-stages` of the upstream project:
  no declaration carrying this node.
- Read the full signature and docstring of upstream
  `AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`, in
  `WeilConjectures.SixFunctors.Etale.Derived.Localization`. It is an ordinary
  etale ambient triangle, with an ambient exceptional-adjoint instance. It
  does not state constructible preservation, the integral/rational/common-stage
  operations, their reductions, Tor bounds or Weil assertion. Hence it is a
  proof ingredient, not an exact existing match for this node.
- Searched all chosen new full names in Mathlib, the upstream project and the
  side Lean source: no name collision.

### Edge cases and self-check

Checked the empty open (d=0), empty closed part, empty X, the zero complex,
smallest positive coefficient exponent n+1=1, arbitrary positive exponents,
negative/zero/positive shifts, degenerate ordered intervals r=s, arbitrary
fields with the coefficient prime invertible, the finite-cd hypothesis only
where required, and an algebraic closure in an independent universe.
The inverse-limit tower and its projections use canonical reduction maps;
objectwise nonempty isomorphisms do not stand in for those maps. The Weil clause
uses morphisms over the finite field and their actual base changes.

No `STATEMENT-DISPUTED` or statement correction. No independent second reader
was started: the brief forbids starting other agents and reserves the
independent review to the maintainer.

Compilation: `scompile.py` passed the repaired module in both sandbox and final
library-path checks, with no warning or error. Delivery preflight is run through
`deliver2.py --no-push` before pushing.

### Saved-packet repair

The initial dry run failed because the proof-only module
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage` imports
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso`, which duplicates
`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv` from the finite-coefficient
`UpperLowerStar.Iso` already required by the statement dependencies. Omitted
that proof-only import: none of its declarations occurs in this statement.
The proof plan still cites `lem-weil-proetale-direct-image-restriction-of-scalars`;
its canonical comparison remains a stage-3 proof ingredient. No statement,
helper construction, node dependency or signature changed.

Self-check against the current node: only `lean` differs in the node copy;
the recorded main signature is verbatim, all variables and universes are bound,
all lines have at most 100 columns, and the three named theorems are exactly
the three postponed proofs.

The second dry run exposed the other legacy proof import,
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion`, whose
`LowerShriek.OpenImmersion.Complement` dependency imports the legacy
`fullyFaithfulOpenImmersionLowerShriek`. This collides with the finite-coefficient
`LowerShriek.Open.FullyFaithful` used by the statement dependencies. Removed
that direct legacy import; retained the already imported
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`.
Again no statement uses the removed legacy interface.

The common-stage record exceeded Lean's default elaboration heartbeat budget.
Diagnostics showed repeated unfolding of p-adic arithmetic and transported field
instances while checking each concrete stage comparison. Factored the identical
four functor comparisons and three adjunction-map equations into the generic
owning-node helper `SfLocalizationStageComparison`, now used by
`SfAlgebraicallyClosedLocalization.comparison L`. This retains precisely the
former closed/open push, exceptional, open pull, counit, open-unit and unit
fields, with independent universes for the two stages. No limit was raised,
no file was split, and no mathematical premise or conclusion changed.

## Second reading by Q64

Read the immutable item node and source place `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-localization-all-stages.md`, then checked the delivered module `Sheaf.Paper.SfLocalizationAllStages`. The main theorem signature renders every node hypothesis: prime `l` and `IsUnit (l : k)`, finite extension data for `E`, independent-universe algebraic closure `Ω`, separated locally finite type quasi-compact `X`, closed/open immersions with the complementary-range equality, and all variables and instances are bound. The `n + 1` finite coefficient index with `Nat.succ_pos n` covers exactly every positive level.

The four conclusion clauses are represented by the finite, integral, rational, and common-stage records. `SfSupportedLocalization` records the prescribed pullbacks, pushes, exceptional right adjoint, counit/unit triangle, natural boundary, uniqueness, orthogonality, vanishing, and exceptional unit. The finite-Tor record preserves the intrinsic predicates and intervals with shifts `2*d+c` and `2*d+c+1`; the integral interval requires one ordered interval uniformly at every positive reduction. Field stages use the recorded field/common-stage categories, so their finite-Tor clauses reduce to the constructible clauses. The integral exceptional Rlim theorem uses the actual reduction units, counit-normalized comparisons, and conjugated canonical transitions. The Weil theorem uses the actual finite-field geometric-fiber maps and fixed-pair Weil functors, retaining the same underlying arrows.

I checked all twelve statement dependency records and the exact declarations they provide, including the finite coefficient ring, intrinsic finite-Tor categories, completed direct images, exceptional inverse image, rational/common-stage pullbacks, cohomological-dimension bound, finite-field datum, Weil complexes, and `topologicalKrullDim`. The source proof steps and module docstrings cite the recorded blueprint places. Searches in the upstream and side Lean trees found no exact all-stage localization declaration; the ordinary etale supported-localization theorem is only an ingredient and does not cover the coefficient stages, Tor bounds, reductions, or Weil clause.

Edge cases checked: empty `U` with `d = 0`, empty closed part and empty `X`, zero objects, `n = 0` (level one), arbitrary shifts and degenerate intervals, algebraically closed `k` with `c = 0`, and independent `Ω` universe. Canonical residue-field transport supplies invertibility without extra scheme hypotheses. No unintended stronger assumption or dropped conclusion was found. The three remaining `sorry`s are exactly the named postponed theorem proofs (`sfLocalizationExceptionalLimit`, `sfLocalizationAllStages`, and `sfLocalizationAllStages_weil`); no local proof is supplied beyond `sorry`.

Per-file reproducibility: `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q64 prop-sf-localization-all-stages snapshot/lean/Sheaf/Paper/SfLocalizationAllStages.lean` passed the sandbox and library checks with no errors or warnings. No lake/global build, repository mutation, live Lean write, or branch-head change was performed. The only repair is this complete report replacement, adding the substantive second-reading record required by the maintainer gates; no Lean or node statement changes.
