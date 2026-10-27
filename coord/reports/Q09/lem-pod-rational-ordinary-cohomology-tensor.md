## Worker report

The delivery adds `Sheaf.Paper.RationalOrdinaryCohomologyTensor`, namespace
`WeilConjectures.RationalOrdinaryTensor`. All definitions have actual data; the only
postponed proofs are `naturality` and `rational_ordinary_cohomology_tensor`. The node's
statement, dependencies and accepted proof are unchanged.

The module retains the derived isomorphism `ordinaryDerivedComparison` as well as the
per-degree E-linear isomorphism `ordinaryComparison`. Both are compositions of the
recorded point normalization and exact-functor comparisons, not arbitrary maps or
unspecified isomorphisms. In particular, `derivedComparison` uses
`pointRationalNormalization` and the inverse of `pointFibreRationalDownIso`.
`cohomologyComparison` applies exact scalar/homology comparison and the homology of
that derived comparison. Its codomain is the recorded rational coefficient cohomology,
with the recorded carrier lift. The domain is the recorded integral cohomology
extended along `pointIntegralToField`. Its E-first coordinates correspond to the
statement's H-first tensor product by the canonical tensor commutor. Restricting
coefficients by `pointFibreCoefficientDown` identifies ULift E with E without changing
the carrier or action. No new cohomology theory or coefficient sheaf is defined.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| p,a,q,k0,k and their relations | `D : FiniteFieldDatum.{u}` |
| prime ell different from p | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` |
| finite E/Q_ell, V, uniformizer, positive finite quotient conventions | `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; V is `Padic.coefficientExtensionIntegers l E`, and its recorded uniformizer and quotient rings are inherited unchanged |
| separated finite-type k-scheme | `Y : Scheme.{u}`, `Y.Over (Spec (.of D.k))`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on the structure arrow |
| s=Spec k, f the structure map | `Spec (.of D.k)`, `Y ↘ Spec (.of D.k)` inside `integralImage` |
| small pro-etale sites, completed coefficients | the `sfIntegralConstructibleCategory` and recorded `integralImage` use those exact sites and `scalarReductionSource`; the completed coefficient is never replaced by the discrete constant sheaf |
| K in D^b_c(Y,V) | `K : sfIntegralConstructibleCategory l E Y` |
| K_E its raw rationalization | `sfRationalConstructibleLocalization`, used by `cohomologyComparison`; `rationalImage` at this input is the same rationalized `integralImage` |
| integral and rational ordinary cohomology | `ordinaryComparison` specializes `cohomologyComparison` to `integralImage D l hl E Y K`; its domain and codomain unfold respectively to the recorded `integralOrdinaryCohomology` and lifted `rationalOrdinaryCohomology` of K_E |
| every integer i, E-linear isomorphism | `ordinaryComparison ... i` is an isomorphism in `ModuleCat E`; the theorem explicitly asserts `∀ i : ℤ, IsIso ...hom` |
| any complex representing the integral point complex | `C : CochainComplex ... ℤ`, `e : Q.obj C ≅ ((pointIntegralFibre ...).obj L).obj`; no boundedness is imposed on C |
| cycle z in ker d^i | `z : LinearMap.ker (C.sc i).g.hom`; this is Mathlib's short complex centered at i |
| tau([z] tensor lambda)=[z tensor lambda] | `CycleFormula`: `cycleClass` is kernel inclusion into cycles followed by `homologyπ`; `tensorCycleClass` uses `mapCyclesIso.inv` and the same quotient after actual termwise tensor. `integralCoordinates` and `rationalCoordinates` transport these to the recorded groups |
| naturality in integral coefficient morphisms | `naturality L M h i` states the full square for every integral point-image morphism h, with rational map exactly `pointRationalFibre.map (sfRationalConstructibleLocalization.map h)`. Apply it to the direct image of any integral coefficient morphism. It is not confined to chain maps or objectwise comparisons |
| K=completed constant coefficient, degree zero and lambda=1 | the last conjunct specializes to `integralCohomologyCoefficient ...`, `C.sc 0`, and `ULift.up (1 : E)` |
| arbitrary degree-zero class e and unit | every class is in the image of `homologyπ`; the last conjunct quantifies over every cycle z. It therefore includes every degree-zero class and in particular the coefficient section 1. The right side uses exactly the rational point normalization, so for the integral unit it is the specified rational unit |
| no connected/proper/smooth/H0 hypothesis | none occurs in the signature or any helper |

Dependency declarations read and used (module abbreviations below all start with
`Sheaf.Paper.` unless explicitly qualified):

- `FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, full structure with p prime,
  exponent positivity, cardinality, finite base field and fixed algebraic closure.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension`: `Padic.finite_coefficientExtensionRing` and the recorded
  integers, uniformizer and quotient constructions.
- The scheme-properties node is explicitly a convention collector. Its intended
  classes are Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`;
  the full category definition is the weakly-etale over category.
- `SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory` (derived completeness, constructible reductions
  and one uniform amplitude interval).
- `SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`; raw scalar localization, no Karoubi completion.
- `SfDerivedDirectImage`: `SfIntegralDirectImage`, its object, projection and Roos
  triangle, as used by `integralImage`.
- `FiniteCoefficientPoint`: `pointIntegralFibre`, `pointRationalFibre`,
  `pointFibreCoefficientDown`, `pointRationalNormalization`,
  `pointFibreRationalDownIso`; read their full signatures, object-map normalization
  and docstrings. The coefficient-down comparison uses the specified pure-tensor map.
- The currently recorded ordinary-cohomology module is
  `CommonStageCompactWeilCohomology`, imported publicly. Its public imports retain
  `OrdinaryCompactCohomology`: `integralImage`, `integralOrdinarySections`,
  `integralOrdinaryCohomology`, `rationalImage`, `rationalOrdinarySections`,
  `rationalOrdinaryCohomology`, `integralCohomologyCoefficient`.
- `CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; the limit lift of the quotient cone,
  publicly inherited through the actual coefficient constructions.
- Proof imports: `SfIntegralDirectImageConstructible.sfIntegralDirectImage_constructible`,
  `SfStrictDirectImageScalarComparison` (the recorded
  `SfStrictDirectImageScalar.strictDirectImageScalarComparison` and its
  `IntegralModel.linear` interface),
  `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr.Padic.extension_integers_dvr`,
  Mathlib `IsLocalization.flat` (Flat/Localization.lean:37),
  `Module.Flat.lTensor_exact` and `rTensor_exact` (Flat/Basic.lean:323,340), and
  the inherited `DerivedCategory` localization.
- Exact homology transport reuses
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryHomologyFunctorIso` (line 263), including its
  representative formula (line 292). Cycles use Mathlib
  `ShortComplex.moduleCatCyclesIso`, `mapCyclesIso`, `homologyπ`.

`moduleDerived` re-registers the exact existing
`HasDerivedCategory.ofIsGrothendieckAbelian` construction at the point targets'
recorded Hom universe; it constructs no alternative localization. This is necessary
because public importing the strict-image proof module activates its competing
module-localization priority. Every derived comparison explicitly specifies the
recorded localization universes. No hypothesis identifying two universes is added.

Edge cases checked mathematically: the empty scheme and zero complex give the
unique zero-module isomorphism; a disjoint union of two points is permitted without
identifying its H0 with V; Y=Spec k gives the exact point comparison; i may be negative;
a complex representing a bounded object may itself be unbounded; torsion cohomology
(such as the two-term complex V --varpi--> V) becomes zero after tensoring, as does its
rational cohomology. Unit normalization needs no H0 computation. No statement fault
or STATEMENT-DISPUTED flag was found.

Searches actually run using `msearch.py Q09 lem-pod-rational-ordinary-cohomology-tensor`:

- LeanFinder: "Flat scalar extension commutes with ordinary pro-etale cohomology
  naturally sending cycle tensors to tensor cycles"; semantic hits do not supply the
  pro-etale ordinary comparison.
- LeanFinder: "Rational ordinary cohomology integral point fibre cohomology tensor
  fraction field natural cycle map"; returned group-cohomology cycle maps and field
  lemmas, not this statement.
- LeanSearch: "Cohomology of a cochain complex commutes with an exact additive
  functor"; returned Ext functoriality and complex maps, no exact match.
- Loogle: "Functor.mapHomologyIso, ModuleCat.extendScalars" and
  "Module.Flat, TensorProduct"; no exact pro-etale ordinary comparison (the latter
  returns flat tensor injectivity/linear-independence lemmas).
- Mathlib grep: `mapHomologyIso|preservesHomologyOfExact` in Algebra/Homology;
  six hits, giving the existing exact-functor homology machinery used here.
- `rg` in WeilConjectures and Sheaf for rational cohomology and tensor/cycle
  terms, and the item id; found the point normalization and exact-functor APIs,
  not an exact declaration of this node. Grep of the upstream-name index and
  Mathlib/WeilConjectures/Sheaf for the new namespace and main name had no hits.

Sources opened: Milne PDF printed p.126, "Sheaves of Q_l-modules"; local Stacks
algebra.tex `lemma-flat` (00HD) and `lemma-flat-localization` (00HT); the current
blueprint `latest/` point-evaluation entry and cohomological-finiteness proof.
The blueprint now has its newer condensed coefficient presentation; this delivery
preserves the live DAG's explicit integral/rational point interface, as instructed.

Validation: the final module compiled through scompile.py in both sandbox and
library module modes with no warnings or errors. The earlier universe diagnostics
were repaired before delivery. No local/global Lean build was run.

## Second reading by Q09

Reopened the node and completed module and matched each hypothesis and clause in
the table above. The finite-field datum, prime inequality, finite extension and the
three structure-morphism properties are present. The raw localization and completed
coefficient object agree with their recorded dependencies; neither uses a discrete
replacement. The E-linearity is in the ModuleCat target after coefficient descent,
and H-first versus E-first tensor coordinates differ only by the canonical commutor.
Checked that `rationalCoordinates` includes the same `derivedComparison` as the map
being characterized and that the right side is an actual tensor-cycle quotient,
not a definition using the left side. The source and target homology factorizations
have the correct directions. Naturality uses the specified rationalization on h;
the last conjunct is at zero and scalar one on the constant object. It covers any
representative, so changing the representative by a quasi-isomorphism is included.

This second pass added the explicit `ordinaryDerivedComparison` so the derived
comparison is retained as requested by the project's complex-isomorphism convention,
and changed the public ordinary-cohomology import to its current recorded module
`CommonStageCompactWeilCohomology`. Recompiled after these changes: clean.
This is the dispatcher's single-worker rereading; the maintainer performs the
independent review of the delivery. No other agent was started.
