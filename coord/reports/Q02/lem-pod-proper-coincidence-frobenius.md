## Worker report

Repair of the returned immutable head 8f75559cb4da. The saved Lean work contained a
partial repair but its report and node binding still described the rejected
existential statement. This packet retains those canonical constructions, checks
them against the current dependencies, and replaces the stale report and binding.
The module is `Sheaf.Paper.ProperCoincidenceFrobenius`.

The hypotheses are rendered as follows. `D : FiniteFieldDatum.{u}` supplies exactly
the finite field, cardinality, chosen geometric algebraic closure and inclusion.
`Y₀ : Over (Spec (.of D.k₀))` and `[IsProper Y₀.hom]` supply the proper model;
properness implies its finite type and separatedness. `D.geometricFiber Y₀` is the
recorded geometric fibre, and its `.hom` is the structure map to `Spec D.k`.
The properness instance on that map is obtained by base change, not assumed.
`l : ℕ`, `[Fact l.Prime]`, `[Fact (l ≠ D.p)]` are precisely the coefficient-prime
conditions. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
`[FiniteDimensional ℚ_[l] E]` give the finite extension. The finite, integral and
rational formulas do not use an embedding into a closure and apply in particular
to every finite subextension in the node. The algebraically closed case uses
`Ω : Type v` with `[Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]` and its
recorded finite coefficient fields, without identifying u and v.
The finite exponent is `n + 1` for `n : ℕ`, covering precisely all n >= 1 of the
node, including exponent one. Inputs are respectively the full subcategory
`intrinsicFiniteTorsionConstructible`, `sfIntegralConstructibleCategory`,
`sfRationalConstructibleCategory`, and
`generalAlgebraicallyClosedConstructibleCategory` at the geometric fibre.

The compactification is fixed in every construction to
`Compactification.ofIsProper Y₀.hom`. There is no arbitrary compactification
binder. `properFrobeniusCompactification_eq` identifies its retained geometric
base change with `Compactification.ofIsProper (D.geometricFiber Y₀).hom`.
This equality concerns the actual records, including the base-change conventions;
its named postponed proof is the identity-compactification calculation of Step 1.

The named canonical comparison is constructed before point fibres or cohomology.
`properFrobeniusFiniteComparison` changes that equal record, applies the existing
adjunction-normalized `sfIntrinsicDerivedOpenId`, and the functor left unitor.
`properFrobeniusSystemOpenId` cancels identity open extension on whole derived
coefficient systems by its specified adjunction and
`integralComparisonSystemUnit`. `properFrobeniusIntegralAmbient` uses
`FrobeniusExchange.compactRealization` and then that system comparison before the
total coefficient limit. `properFrobeniusIntegralIso` restricts the resulting
natural isomorphism to the full constructible categories.
`properFrobeniusRationalIso` is uniquely specified by localization of every
component of this integral comparison. The `existsUnique` specification fixes
all components; its use of choice never selects an unspecified Nonempty iso.
`properFrobeniusQbarComparison` is the same-stage class of this rational iso.
The common-stage source and target natural comparisons are uniquely specified
by `commonStageDerivedPullback.map` of this very named comparison and by
this comparison at `commonStageDerivedPullback.obj K`, respectively. Thus their
naturality concerns all common-stage morphisms, including scalar enlargement.
These are helper declarations of the comparison explicitly requested in the
return, all recorded in `lean.declarations`; they are not new independent notions.

Each of the four theorems (`properCoincidenceFrobeniusFinite`,
`properCoincidenceFrobeniusIntegral`, `properCoincidenceFrobeniusRational`, and
`properCoincidenceFrobenius`) states the same three conjuncts:

1. Clause 1 is `Lg_s^*(κ_M) ≫ FrEx_* = FrEx_! ≫ κ_(Lg_Y^*M)` in Lean's
   left-to-right composition convention. The finite ordinary exchange is the
   recorded `finiteExchange`; `properFrobeniusFiniteExchange` is exactly the
   `finiteCompact` expression and canonical inverse-image coordinate changes in
   `frobeniusCompactTransportFinite`. The integral and rational exchange helpers
   unfold to `modelExchange` and `modelRationalExchange` for the recorded direct
   or identity-compactification model. The Qbar helper unfolds to
   `commonStageExchange`; its two comparisons have the actual corresponding
   `stageAction` source and target, with specified representative components.
2. Clause 2 at the complex level is
   `Fib(κ_M) ≫ τ_M = τ_c,M ≫ Fib(κ_(Lg_Y^*M))`. The two maps on the left and
   right are `.1` and `.2` of the existing
   `frobeniusCohomologyTransportFinite`, `...Integral`, `...Rational`, and
   `frobeniusCohomologyTransport`. Point-comparison helpers are `mapIso` under
   the existing point fibre. At Qbar they are the recorded exact coefficient
   extension of the finite-stage rational point comparison, exactly as in the
   transport definition. The pulled-input comparison always uses `Lg_Y^*M`;
   the transport's target is RΓ(Y,Lg_Y^*M), with no Weil structure assumed.
3. `∀ i : ℤ` gives the node's degreewise consequence by mapping those point
   comparisons with the same cohomology functors as the recorded
   `frobeniusCohomologyMapFinite`, `...Integral`, `...Rational`, and
   `frobeniusCohomologyMap`. The two Frobenius maps are those declarations'
   components, never new quantified endomorphisms.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.Paper.FrobeniusGeometricExchange` and its imported
  `FrobeniusSquareExchange`: the actual `galois`, `finiteExchange`,
  `finiteCompact`, `modelFunctor`, `modelExchange`, `modelRationalFunctor`,
  `modelRationalExchange`, `stageAction`, `commonStageExchange` and
  `compactRealization` constructions. The geometric model wrappers are exactly
  the recipes retained by the transport declarations.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`: all four transport and
  induced-map declarations, and its retained compactification/model definitions.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`: the inherited ordinary/compact
  cohomology and the geometric point `sfWeilCohomologyPoint`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointIntegralFibre`,
  `pointRationalFibre`, the finite section functor and common-stage fibre calculus.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `Sheaf.Paper.SfCommonStageDirectImage`: the recorded ordinary derived-image
  interface `sfModelDerivedPush`; the exchange's direct branch uses the ordinary
  completed coefficient tower realization of that operation, as prescribed by
  the recorded transport API. No arbitrary direct-image functor is introduced.
- `Sheaf.Paper.ProperCompactCoincidence`: `properCompactCoincidence`, whose bare
  Nonempty interfaces are insufficient to name κ; this delivery constructs its
  specified identity-compactification comparison explicitly.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, and the recorded finite intrinsic pullback.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`, inherited through the canonical realization
  used by the exchange construction.

Proof imports retain `FrobeniusPointTransportNatural`,
`IntrinsicCompactSupportRestriction`, and `SemilinearDerivedSections`. The proof
plan is exactly the node's four steps: cancel identity extension at finite level;
cancel it on whole simultaneous coefficient systems before total limit, then
localize and descend; use point-transport naturality for the complex square;
apply cohomology. Every theorem is postponed by `sorry`. Definitions have real
data or take the object uniquely fixed by an explicit universal specification.

Edge cases checked: exponent one; every integer cohomological degree; the zero
complex; the empty proper scheme; the proper point; arbitrary constructible
complexes without a Weil structure; an independent algebraic-closure universe;
and identity/repeated coefficient-stage enlargements. No equation identifies M
with its Frobenius pullback, and no smoothness or connectedness is imposed.

Searches: `msearch.py leansearch` with "proper compact support ordinary cohomology
canonical comparison Frobenius compatibility" returned only compactly supported
functions and test functions, no cohomological comparison. The retained packet's
searches and the repeated `msearch.py` LeanFinder
query "proper compact support ordinary cohomology comparison commutes Frobenius
exchange" returned group-cohomology functoriality and Shapiro lemmas only.
`msearch.py loogle CategoryTheory.NatTrans.naturality` returned generic categorical
naturality, not this comparison. `msearch.py grep
proper.*[Ff]robenius|[Ff]robenius.*proper AlgebraicGeometry` returned zero hits.
`rg` in the upstream `WeilConjectures` and current `lean/Sheaf` found ordinary
Frobenius exchange components and `WeilSheaf/Finiteness.lean`; its theorem is only
existence of an equivariant Qbar Weil-cohomology isomorphism, not the two specified
exchange/transport squares on all four coefficient categories. No exact existing
statement was found. The source read is the current main-20261015
`prop-cohomological-finiteness.proof.md`, Step 6, together with the DAG's explicit
four-step expansion. No mathematical statement correction is needed.

## Second reading by Q02

This is the dispatcher's single-worker self-check, not an invented independent
worker review; the maintainer performs the independent review after delivery.
I compared the current node, saved work and recorded dependency definitions.
The saved report and node record still bound the rejected existential theorem;
they are replaced. Long generated lines were wrapped to the project limit.
The saved repair now has an explicit named Qbar comparison before pullback, in
addition to its normalized source, target and point comparisons.
The four theorem declarations each include clause 1, the complex-level clause 2,
and its all-integer-degree consequence. In each case the Frobenius maps are the
landed exchange and transport maps. The compactification is the fixed identity
compactification over k₀, retained by base change. Canonical comparisons come
from identity-open cancellation, localization and specified same-stage classes;
none is an arbitrary per-degree iso. The old `STATEMENT-DISPUTED` note described
an interface omission repaired by these constructions and is removed.

## Dependency modules

`def-weil-derived-pullback-tensor-hom`: two dry runs and the explicit file check
failed before compiling the consumer, at the published
`Sheaf.Paper.DerivedPullbackTensorHom` module's 60-second overlay limit.
The dependency repair preserves every declaration and construction verbatim,
locally making the existing cached finite-stage category instance reducible
during elaboration. Profiling identified repeated eta comparisons of this
instance with the underlying rational category as the compile cost. The local
attribute introduces no instance, declaration, assumption or mathematical change.
Its node changes only in `lean`, with the required explanation. The same
mathematical operations and canonical maps remain in use.

The final retry rechecked the saved packet against the current published node
and source. It retains every requested repair: named canonical comparisons, the
fixed identity compactification, both compatibility clauses, all four coefficient
cases, and transports to the Frobenius-pulled input. The dependency compile repair
changes elaboration only; no mathematical statement or definition is weakened.


The resumed dry run exposed a published-overlay elaboration mismatch rather than
an incorrect direct-image recipe: `#print` confirms that `modelFunctor`,
`modelRationalSource`, and `modelRationalTarget` are marked irreducible in the
compiled dependency. Their existing definitions are made locally reducible while
this module elaborates; no operation, comparison, or global attribute is changed.
The integral ambient comparison now checks against exactly the recorded
`modelFunctor` branches. Pullbacks on the geometric fibre receive the actual
`properFrobeniusFiberPrime` instance explicitly, since matching the unfolded
pullback scheme cannot reconstruct the finite-field datum during instance search.
These are inherited units, with no additional invertibility hypotheses. Added
source docstrings and declaration records for the six saved structure instances.
Refreshed the dependency node from the current DAG, preserving all fields other
than its authorized `lean` repair.
