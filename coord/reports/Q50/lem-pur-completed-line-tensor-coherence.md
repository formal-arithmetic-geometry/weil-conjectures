## Worker report

The delivery states `lem-pur-completed-line-tensor-coherence` in
`Sheaf.Paper.CompletedLineTensorCoherence`, namespace
`WeilConjectures.CompletedLineTensor`. Definitions have actual data. Each postponed
proof is a named theorem in this node's module, with a source and a full proof
plan in its docstring. In particular, the ordinary comparison packages are chosen
from *unique*, fully normalized constructions; they are not arbitrary natural
isomorphisms obtained from a bare existence assertion. `tensor` specializes
Mathlib's exact-functor descent of the recorded ordinary sheaf tensor, rather
than introducing a second general derived tensor construction.

Hypotheses and clauses, in the order of the node:

- Prime and finite coefficient extensions: `(l : ℕ) [Fact l.Prime]`, each of
  `E`, `F`, `G : Type u` with `Field`, `Algebra ℚ_[l]`, and `FiniteDimensional`.
  The inclusions are algebra homomorphisms `ι`, `j`, and `j.comp ι`; field
  homomorphisms are injective, and identities are allowed. The site is exactly
  `X.ProEt`, with scheme universe `t`, object universe `t+1`, morphism universe
  `t`, and coefficient/module universe `max u (t+1)`. No equality between site
  universes is assumed.
- The valuation rings, uniformizers, completed coefficients, positive quotient
  towers, same-index quotient maps and strict termwise-product mapping cocones
  are the existing constructions in `FiniteFreeCompletedScalarComparison` and
  `IntegralScalarExtensionUniverses`. `integralTowerModules` is their actual
  module category and `DerivedCategory` their unbounded derived category.
  `completedDerivedScalarExtension` is B, `integralScalarExtensionOfUniverses`
  is C, and `completedScalarComparison` is the prescribed χ. No replacement
  completion or arbitrary ring map is introduced here.
- A line is `L : integralTowerModules ...` with
  `[L.IsFiniteLocallyFreeOfRank 1]`. Scalar line data are actual isomorphisms
  `changeOfRingsOfUniverses (completedCoefficientMap ...) L ≅ N`.
  `tower.hb` and `rational_tower.hb` express b20=b21(b10⊗1) on all local
  sheafified pure tensors, including arbitrary scalar factors. Local generation
  makes this equivalent to the balanced associator equation. The diagonal datum
  is multiplication; `rational_diagonal.hb` gives its section formula. The
  arbitrary repeated-field case retains its b, as explained under the correction.
- `power` gives the existing `scalarTensorPower` at nonnegative exponents and
  the existing `homObj` of the positive power into the actual coefficient unit
  at negative exponents. In particular 0 is R and 1 is L. `sheaf` is the existing
  `siteSheafTensorRight` specialized to this power; `complex` is its termwise
  cochain functor. `exact` states its additive exactness. `tensor` is
  `sheaf.mapDerivedCategory`, i.e. ordinary derived tensor by the flat line.
  There is no boundedness hypothesis. `factors` is the canonical exact
  localization factor, not an unspecified comparison.
- `pairing`, `evaluation_existsUnique`, `evaluation` and `epsilon` specify both
  the zero multiplication pairing and the positive/negative internal-Hom
  evaluation. The representative formula sends ((x⊗a)⊗b) to ev(a,b)·x.
  `epsilon` derives this very sheaf evaluation with Mathlib's canonical
  localization composition and identity factors.
- `PairData.line` and the first two conjuncts of `IsPairNormalized` pin the signed-power scalar maps.
  Nonnegative maps use the unique normalized binary comparison and tensor powers
  of b; negative maps satisfy exactly the evaluation formula with scalar factors
  s and t. In particular the zero comparison is multiplication and the first is b.
  The third conjunct of `IsPairNormalized` gives ((x⊗a)⊗s) ↦ (x⊗s)⊗b_m(a⊗1).
  `PairData.ordinary` is the natural ordinary derived isomorphism. The final normalization conjunct uses
  the actual universal K-flat counits and canonical exact localization factors.
  `comparisonComplex` applies the sheaf formula termwise. The normalization is
  written using HEq to avoid repeatedly expanding source and target functors;
  both sides have the same canonically specified endpoints, so it is the same
  equality. Applying any finite quotient gives the node's finite-projection
  formula, rather than choosing new finite-quotient comparison maps.
- `complete` states precisely preservation of the recorded unrestricted derived
  completeness predicate by every signed twist. `extension_complete` supplies
  completeness at intermediate scalar-extension inputs. `chi` inverts the
  recorded `completedScalarComparison` only using the finite-free comparison
  theorem at a complete input. `beta` is literally χ(TK)⁻¹, then bar-beta(K),
  then T(χ(K)), in Lean's chronological `≪≫` order. No chain inverse is asserted.
- `AssociatorData` with `IsAssociatorNormalized` fixes ordinary associativity by t⊗(s⊗x) ↦ t·j(s)⊗x and its
  universal counit normalization. `associator` is its stated conjugation by
  χ21,C10, B21(χ10), and χ20. `tower` states exactly the displayed three-field
  equation. `beta_natural_evaluation` contains both naturality on complete
  inputs and the displayed evaluation equation, with signs and order explicit.
- `ordinaryUnit` is uniquely fixed by the recorded chain multiplication unitor.
  `unit` is χii⁻¹ followed by that unitor. `unit_normalization` identifies its
  inverse on good representatives with the recorded direct completion unit,
  including its zero shifted-product component, and states naturality.
  `scalar_coherence` gives both unit laws and the four-field pentagon.
  `repeated` identifies scalar-normalized beta with the actual ordinary b-induced
  comparison. It never asserts a strict equality Cii=1.
- For rationalization the module uses the *recorded* constructible categories,
  which use the common coefficient/scheme universe convention `Y : Scheme.{u}`.
  `PreservesConstructible` is exactly the conditional preservation hypothesis
  for all integers. `integralTwist` is the full-subcategory lift of the ambient
  tensor, and `rationalTwist` is the actual `ScalarLocalization.map` of that
  functor. `integralTwist_linear` states preservation of the recorded coefficient
  action, which is needed to define that actual localization. `intrinsic_complete`
  identifies intrinsic complete constructible inputs with the completeness
  predicate used by χ, without adding completeness as a new hypothesis.
- `integralEpsilon`, `integralBeta` restrict the actual ambient components.
  `rationalEpsilon` and `rationalBeta` are uniquely pinned to the images of
  those integral components under `sfRationalConstructibleLocalization`.
  The auxiliary existing-API parameters p and hl:l≠p impose no condition on X
  or its characteristic (one can always take p=l+1); they are retained to use
  exactly the dependency's scalar functors. HEq in the rational component
  specifications transports the object equalities in the recorded functor's
  specification, whose objects are fixed propositionally rather than definitionally.
- `canonical_restriction` equates the completed associator/unit with the recorded
  integral scalar comparisons and their rationalizations with the recorded rational
  comparisons. `rational_tower` and `rational_evaluation` give the displayed
  equations on all rational objects, using those actual scalar functors.
  Their pentagon and unit laws are the existing `sfRationalScalar_coherence`
  for these same named associators and units. `rational_repeated` retains the
  localized b-induced line map after scalar normalization; identifying along
  it makes the comparison identity. `rational_diagonal` states the identity
  equation explicitly for the multiplication diagonal datum, for every rational
  object. The transported tower/evaluation equations follow from their stated
  equations, not from a strictification assumption.

Dependency declarations read and used:

- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-weil-derived-complete`: `Sheaf.Paper.DerivedCompleteOnSlices`, `WeilConjectures.IntegralOnSlice.IsComplete`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `def-weil-integral-scalar-extension`: `Sheaf.Paper.IntegralScalarExtensionUniverses`, `WeilConjectures.integralScalarExtensionOfUniverses`.
- `lem-weil-finite-free-completed-scalar-comparison`: `Sheaf.Paper.FiniteFreeCompletedScalarComparison`, `WeilConjectures.finiteFreeCompletedScalarComparison`.
- `def-pur-sheaf-tensor-product`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, `SheafOfModules.cochainModulesMonoidal`.
- `def-pur-sheaf-hom`: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, `SheafOfModules.homObj`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-rationalization-karoubi`: `Sheaf.Paper.SfRationalizationKaroubi`, `WeilConjectures.sfRationalConstructibleCategory`.
- `lem-weil-scalar-extension-composition`: `Sheaf.Paper.SfScalarExtensionComposition`, `WeilConjectures.sfRationalScalarComp`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`.
- `def-pc-sheaf-restrict-scalars`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, `SheafOfModules.restrictScalars`.

Further proof interfaces are imported by their recorded modules: K-flat resolution,
K-flat change of rings, independent-universe tensor descent, tensor-closed sheaves,
successive quotient normalization, equivalences preserving limits/colimits,
pro-etale countable-product exactness, derived-limit existence and intrinsic
constructible scalar extension. The proof-only line/unbounded-tensor node has no
recorded Lean module; the exact-specialization interfaces needed in this statement
are explicitly given here, with source and proof plans.

Edge cases checked before writing and again in the second pass: m=0 gives unit
multiplication, m=1 gives the original b, both signs use the correct internal-Hom
evaluation, K=0 needs no extra hypothesis, and the empty scheme is allowed.
The complexes are arbitrary unbounded complexes. Repeated coefficient fields
use the actual unit comparison even though their scalar functor is not strictly
identity. An arbitrary repeated-field line map can be nontrivial (the corrected
clause below). Ramified field maps use the existing same-index quotient maps;
no equality of uniformizers or étaleness of the ring extension is assumed.
Products are termwise products in the recorded mapping cocone; their completion
map is always the recorded quotient map with zero shifted component.

Searches for an existing match (run with the prescribed msearch wrapper):

- LeanFinder: “Completed scalar extension of sheaves commutes coherently with
  tensor by compatible invertible lines and evaluation”: free-sheaf and
  LightCondensed tensor hits; no completed derived tower/evaluation theorem.
- Loogle: `SheafOfModules, Functor`: no hits.
- Mathlib grep: `extendScalars.*[Tt]ensor|[Tt]ensor.*extendScalars`:
  ordinary `ModuleCat/Monoidal/Adjunction.lean` hits, not this statement.
- LeanSearch: “Derived tensor by an invertible module sheaf commutes with
  completed extension of coefficient fields and respects evaluation”:
  ordinary adic-completion tensor and invertible-module results, no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `completed.line|CompletedLine|LineTensor|lineTensor|signedPower|SignedPower`:
  found specialized integral-line/twist interfaces, read and reused their
  underlying constructions; none states the arbitrary compatible-line coherence.
- Exact node-ID search in `lean/WeilConjectures`: none. Search for
  `completedLineTensor|CompletedLineTensor` in `lean/Sheaf` and
  `dag/lean_names_upstream.json`: none before this delivery.

## Second reading by Q50

I made a separate second pass with the node, source and complete module open.
The dispatch brief explicitly forbids starting other agents, so this is a worker
self-review; the maintainer's independent review remains separate. I checked
all hypothesis and clause correspondences above, particularly the order of both
coherence composites, the m versus -m evaluation ordering, the same-index
quotient completion normalization, and the exact rational scalar-functor names.

The mathematical mismatch found was the arbitrary repeated-field identity claim:
scalar normalization alone cannot discard b. I corrected the node and final
proof step as below, and gave both the arbitrary-b formula and the diagonal
multiplication identity in Lean. Elaborator fixes made universe arguments and
source/target functors explicit; they introduced no new mathematical hypothesis.
No new definition nodes or dependency repairs are included.

## Statement corrected

The original node's final sentence asserted identity components for rationalized
beta at every repeated field after scalar-unit normalization alone. This is false
for the arbitrary compatible line data allowed earlier in the statement. Take
X a nonempty geometric point, all fields Q_l, all lines the coefficient unit, b10 multiplication by -1, b21
identity, b20 multiplication by -1, and diagonal bii multiplication. The cocycle
condition holds. At m=1 and the unit object, scalar-normalized rational beta10
is multiplication by -1, not identity. Here -1 is an integral unit for every
l, including l=2, and the rational coefficient field has characteristic zero.

The corrected final sentence retains that b-induced signed-line map, and asserts
identity after *also* identifying lines along it. The diagonal multiplication
case is already identity after scalar normalization. This is what the source
supports: blueprint main-20261015, sk-def-sp-tate-twist-locally-free Proof (3),
final sentence, uses the canonical compatible Tate-line identifications.
The full old statement is preserved verbatim in `statement_change.old_statement`;
the original full proof is preserved in `old_proof`, since its final step had the
same fault and is corrected accordingly. No statement dependency changed.

Citer audit used the prescribed exact-ID grep, then inspected stmt_deps/proof_deps:

- `det-def-sp-tate-twist-locally-free`: holds. Its canonical Tate-line comparison
  uses exactly the line identifications retained by the correction, so its inverse
  twist construction and coefficient conventions remain valid. It is not edited.

The exact old final sentence was: “Replacing each identity transition by the identity functor using its unit comparison gives a normalized diagram (identity transitions and associators with repeated adjacent fields are identities); the rationalized $\beta$ then has identity components at repeated fields and satisfies the displayed tower and evaluation equations for that diagram.”

The comparison product packages contain only maps; their full pure-tensor and counit
normalizations are separate Prop-valued definitions. The existence theorems
assert a unique package satisfying those predicates. Named projections are ordinary
product projections. This avoids expensive
automatically generated eliminators for long dependent proof fields without
removing any condition or splitting the delivered module.

- `lem-wf-tate-twist-compatibility`: holds. I read its entire statement and proof
  after server preflight identified it as a second current-base citer. Proof
  steps 4–5 supply the canonical compatible Tate-line b maps, multiplication
  at repeated fields, and use the ordinary bar-beta with the exact pure-tensor
  formula. The completed conjugate beta is explicitly not needed there. The
  corrected arbitrary-b clause retains the canonical diagonal identity and all
  these ordinary comparisons, so the scalar extension and strict Weil-pair
  compatibility argument remains valid. This citer is not edited.

The required clean compile succeeded in the delivery dry run; the first server
preflight then requested the additional citer audit entry above. Both current
base citers are now recorded as holds:true.
