## Worker report

The delivery states all three clauses of `lem-per-tate-twist-lisse-line` in
`Sheaf.Paper.TateTwistLisseLine`. Its recorded declarations are one interface:
`perTateTwistLisseLine` and `perTateFiniteSystem` give the finite/lisse assertions;
`perTateInverseLimit` gives the prescribed inverse limit;
`perTateIntegralTensor`, `perTateRationalTensor`, and `perTateCommonTensor` give the
ordinary/completed and finite/common-stage tensor assertions. Auxiliary declarations
construct the actual objects or specify the coefficient comparisons used in these
assertions. Each postponed theorem has its source and natural-language proof.
No item statement, dependency list, proof, or proof dependency is changed.

The primary source was read at https://arxiv.org/pdf/1309.1198: Corollary 5.1.5,
Definition 6.8.3, Proposition 6.8.4(1), Proposition 6.8.11(3), Proposition 6.8.14,
and Remark 6.8.15. The current blueprint's smooth-pullback proof says that the
Tate twist is lisse of rank one. The node's four proof steps are retained in the
finite-system, limit, coefficient-comparison, and tensor docstrings.

Hypotheses and objects:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Scheme: `(X : Scheme.{u})`. The relevant assertions retain `[IsNoetherian X]`
  and `[X.IsSeparated]`; the PBC and common-stage assertions also retain
  `[hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]`.
  Some finite-system auxiliary assertions are valid without the dimension bound.
- Ell invertible on X: `[hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]`.
  The public `pbcTwistResidueInvertible` supplies exactly the residue-field form
  used by the tensor and lisse interfaces. The lisse membership theorems explicitly
  include hInv even when their object expressions themselves do not require it.
- Algebraic closure: `(Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]
  [IsAlgClosure ℚ_[l] Ω]`, with w independent of the scheme universe.
- Finite field inside Ω: `F : Padic.FiniteCoefficientFields l Ω`; the prescribed
  `pbcFiniteField.{u} l Ω F` is its canonical Shrink model, related to F by
  `Shrink.algEquiv ℚ_[l] F.val`. Integral assertions also allow arbitrary
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- Integer twist: `(m : ℤ)`, with no sign restriction.
- Integers, uniformizer, and quotients: `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, `Padic.coefficientExtensionIdeal`,
  `Padic.coefficientExtensionRing`. The diagram's index n represents the node's
  positive index n+1; no degree-zero quotient is added to the system.
- Finite etale Tate sheaf: `perTateFiniteEtale l X E n m` is exactly
  `finiteEtaleTateSheaf` with coefficients `ULift A_(n+1)` and `N=l^(n+1)`.
  `perTateAnnihilator` states the required zero equation for this N, including
  ramified E. The ULift is only the public finite-sheaf API's coefficient size.

Clause 1, hypothesis by hypothesis and assertion by assertion:

- The transition is the published `completedReductionModuleTower`, applied to
  the actual signed `pbcTateLineSheaf`, followed by constant-scalar restriction.
  `perTateEtaleTower` applies the recorded comparison lower star to this diagram.
  These are actual functors; neither an arbitrary family of maps nor a choice of
  an unspecified inverse system is used. The upstream integral root line has the
  root-power transitions; signed coefficient twists retain tensor powers and duals.
- `perTateFiniteSystem` identifies each level with `perTateFiniteEtaleIntegral`,
  the original finite Tate sheaf with its integer-ring action. Its local-cover
  clause is an etale Cover and an isomorphism to the constant A_(n+1) module
  sheaf on every slice, expressing local constancy and rank one.
- `IsLisseIntegralDiagramOfUniverses` gives finite local constancy, quotient-ideal
  annihilation, and surjective geometric-stalk transitions with kernel the
  appropriate uniformizer power times the source. The original lisse dependency
  uses exactly this conservative-stalk rendering of the reduction tensor
  isomorphism. Together with the fixed quotient-tower transitions, it expresses
  the displayed reductions, including the inverse dual base change for m<0.
- `perTateLisseIntegral` is the actual full-subcategory object with that tower;
  its proof component is the named lisse membership theorem.
- `perTateTwistLisseLine` asserts a `Module.Basis (Fin 1)` of every integral
  geometric fibre, using the same inverse-limit fibre construction as the
  dependency. `perTateRationalTensor` asserts finrank Ω = 1 after extension along
  the actual `pbcFibreCoefficient` integer inclusion. This is the fibre of the
  rational lisse model (E,T_E tensor E) extended to Ω, rather than an assumed
  one-dimensional auxiliary vector space.
- `perTateLisseModel` explicitly constructs the pair of its finite field and
  its lisse integral system. Rationalization keeps this integral representative,
  as in the recorded lisse rational-object definition, and extends its morphisms.
  `perTateStageLine` rationalizes exactly the degree-zero realization of that line;
  `perTateCommonLine` is the pair with that finite stage. For every F and G,
  `perTateRationalTensor` gives their isomorphism in the actual common-stage
  category. `perTateCommonTensor` retains the integral-normalized scalar
  comparisons, their repeated-field units, and their tower equation, identifying
  these finite models through the canonical coefficient comparisons.

Clause 2:

- `ProEtale.comparisonUpperStar` is the comparison nu-star. In
  `perTateFiniteSystem` its value on the named finite etale Tate sheaf is
  isomorphic to `perTateFiniteProEtale`, the recorded finite signed pro-etale line
  with its A_(n+1) action.
- `perTateComparison` is the actual comparison adjunction counit on the whole
  quotient diagram, and its components are IsIso. Because this is one natural
  transformation, compatibility with every transition is part of its type.
- `perTateQuotientUnit` is the actual ordinary scalar-adjunction augmentation
  from the completed line to each quotient. Its named naturality theorem gives
  `perTateQuotientCone`, with exactly that line as point and those maps as legs.
  `perTateInverseLimit` asserts `Nonempty (IsLimit perTateQuotientCone)`. This is
  the universal property of the specified inverse limit; it avoids selecting an
  unrelated cone or assuming nu-star commutes with an infinite limit.
- `perTatePbcLine` has the literal degree-zero underlying PBC line.
  `perTateCommonTensor` identifies its rationalization, under the normalized
  category comparison, with `perTateCommonLine`. Its object is thus precisely
  the lisse line realized in degree zero at the specified finite field.

Clause 3:

- `perTateIntegralTensor` retains ordinary K-flat total tensor T, its localization
  comparison e, its quotient chain comparison chi, and the descended map tau.
  The pure-tensor equations and zero second Roos coordinate specify the
  canonical ordinary-to-completed map, rather than an arbitrary isomorphism.
  For every integral K, this very tau is IsIso; the ordinary product and the
  literal exact termwise twist are derived complete. The functor isomorphism
  with `integralSheafTwist.mapDerivedCategory` expresses naturality in K.
- `perTateRationalModel` is uniquely fixed by its composite with the recorded
  integral localization, so both objects and all localized morphisms are fixed.
  `perTateRationalTensor` intertwines the literal `pbcTateRational` functor with
  `rationalDerivedTensor` fixing the right input to `perTateStageLine`.
- `perTateScalarMap_eq` identifies the two published presentations of the same
  completed coefficient inclusion. `perTateIntegralScalarModel` is uniquely
  normalized by the actual `purScalarModel` followed by
  `sfIntegralOrdinaryComparison`, including the equality transport between these
  two coefficient-map presentations.
- The coefficient spelling equality `perTateStageCategory_eq` retains both
  category structures. Its eqToHom transport only relates the same canonical
  small field in the two APIs; no universe equality is imposed.
- `perTateCommonTensor` uses the concrete specialization `perTateCommonModel` of
  `StageSystem.coefficientPairFunctor_exists` on the actual
  quotient with the specified integral scalar normalization and coherent tower
  equation. It is an equivalence. The statement then supplies a twist functor U
  whose object function is exactly `pbcTateTwist` and whose restriction to each
  finite stage is exactly `pbcTateRational`, including morphisms. Finally it
  states a natural functor isomorphism `U ⋙ T ≅ T ⋙ tateTensorRight
  (commonStageDerivedTensor l Ω X) (perTateCommonLine ... F m)` for every finite
  model F of the line. The published coefficient-twist API supplies only the
  common-stage object function; this extension states its natural tensor meaning
  without replacing that function or its finite-stage arrow action.

Dependency declarations read and used:

| Node / module | Declaration or interface |
| --- | --- |
| scheme conventions / Mathlib scheme properties | `Scheme`, `IsNoetherian`, `Scheme.IsSeparated`, `topologicalKrullDim` |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | `Padic.finite_coefficientExtensionRing` and reexported integer, ideal, uniformizer, quotient definitions |
| `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf` | `Scheme.finiteEtaleTateSheaf` |
| Mathlib small etale site | `Scheme.smallEtaleTopology`, `Scheme.Etale`, `etalePrecoverage` |
| `Sheaf.Paper.LisseAdicSheaves` | `AdicIntegralDiagram`, `IsLisseIntegralDiagram`, `LisseIntegralSheaf`, rational/algebraic model definitions |
| `Sheaf.Paper.LisseAdicFiberFunctors` | `lisseIntegralFiberFunctor` and underlying integral-fibre definition |
| Mathlib geometric points | `Spec`, field and `IsAlgClosed`, `pointSmallEtale` |
| `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` | `proEtaleSiteComparison`, `comparisonUpperStar`, `comparisonLowerStar`, `comparisonAdjunction` |
| `Sheaf.Paper.PbcCoefficientTwists` | `pbcTateLineSheaf`, `pbcTateAmbient`, `pbcTateRational`, `pbcTateTwist`; signed `coefficientTwistLine` |
| `Sheaf.Paper.PbcQbarCategory` | `pbcQbarCategory`, `pbcStageCategory`, `pbcStageLocalization`, `pbcScalarSystem` |
| `Sheaf.Paper.DerivedPullbackTensorHom` | `rationalDerivedTensor`, `commonStageDerivedTensor`, integral completed tensor and normalized scalar comparisons |

The relevant proof interfaces are also imported: finite etale line, locally free
integral twist and explicit signed line, exact comparison pullback, module-pullback
tensor comparison, integral-category characterization, finite-free scalar completion,
PBC scalar extension, and constructible tensor completion. `prop-weil-twist-preserves`
has no usable recorded declaration; no assumption of that theorem is added to the
statement. The required membership and coefficient compatibility are stated explicitly
as the item's sourced companion assertions.

Edge cases checked against the source and definitions:

- n=0 means the first positive quotient A_1. There is no accidental A_0 system.
- Ramified finite extensions: ell = unit times varpi^e, e≥1, so ell^(n+1)
  annihilates A_(n+1), though its exponent need not be the minimal annihilator.
- m=0 gives the coefficient unit; m=1 is the root line; negative m uses the
  recorded dual rather than a positive-only substitute.
- The empty scheme has no geometric points; fibre statements are vacuous, while
  the zero sheaf satisfies the local and limit assertions and [0,0] bounds.
- Disconnected schemes are allowed; neither connectedness nor a chosen point is
  assumed. The Tate root construction supplies the same finite field globally.
- Arbitrary complexes K, zero complexes, and shifts are included; there is no
  sheaf-only or degree-zero restriction on the tensor input.
- Identity coefficient extensions and repeated stages are retained by the
  specified unit comparison and tower equation; different finite models of the
  line are compared at common finite stages.
- Scheme and algebraic-closure universes remain independent. ULift and Shrink
  are canonical coefficient transports, not equal-universe hypotheses.

Searches (prescribed msearch queries are logged in searches.jsonl):

- LeanFinder, `Tate twist sheaf is a rank one lisse l-adic sheaf and twisting is
  tensor with it`: eight condensed module tensor/local-constant results, no match.
- LeanFinder, `Tate twist rank one lisse sheaf tensor product`: eight condensed
  tensor or Picard-group results, no match.
- LeanSearch, `Tate twist rank one locally constant l-adic sheaf`: eight condensed
  local-constant results, no match.
- Loogle, `finiteEtaleTateSheaf, LisseIntegralSheaf`: no hits; those side-project
  identifiers are unknown to the Mathlib search index.
- Mathlib grep, `TateTwist|Tate.*lisse|Lisse.*Tate`: no hits.
- rg of WeilConjectures and lean/Sheaf for Tate/lisse names found
  `WeilSheaf.isLisse_tateTwistSheaf`. Its complete signature and construction were
  read: it assumes a scheme over a finite field and gives a lisse Weil sheaf with
  cyclotomic Frobenius structure. It does not state this arbitrary-scheme finite
  quotient, comparison, rank, or common-stage tensor assertion.
- The upstream search for the item's exact blueprint identifier has no match.
  The side project supplies the dependencies listed above, but not this statement.

No statement dispute or item-node correction was needed. All compilation and
preflight validation use only the authorized scompile.py and deliver2.py wrappers.

## Dependency modules

`def-pod-lisse-l-adic-sheaves` receives a lean-only interface repair in
`Sheaf.Paper.LisseIntegralSmallCoefficients`. The old integral interface requires
`E : Type (u+1)`; the actual recorded PBC stages use `pbcFiniteField : Type u`.
The new interface renders exactly the old inverse-system criterion and integral
full subcategory for these small finite fields, with module universe u+1 retained.
The quotient ideal is definitionally the original span-uniformizer power. The
inverse-limit integral fibre uses the same geometric-point functor. The
Grothendieck-abelian structure is transported through the canonical ULift ring
scalar equivalence with an actual proof and real data. Public import retains the
original rational and algebraic lisse interfaces and operations. No data is sorry,
no private alternative coefficient ring is introduced, and no closure/site universe
equality is required. Every other field of the dependency node is unchanged.

The final common-stage elaboration treats the published chosen stage system as locally
irreducible, with the transparency override scoped to that attribute command. This
prevents repeated expansion of the complete witness during dependent Hom elaboration;
it does not change any transition, category structure, coefficient universe, or statement.
The tensor-completion interface retains its normalized existential witness instead of
repeatedly projecting its large nested proof. Compilation limits were not raised.

Validation: the two modules compiled cleanly through scompile.py, including final
module-name compilation; no warnings other than the authorized sorry warning were
reported. The universal-property limit, named coefficient-stage equality transport,
and locally opaque comparison functors avoided the initial elaboration timeouts
without raising any compiler limit. The final model helper is checked again by
the delivery dry run.

The delivery dry run returned `OK`: commit 2524bc91e6 passed the maintainer's
server preflight and per-file compilation. Both node deltas were checked to change
only `lean`; all recorded signatures are verbatim source substrings, and every
module line is at most 100 characters.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
