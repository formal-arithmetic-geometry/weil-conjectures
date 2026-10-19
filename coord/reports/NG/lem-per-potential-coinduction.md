## Worker report

The delivery states `AlgebraicGeometry.Etale.potential_coinduction` in
`Sheaf.Paper.PotentialCoinduction`. Its sole proof is `sorry`. All seven supporting
declarations are real definitions for the canonical comparison in this node; none
chooses data from a mere existence theorem. There are no new nodes, dependency
rebindings, or changes to the mathematical statement.

I read the current live item, all three statement dependency records and their
recorded definitions/docstrings, and its five proof steps. The old interruption
note referred to Q42's stage-1 split, merged in the ledger at 18:22. The current
node has that reviewed split and no Lean record. This delivery supplies stage 2;
it does not split or replace Q42's work. The preserved sandbox initially contained
only dispatcher marker files, with no interrupted delivery to repeat.

Source checked: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Proposition the project server, printed page 294, including the coefficient-ring definition
and second displayed internal-Hom comparison. I read the PDF with pdftotext.
The node deliberately isolates the formal coinduction assertion from the
potential-dualizing assertion and places the result in unbounded D(R). The
resolution proof supplied by the node proves precisely that general assertion;
I did not reintroduce potentiality or the source's stronger displayed D+ ambient.

Hypothesis and clause correspondence:

- A prime ell: `(l : ℕ) [Fact l.Prime]`.
- Integers `1 ≤ s ≤ r`: `(_hs : 1 ≤ s) (hsr : s ≤ r)`. These imply r is positive
  and include s = r. No successor reindexing or identity quotient is omitted.
- R = Z/ell^r and S = Z/ell^s: the theorem specializes to
  `ULift.{u + 1} (ZMod (l ^ r))` and `ULift.{u + 1} (ZMod (l ^ s))`.
  ULift changes only universe size. There is one independent scheme universe u.
- The specified quotient map, rather than an arbitrary algebra structure:
  `(ZMod.castHom (pow_dvd_pow l hsr) (ZMod (l ^ s))).ulift`.
- X is any scheme: `(X : Scheme.{u})`, with no geometric hypotheses.
- The categories are the actual small-etale fixed-coefficient module-sheaf
  derived categories. `InternalCoinductionComparison` uses
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` and the corresponding
  B-category. These are the `DerivedCategoryModule` presentation of the recorded
  derived-categories node, not presheaves or ordinary modules.
- Restriction on M and on the right-hand object is the exact published
  `(Sheaf.restrictScalars X.smallEtaleTopology q).mapDerivedCategory`, called U.
  The general dependency `SheafOfModules.restrictScalars` is imported, and its
  constant-coefficient presentation is the existing upstream `Sheaf.restrictScalars`:
  on sections both retain the underlying module and act through q. No private
  definition of scalar restriction or change of coefficient category is made.
- K ranges over all D+(R) objects: PR is `DerivedCategory.Plus.ι` from that
  category. Likewise PS includes every D+(S) object M. Both appear in the
  domain of the final natural isomorphism.
- The S-linear K_s is defined by the existing
  `C := (coextendScalars q X).rightDerivedFunctor`, not by choosing a lift of
  an R-object or by an arbitrary action. Ordinary coextension is sectionwise
  Hom_R(S,F), with `(a φ)(b) = φ(ba)`; the published construction retains this
  action through a K-injective resolution. The second conjunct asserts
  `∀ K : DerivedCategory.Plus ..., ∃ n : ℤ, (C.obj K.obj).IsGE n`.
- The underlying identity with RHom_R(S_X,K) is the third conjunct, a natural
  isomorphism `PR ⋙ C ⋙ U ≅ PR ⋙ RHom_R(U(constantComplex S X), -)`.
  `constantComplex S X` is the published constant coefficient complex, so its
  restriction is exactly S_X[0] with its R-action.
- The internal-Hom comparison is the final natural isomorphism e, whose source
  at `(op M,K)` is `U RHom_S(M,C K)` and whose target is `RHom_R(U M,K)`.
  Its inverse has the orientation displayed in the node.
- Naturality in M and K is carried by one natural isomorphism of functors on
  `D+(S)^op × D+(R)`, not merely a family of unrelated object isomorphisms.
- Canonicity/evaluation at 1 is the component equality
  `e.hom.app (op M,K) = coinductionInternalHomMap q X μ M.obj K.obj`.
  That definition is the tensor-Hom transpose of the derived balancing map,
  followed by U applied to S-linear evaluation, followed by the counit of
  `(Sheaf.restrictCoextendScalarsAdj ...).mapDerivedCategoryRightDerivedAdjunction`.
  The ordinary adjunction's counit is h mapped to h(1), so its composite sends
  φ to evaluation-at-one composed with φ.
- The balancing map μ is existentially produced in the conclusion, with the
  predicate `CoinductionTensorNormalized` specifying its value on every cochain
  representative: on each tensor-total summand it is precisely
  `Functor.LaxMonoidal.μ (Sheaf.restrictScalars ...)`, followed by the summand
  inclusion. The displayed square commutes with the actual localization
  tensorators and restriction/localization comparison. K-flat B-representatives
  make the target comparison invertible, so these requirements determine μ.
  Thus there is no unconstrained comparison-map assumption.
- Both internal Homs have codomain unbounded D(R). Only C(K) is asserted
  bounded below. No constructibility, potentiality, upper bound, flatness of
  M or K, or finite Tor amplitude is required.

The helper definitions `coinductionCochainTensor`, `coinductionTensorInclusion`,
and `coinductionTensorRepresentative` specialize existing tensors, summand
inclusions and the localization tensorator. `CoinductionTensorMap` names the
comparison type; `CoinductionTensorNormalized` fixes it by its ordinary formulas;
`coinductionInternalHomMap` is the actual closed transpose; and
`InternalCoinductionComparison` packages the full assertion before specializing
A and B. These are owning-node helpers, not new independent mathematical notions.
Keeping the coefficient category abstract in the tensor helpers avoids the
concrete-module instance-comparison issue documented in the upstream
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure` module. The first
naive concrete formulation timed out; the final module compiles in seconds
without changing the timeout, adding hypotheses or suppressing warnings.

Dependency declarations and imported proof plan:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` reexports
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the fixed-coefficient encoding
  required by `def-weil-pbc-derived-categories`. D+ and its inclusion are
  `DerivedCategory.Plus` and `DerivedCategory.Plus.ι`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, the general ring-sheaf definition recorded
  by `def-pc-sheaf-restrict-scalars`; the constant-ring specialization used here
  is `CategoryTheory.Sheaf.restrictScalars` from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its publicly reexported
  ordinary-etale specialization `AlgebraicGeometry.Etale.derivedHom` and
  `derivedTensorHomAdjunction` (recorded in this dependency's declarations).
- `WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars`:
  `AlgebraicGeometry.Etale.coextendScalars`, and the existing right-derived API.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`.
- The proof-only imports retain all recorded proof dependencies:
  `CategoryTheory.homComplex` in `Sheaf.Algebra.Homology.HomComplex`;
  `SheafOfModules.homObj` in
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`;
  `CategoryTheory.quasiIso_homComplex_map` in
  `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`;
  `DerivedCategory.Plus.exists_injective_nonempty_iso` in Mathlib's
  `Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`;
  `AlgebraicGeometry.Scheme.etaleModule_enoughInjectives` in
  `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`; and
  `CategoryTheory.Adjunction.preservesKInjectiveComplexes` in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
  These are already imported transitively where needed but are listed explicitly
  as proof imports to retain the node's proof plan. No import cycle was found.

Edge cases checked before and after writing:

- s = r: the canonical quotient is the identity, ordinary coextension is Hom_R(R,-),
  and evaluation gives the usual identity comparison. This case is included.
- r = s = 1 and s = 1 < r: both the field case and nonflat coefficient quotient
  occur; no assertion that restriction preserves injectives is made.
- Empty X and zero complexes: the definitions and naturality remain meaningful;
  there is no nonempty, connected or Noetherian assumption.
- K bounded below but M unbounded above: Hom may be unbounded below, so both
  functors deliberately land in D(R). Their domain is still all D+ objects.
- l need not be invertible on X. The assertion is a formal module-sheaf adjunction
  and the Lean theorem imposes no such condition.
- s = 0 and r = 0 are excluded only by the exact stated 1 ≤ s ≤ r hypotheses.
- All variables and universes are explicitly bound; `autoImplicit` is false.

Searches made for an existing statement and for duplicate notions:

- msearch.py / LeanFinder: query "Internal derived Hom of sheaves comparison for
  restriction of scalars and coinduction along a coefficient quotient". Eight
  hits, including `PresheafOfModules.restrictHomEquivOfIsLocallySurjective` and
  `SheafOfModules.PullbackContinuous` infrastructure; no derived internal
  coinduction comparison.
- msearch.py / Loogle: query "coinduced, restrictScalars, derivedHom". Zero hits;
  `coinduced` was reported as an unknown identifier.
- msearch.py / LeanSearch: query "Derived internal Hom comparison with coinduction
  for restriction of scalars on sheaves of modules". Eight hits, including
  `SheafOfModules.restrictScalars`, `ModuleCat.restrictScalars` and representation
  coinduction adjunctions; no exact statement.
- msearch.py / grep: `coextendScalars|coinduction` in
  `Algebra/Category/ModuleCat`. Seven hits, locating the ordinary Mathlib
  coextension and its adjunction, which the upstream sheaf coextension uses.
- rg in the upstream WeilConjectures tree: `coinduc|Coinduc`,
  `coextend|Coextend`, and `restrictScalars`; found the sectionwise coextension,
  derived adjunction, ordinary fixed-coefficient restriction and generic internal
  Hom. These supply the canonical constructions but not this internal comparison.
- rg in lean/Sheaf: the same concept searches found ordinary-module
  `DerivedCoinductionAdjunction`, perfect-algebra tensor descriptions, ringed-space
  sheaf coinduction, and `PrimePowerHomTensorTest`. They have different statements
  and none is this small-etale two-variable internal comparison for all D+ M,K.
- rg for `lem-per-potential-coinduction` in upstream WeilConjectures: no declaration.
- Exact-name search in Mathlib, upstream WeilConjectures and lean/Sheaf for
  `CoinductionTensorMap|CoinductionTensorNormalized|coinductionInternalHomMap|potential_coinduction`:
  no existing declarations. The additional owning-helper names were checked against
  the same trees before delivery.

Validation: prescribed scompile.py compiled the final file both as a sandbox
module (6.9 seconds) and as `Sheaf.Paper.PotentialCoinduction` (7.8 seconds), with
no errors or warnings. All definitions have actual data; the only postponed
proof is `potential_coinduction`, with the full natural-language proof above it.
No STATEMENT-DISPUTED or new node fault was found.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
