## Worker report

The module `Sheaf.Paper.CompletedPerfectScalarPullback` states
`WeilConjectures.CompletedPerfectScalar.completedPerfectScalarPullback` and supplies
its explicit scalar models and normalized comparison interface. All theorem proofs
are `sorry`. Definitions contain constructions, never `sorry` data. Helpers belong
to this node's scalar-model, strict-tower and balanced-tensor calculations; they are
listed in `lean.declarations` and carry this node's blueprint/source docstrings.
No statement correction, disputed statement, new independent notion, or dependency
record repair is made.

Hypotheses and objects, with the node and source open:

- A prime ell is `(l : ℕ) [Fact l.Prime]`; the finite extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  `Scalars` is the harmless ULift of the recorded integer ring. The actual quotients
  use `Padic.coefficientExtensionRing l E (n+1)` and the recorded uniformizer.
  A different chosen uniformizer generates the same powers of the maximal ideal;
  this fixes the standard quotient presentation without restricting the scalar datum.
- `X Y : Scheme.{t}` represent V' and V, and `g : X ⟶ Y` is arbitrary.
  `_hX` and `_hY` require ell to be a unit in every local ring, exactly invertibility
  on the two schemes. There is no Noetherian, qcqs, proper, smooth, nonempty, or
  finite-dimensional hypothesis on the schemes.
- Completed coefficients are the existing
  `completedIntegralCommRingSheafUnrestricted` / underlying RingCat limit, with
  `integralConstantToCompletionOfUniverses` and its actual projections.
  `scalarMap` merely changes the commutative presentation using the faithful
  forgetful functor. `constant` is constant module presheaf sheafification with
  respect to that constant ring sheaf, so is the standard constant module sheaf.
- `Complex` retains the specified cochain complex, all degrees, differential and
  chain maps. `IsModel` is the termwise hypothesis on that representative: bounded
  support (`IsZero` outside some c,d) and `Module.Finite` plus `Module.Projective`
  in each degree. It is deliberately not a predicate allowing replacement by a
  different representative. `DerivedCategory.IsPerfectRingComplex`, the recorded
  dependency, instead existentially forgets the representative. Its finite/projective
  and bounded representative clauses are written out here because the node explicitly
  keeps this representative and differential. This does not define another notion
  of perfect derived object.
- `modelModules`, `model` and `derivedModel` are ordinary extension of the constant
  module, its actual cochain functor, and its image under `DerivedCategory.Q`.
  Their ordinary scalar-change functors come from the published universal derived
  change-of-rings pair, whose `obj_eq` specifies the sheafified ordinary tensors.
  That choice retains a universal counit and does not choose an arbitrary object
  from an undetermined existence statement.

Every conclusion and normalization:

- `Reductions` and `ModelReductions.reduction` give ordinary chain isomorphisms at
  every finite level on both schemes. `derivedReductionIso` uses the actual
  universal resolution comparison and `model_good` to give the first displayed
  *derived* tensor isomorphism. `ReductionFormula` is precisely
  a tensor (b tensor x) mapped to a pr_n(b) tensor x on arbitrary local sections.
- `quotientTower` has the restricted finite scalar complexes as its levels.
  `TransitionFormula` fixes its conjugated transition to the ordinary quotient on
  sheafified pure tensors, hence it is the node's quotient tower, not an unrelated
  tower with those objects. `ModelReductions.naturality` covers every original
  scalar chain map. All comparisons are chain isomorphisms, so preserve the
  specified differential; no degreewise splitting replaces that differential.
- `pullbackIso` uses the existing `integralDerivedPullbackComparison` on the good
  representative. It then applies the actual Roos functor to `Comparisons.tower`.
  Composing with `target.limitIso` is exactly the second displayed pair of
  isomorphisms. `FinitePullComparisons.formula` fixes each finite map on the
  constant-section coefficient generators; `tower_evaluation` fixes all components
  of the single strict tower isomorphism to these finite comparisons. Its
  naturality equations include all consecutive quotient transitions.
- `limitUnit` is the real mapping-cocone lift of the product of ordinary quotient
  maps with second coordinate zero. `limit_unit` fixes the inverse limit comparison
  to its derived image, and `projections` identifies *every* derived-limit projection
  with the ordinary quotient map. This extra unit normalization prevents arbitrary
  automorphisms invisible on a collection of unrelated projections.
- `LimitNaturality`, `FinitePullComparisons.naturality` and `pull_natural` impose
  naturality for every chain map of the stated bounded finite-projective complexes.
  The maps of strict towers and Roos complexes used there are actual functor maps.
- `complete` is the existing `IntegralOnSlice.IsComplete` predicate on these
  derived objects. The strict reduction-tower `integralDerivedPullback` is the
  Lg* specified in the node. Its completed interpretation on this complete input
  is the existing integral/completed comparison (imported as the proof plan), not
  an assumption of coefficient-map invertibility or of an arbitrary lift.
- `cohomologyIso` gives the canonical comparison for *each* integer j, with
  `P.homology j` exactly H^j(P). It is constructed from
  `DerivedCategory.homologyFunctorFactors` and `(P.sc j).mapHomologyIso`, so is the
  actual cycles/boundaries comparison. `modelModules_exact` supplies only the
  source scalar-ring flatness used in the node's step 7.
- `directMap_existsUnique` fixes the completed ring morphism by *all* finite
  projection equations. `ordinaryPull` is its module direct image's universal
  left adjoint, together with `ordinaryAdjunction`; that universal pair determines
  the tensor inverse image canonically. `ordinaryGenerator` is the adjunction unit,
  i.e. 1 tensor g inverse x. `OrdinaryComparison.iso` is natural for all R-modules N,
  hence applies to every H^j(P). Its forward and inverse equations are respectively
  b' tensor (b tensor n) mapped to b'g-sharp(b) tensor n, and b' tensor n mapped to
  b' tensor (1 tensor n). Linearity, locality and sheafification extend these
  generator equations to balanced tensors.
- `Amplitude` quantifies a,b with a ≤ b and every integer j outside that interval.
  It assumes vanishing of the *source cohomology*, not support bounds on P, and
  concludes vanishing of target cohomology. There is no flatness hypothesis on
  B_target over the inverse image of B_source anywhere in the theorem.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionRing`,
  `Padic.finite_coefficientExtensionRing` (and the coefficient constructors it imports).
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`,
  `integralConstantQuotientOfUniverses` and the completed limit/projections it imports.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  ordinary module sheafification is `PresheafOfModules.sheafification`.
  The existing `commutativeSiteConstantModuleFunctor` restricts coefficients to
  max(site-object,site-morphism); this delivery's same sheafification construction
  permits independently larger coefficients and the retained small site.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` supplies the representative convention;
  `Module.Projective` and `Module.Finite` render its termwise hypotheses as explained.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory.standard`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` and its retained original
  `IntegralDerivedOperations`: `WeilConjectures.integralDerivedPullback`,
  `integralDerivedPullbackComparison`, `integralOperationsLevelPullback`,
  `integralOperationsRoosFunctor`, `IntegralOnSlice.IsComplete`.
- `Sheaf.Paper.PbcQbarCompletedPullback` retains the underlying completed-pullback
  modules publicly. The Qbar specialization is not substituted for integral Lg*.
  `Sheaf.Paper.IntegralPullbackCompletedComparison` is the comparison proof dependency.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleBaseChange` and
  `coefficientProEtaleDirectRingMap` from its coefficient framework.
  The general `sheafPushforwardContinuous` avoids specializing the coefficient
  universe to the site universe; its adjoint gives the same pro-etale inverse image.
- The updated recorded cohomology interface is Mathlib's
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
  `IntegralReductionTowerWellDefinedUnrestricted` supplies
  `unrestrictedTowerResolutionIso`, `unrestrictedTowerUnit`, the finite tensor
  sections, actual reduction functors and consecutive quotient transitions.

All stated proof-dependency modules are imported as the stage-3 proof plan,
including flat/K-flat, finite perfect coefficient limit, exact countable products,
strict Roos comparison, constant-module inverse image, ordinary tensor comparison,
completion equivalence and constant-module exactness. The main docstring records
all nine proof steps; the helper theorem docstrings give their specific arguments.

Edge cases checked mathematically before and during transcription: the zero complex;
a single shifted finite projective; a nonfree finite projective summand (no basis is
required); the two-term complex R --pi--> R (its torsion cohomology is not assumed
projective); a representative with wider support than its cohomological amplitude;
identity and arbitrary morphisms; empty schemes; and every positive quotient,
including exponent one (`n=0`). No faithfulness or nonempty-site argument is used.
The coefficient-field universe u and scheme universe t are independent, and the
small pro-etale site keeps object universe t+1 and morphism universe t. Named
wrappers make Roos normalization opaque during subsequent elaboration without
changing any mathematical definitions or raising compile limits.

Searches: the prescribed msearch LeanFinder query was "Completed perfect scalar
complexes over the completed constant integral coefficient sheaf pull back canonically
under an arbitrary scheme morphism, preserving finite reductions and cohomological
amplitude". Eight hits concern ordinary structure-sheaf pullback and do not state
this lemma. Loogle query "CategoryTheory.constantSheaf, Module.Projective,
DerivedCategory.homologyFunctor" returned zero combined matches; the earlier
single constantSheaf query found the standard sheafification functor used here.
Mathlib grep `completed.*[Pp]erfect|[Pp]erfect.*[Ss]calar` returned six unrelated
perfect-pairing/perfect-field hits. Project rg for `CompletedPerfectScalar` and
`lem-a1-completed-perfect-scalar-pullback` found no declaration; broader constant
module/perfect pullback searches led to the imported framework modules. The
upstream declaration-name catalogue has no same name. No existing theorem has
all the strict tower, tensor-formula, cohomology and amplitude clauses of this node.

Source checks: read Bhatt--Scholze 6.5.9(4)--(5) and 6.6.11, and the local Stacks
sites-modules.tex `lemma-completion-flat` (093M). The scalar-model calculation is
valid on arbitrary schemes: the qcqs or Noetherian hypotheses needed elsewhere in
the paper's constructibility theory are not required for this bounded scalar model.

## Second reading by Q101

This is the worker's explicit second pass with the node and Lean file open; the
dispatched brief assigns independent review to the maintainer and prohibits spawning
another agent, so this section does not claim an independent worker's review.

Checked the full correspondence above against every paragraph of the node. Fixed
three transcription/interface defects during the pass: the finite transition's
section map needed an unambiguous parenthesized application; the Roos projection
needed its source type stated explicitly; and the single large record was split
into finite-reduction and limit-normalization structures to stay within the fixed
compile limit. The quotient-unit normalization, all-projection equations, naturality,
original differential and balanced inverse formula were retained. The scalar-model
hypothesis is now named `IsModel` to distinguish it from the imported perfect-object
predicate, which forgets the specified representative. Every theorem proof remains
`by sorry`; proof obligations used in definitions are separately named theorems.
No new node or dependency module needs review. The sandbox vanished during the
interrupted compilation loop and was restored from the inspected draft; no delivery
had run at that point and the live node had no Lean record.
