## Worker report

The delivery states `WeilConjectures.CoefProjectionEvaluation.pairingFiniteNormalization`
in `Sheaf.SixFunctors.CoefPairingFiniteNormalization`. Its only postponed proof is
this theorem's `sorry`. Its docstring gives the complete six-step natural-language
proof: cartesian scalar reduction and Hom evaluation; unit/counit and strong-tensor
evaluation; open chain-map evaluation; scalar balancing; evaluation of the specified
system composite; transport by the recorded full-system Hom comparison.

The accepted item's mathematical statement, proof and proof dependencies are unchanged.
Two definition nodes expose the precise finite word and normalized comparison data.
They avoid a single overlong elaboration exceeding the prescribed 60-second limit.
No existence, invertibility, preservation of injectives, or reconstruction principle
is hidden in these definitions. All such witnesses are existential conclusions of
the item's theorem, for the already given system model and scalar specialization.

Clause-by-clause rendering:

* Prime ell and finite extension E/Q_ell: `(l : ℕ) [Fact l.Prime]`, `(E : Type u)` with
  `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The valuation ring and
  quotients are the existing `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionRing`, and `compactSupportSystemLevel`. Index `n : ℕ`
  always means exponent `n + 1`, so it covers exactly the positive exponents.
* The small pro-etale sites and ordinary unbounded module derived categories are
  `W.ProEt`, `ProEt.topology W`, `coefficientSequenceModules.{u,u}`,
  `coefficientSequenceDerived.{u,u}`, and `normalizedDVRDerived.{u,u}`. All scheme
  objects use universe u; finite sheaf carriers and morphisms use u+1 and their
  ordinary derived objects use u+2. No universe equality is imposed on a site's
  object and morphism universes. The fixed-size instance helpers choose the existing
  sheafification, local-bijectivity, monoidal, additive and Grothendieck structures.
* The actual quotient sequence ring, completed constant ring and scalar restriction
  square are the existing `coefHomScalarMap`, `coefHomPointScalarMap`,
  `coefHomPointRestriction`, `coefHomPointDerivedRestriction`, and the prescribed
  `ScalarSpecialization` of the system theorem. `restrictionEvaluation` is constructed
  from exact functor-composition localization comparisons of the same ordinary
  restriction/evaluation composite. It introduces no scalar-action choice.
* Derived sections take values in towers: `coefHomQuotientDerivedSections`,
  `coefHomPointModules`, and `coefHomQuotientPointModules`. There is no inverse limit.
  `finiteSections` is final-object evaluation followed by the actual sheafification
  unit's quotient scalar action; `finiteDerivedSections` is its right-derived functor.
* `k` is an arbitrary field, with `_hl : IsUnit (l : k)`. Both X and Y have `Over`
  structures over `Spec k` and locally-finite-type plus quasi-compact structure maps,
  precisely finite type. `a.IsOver`, `IsSeparated a`, `LocallyOfFiniteType a`, and
  `QuasiCompact a` render the separated finite-type k-morphism. `c : Compactification a`
  supplies the actual open immersion, proper map, and equation `c.comm`.
* The system `F` is `Model.support = CoefSupportOpenTensor.operation`; finite `F_n`
  is `finiteSupport = moduleJ.mapDerivedCategory ⋙ finitePush`. Proper image is
  derived after exact open extension, rather than deriving the whole composite.
* Arbitrary completed-coefficient K is a `DerivedCategory (scalarReductionSource ...)`.
  `s.reduced K` is the recorded derived scalar extension of actual constant K.
  `coefficientFiniteDerivedExtension` is K_n; `s.reductionEvaluation` and
  `s.reductionModel` retain the actual quotient transitions and reduction units.
* N is arbitrary `coefficientSequenceDerived`; it has no boundedness, flatness,
  constructibility, cartesianness or normalization assumption. `Model.hom`,
  `Model.h`, and `Model.b` are exactly D, h, b_M and b_N. Signed closed tensor-Hom
  data are the existing `SystemTensor.data`, `symmetry`, `signed`, and finiteClosed.
* `ScalarSpecialization.transported` is the already constructed beta_K,N. Its
  defining `comparison` is the whole-system scalar-Hom comparison, with the
  representative normalization supplied by that dependency. The delivery evaluates
  this map; it never chooses a system map using its finite values.
* `FiniteModel.beta` explicitly composes `balance`, quotient signed symmetry and
  `q`. `balance` explicitly composes the scalar projection mate with restriction
  of tensor(1, scalar counit). The ordinary scalar tensor is fixed by the equation
  sending x tensor_R y to x tensor_A y (`FiniteRestrictionTensor.pure`).
* `q` is the finite sections projection mate followed by derived sections of
  `Pi` and compact support of `v`. `Pi` is the proper counit-defined projection
  mate, then the actual `finiteGamma`, then the native pullback compositor and
  c.comm. This is exactly the ambient def-exchange-projection word, with neither
  projection mate inverted. `properTensor` transports the prescribed tensor
  comparison through the unique adjoint-compatible identification with native
  geometric pullback. The finite gamma is the existing `FiniteOpenModel` gamma,
  whose ordinary and chain normalizations are the sheafified pure-tensor map.
* `v` is tensor(1,t), signed symmetry, and finite closed evaluation. `t` is the
  sections pullback-composition comparison followed by the finite g_X counit.
* `FiniteEvaluation` contains the normalized exact evaluation/tensor isomorphisms.
  `TensorEvaluation.normalization` uses all complexes and universal localization;
  `SiteTensorEvaluation.pure`, `quotient_pure`, `integral_pure` fix ordinary tensor
  maps on the actual sections. `FiniteSiteTensor.totalComparison`, `total_pure` and
  `compatibility` relate the native total to the recorded K-flat tensor model.
* `SectionsEvaluation.sections` fixes the ordinary comparison on actual sections;
  `normalization` fixes its derived comparison by the two right-derived units and
  exact evaluation factors. It asks for no K-injectivity of finite evaluations.
* `FiniteEvaluation.hom` is asserted for every K,N. `hom_normalization` equates its
  hom with `coefficientBaseChangeHom`, the actual tensor-Hom transpose of evaluated
  closed evaluation. Thus the isomorphism cannot insert an arbitrary automorphism.
  `homComparison` composes evaluated full-system scalar-Hom comparison, restriction
  evaluation, sections evaluation, this Hom comparison, and the inverse-op of the
  reduction comparison in the contravariant first input.
* `quotientSupport` composes canonical proper/open evaluation with sections
  evaluation. `support` adds the exact scalar-restriction square; `reducedSupport`
  adds the actual K_n reduction comparison. These are the three displayed source
  and target identifications of the node, retaining their R and A_n actions.
* `FiniteEvaluation.gxUnit/gxCounit`, `gyUnit/gyCounit`, `rUnit/rCounit`, and
  `properUnit/properCounit` state preservation of the specified units and counits.
  `gxTensor`, `gyTensor`, `rTensor`, and `properTensor` state the commuting strong
  tensor squares. Substitution in the definition of `derivedProjectionFormulaMate`
  gives exactly its adjoint `(epsilon tensor 1) mu`, including the proper factor.
* `composition` and `pullbackComposition` are the actual sections and geometric
  pullback-composition equations. `gamma` is equality of the evaluated system
  gamma with the specified finite gamma under native open/pullback/tensor
  comparisons. `symmetry` and `xSymmetry` preserve the signed symmetries.
* `FiniteEvaluation.PairingEquation` says evaluation of `s.transported K N`,
  followed by support comparison, equals exact integral tensor evaluation,
  tensor of the Hom and reduced-support comparisons, then `FiniteModel.beta`.
  This is the displayed two-arrow finite formula in the node.
* `finitePointSectionsConvention` is an identity isomorphism to the existing
  `pointFiniteSections` at `Spec k`, using the recorded final-object convention.
  It applies in particular to the geometric finite-field point. The main theorem
  has no finite-field restriction, as the node is stated for every base field.

Dependency declarations read and used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the coefficient ring/integers API.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`;
  size convention is metatheoretic, not an extra Lean structure.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; completed coefficients and the
  constant-to-completion map enter through the recorded scalar specialization.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
* `Sheaf.Paper.CoefficientRingedSequenceSite`: `coefficientSequenceEvaluation`,
  `coefficientSequenceDerivedEvaluation` and the actual quotient sequence sites.
* `Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses` and
  `Sheaf.Paper.CoefficientRingedTensorHomModel`: the derived internal Hom,
  `CoefficientClosedStructure`, `CoefficientTensorModels`, `coefficientTotalTensor`,
  `coefficientTensorGenerator`, and `CoefficientTensorModels.iso`.
* Scheme morphism properties are the recorded Mathlib classes. The compactification
  is `Compactification` from `WeilConjectures.Compactification.RefinementCategory`.
* `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: the recorded native compact
  support, represented here by its strict moduleJ/proper-image composite.
* `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension` and its actual extension/restriction adjunction.
* `Sheaf.SixFunctors.CoefSystemProjectionEvaluation`: `Model`,
  `ScalarSpecialization`, `Model.beta`, `ScalarSpecialization.transported`,
  `SystemTensor`, and their normalized tensor/adjunction data.
* `Sheaf.SixFunctors.CoefHomTowerScalarModel`: `coefHomTower`,
  `coefHomQuotientSections`, point scalar maps, restriction, and exact point
  evaluation. `coefficientBaseChangeHom` comes from the recorded evaluation calculus.
* `Sheaf.Paper.CoefSupportOpenTensorModel` and its data imports:
  `CoefSupportOpenTensor.SystemOpenModel`, `FiniteOpenModel`, `systemGamma`,
  `finiteGamma`. The native `ProEtale.VaryingRing.evalG/evalP/evalJ` fix evaluation.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData`.
  `FiniteModel.Pi` writes the same uncurried proper-mate/open/compositor composite.
* `Sheaf.Paper.FiniteCoefficientPoint`: the finite fibre's final-object section
  convention, using `pointFiniteSections` from its actual imported scalar functors.
* Proof-only imports are the prescribed semilinear derived-sections, operations
  existence, systems existence, and open tensor normalization theorems.

Edge cases checked in the mathematical statement and the types: n=0 means A_1,
never the zero exponent quotient; K=0 and N=0 require no nonzero assumptions; empty
X and empty Y have the same terminal-object site construction; identity morphism
and identity compactification use native identity and composition comparisons;
R to A_n can be nonflat (all extension/tensor operations are derived). Arbitrary
unbounded K and arbitrary noncartesian N remain allowed. Only the scalar reduction
of K is cartesian when using internal-Hom evaluation. No finite-field datum or
separatedness of X and Y over k was added. No projection map is assumed invertible.

Searches for the item: msearch LeanFinder on evaluation of a derived coefficient
projection/evaluation pairing gave eight unrelated Profinite.Nobeling evaluation
hits; Loogle `CategoryTheory.Adjunction, CategoryTheory.evaluation` gave five
ordinary categorical adjunction/evaluation declarations; Mathlib grep
`evaluation.*[Pp]rojection|[Pp]rojection.*evaluation|[Ss]emilinear.*[Cc]ounit`
gave only LocallyConstant evaluation/projection. Project rg for the item and its
finite normalization found no exact declaration. Additional LeanSearch,
LeanFinder, Mathlib grep, project/DAG rg and blueprint searches for the new data
notions are recorded verbatim in their `mathlib_searches` records, including the
older downstream finite frame and the etale-only tensor comparison. No exact
existing full normalized finite pairing/evaluation package was found.

No STATEMENT-DISPUTED issue and no statement correction. No dependency replacement.

## New nodes

`def-coef-finite-projection-evaluation-data` owns
`Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData`: the actual finite module
operations, pure-tensor lax maps, universal adjunction/tensor data, explicit finite
projection/evaluation word, and normalized exact evaluation comparison interfaces.
Its formulas are precisely the source node's specified finite word (blueprint
paragraph 2 and Stacks 07A6/0B56). It asserts no existence. The searches above found
no owner or exact API: the old CoefPairingFiniteFrame omits these normalization
conditions and is attached to a downstream theorem. All definitions have real data.

`def-coef-finite-pairing-evaluation-data` owns
`Sheaf.SixFunctors.CoefFinitePairingEvaluationData`: the simultaneous finite
comparison package with pure tensor, unit, counit, strong tensor, composition,
signed symmetry, open gamma, and closed Hom evaluation equations. It builds on
the first new node and the already recorded system/Hom/open models. Again it is
a definition of witnesses, not an existence theorem. Searches found no equivalent
package. The old generic adjunction evaluation structure has mismatched category
universes; this delivery avoids copying that notion and spells out only the actual
specialized unit/counit equations inside this package.

## Second reading by NJ

The dispatcher forbids starting another agent; no independent worker was available.
This is a disclosed self-review, followed by the maintainer's independent review.
I reread the node, every displayed formula and the source paragraph against the
three modules. Corrected the contravariant Hom transport to use reduction.symm.op;
fixed the quotient point functor's codomain to retain the exact coefficient size;
added pure-total compatibility and signed-symmetry equations; replaced a duplicate
generic adjunction helper by the specialized unit/counit equations; and split the
definition interfaces into their own nodes/modules to respect the compile limit.
All quantified K,N are arbitrary; witnesses occur in the conclusion; no extra
mathematical hypothesis or weakened conclusion was introduced.

## Validation

All three modules compiled cleanly through scompile.py on the live server, within
the prescribed per-file limit (approximately 33, 44, and 8 seconds). The delivery
dry run printed OK at d1d778de1da: preflight passed and all modules compiled.
The only proof deferred in the delivery is the assigned theorem.

The helper `finiteIntrinsicSupport` explicitly identifies the native moduleJ/proper
composite with the dependency's `sfIntrinsicCompactSupport`, using the recorded
ordinary direct-image and adjoint-compatible open comparisons. Thus the native finite
word uses the same compact-support functor up to its prescribed canonical comparison.

## Repair of global-build return, 2026-10-24 UTC

1. The returned build of 119585a38b failed in
   `FiniteSectionsComposition.normalization`: instance synthesis could not find
   `(finiteSections l E Y n).Additive`. The existing
   `finiteSectionsAdditive l E Y n` already proves precisely this property. The
   repaired field applies `@DerivedCompositionNormalization` with its three module
   categories and the three existing additive witnesses explicitly:
   `finitePushAdditive l E a n`, `finiteSectionsAdditive l E Y n`, and
   `finiteSectionsAdditive l E X n`. This follows the existing explicit application
   in `SectionsComposition.normalization`. It changes no equation or hypothesis,
   adds no axiom or sorry, and prevents dependent instance inference from selecting
   or unfolding a different concrete functor presentation.

The dispatched sandbox was empty, so the packet was recovered read-only from
returned commit 67c36b6f2d1, then compared with the failed build commit 119585a38b.
The failed build contains the maintainer's additional signed finite point symmetry,
`FiniteSectionsComposition`, and its canonical left-adjoint composition. Those
review fixes are preserved; only the missing explicit instance arguments are repaired.
The node metadata was compared with current main and refreshed outside the worker's
owned fields. Delivery wrappers rebase the packet on current main. No direct Git
command or source-repository mutation was used.

Repair validation: scompile.py accepted all three delivered modules against current
server sources with no errors or unexpected warnings. The repaired projection-data
module compiled in 24.7 seconds, its evaluation-data consumer in 37.7 seconds, and
the main normalization module in 5.1 seconds. The consumer checks include the
maintainer's canonical finite composition and signed-symmetry additions.
