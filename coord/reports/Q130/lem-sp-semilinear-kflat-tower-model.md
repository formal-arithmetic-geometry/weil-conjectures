## Worker report

This delivery states `AlgebraicGeometry.ProEtale.sp_semilinear_kflat_tower_model`
in `Sheaf.Paper.SemilinearKFlatTowerModel`. Its only postponed proof is that theorem.
`HasSpSemilinearKFlatTowerModel` packages its conclusions with real Prop-valued data;
`HasSpSemilinearCompletedLift` packages its completed-ring clause separately to
keep elaboration within the file limit. Both are helpers for this same statement;
it does not choose representatives, morphisms or functors from an existence claim.
`spSemilinearCompletedProjection` is a real helper construction of the actual
completed-ring quotient: preimage under the fully faithful forgetful functor of
the unique completed limit comparison followed by the nth limit projection.
This proof-determined unique comparison is already allowed by the node dependency;
no arbitrary existence witness is chosen. Isolating the helper prevents expensive
unfolding of the coefficient sheaves during elaboration.
`spSemilinearChainTransition` similarly names the actual termwise strict transition,
with its full source and restricted target; this shares its type during elaboration.
`spSemilinearEvaluationIso` names the canonical evaluation comparison followed
by evaluation of the one tower isomorphism, shared by both predicates.
The source is the preliminary coherent-tower realization in the current
sk-lem-sp-tower blueprint proof, with the explicit seven-step proof in this DAG node.
The module docstring repeats that proof for stage 3. No statement correction,
new independent notion, or dependency-interface repair is needed.

Hypotheses and clauses, individually:

* Prime ell is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  The scheme is `(T : Scheme.{t})`; `t` and `u` are independent.
* O is the existing `Padic.coefficientExtensionIntegers l E` inside the recorded
  coefficient ring tower. B is `spCoefficientCommRings l E T`, which retains
  the commutative structure of `spCoefficientRing`. Index n means exponent n+1.
  R is `completedIntegralCommRingSheafUnrestricted l E T`, with its actual
  quotient projections `rho n` from `sp_completed_coefficient_limit`.
* The ambient abelian tower category is the original `spCoefficientTowers`.
  D is the `SpCoefficientTowersAbelian` interface guaranteed by its recorded
  theorem, including exact evaluations and canonical ordinary/derived reductions.
  It is a presentation of that category and its maps, not a new mathematical
  hypothesis. `C` is in its ordinary unbounded derived category using D.hasDerived.
* Existential P is a complex in this tower category and a is `Q.obj P ≅ C`.
  Its evaluated complexes are `Qn n`; the displayed `e n` is the inverse exact
  evaluation factorization followed by the evaluated a, so it has source Q(Qn n)
  and target the original derived evaluation of C.
* `∀ n, systemLevelKFlat B n (Qn n)` is exactly independent-coefficient K-flatness
  and `∀ i, IsFlatOnSite ((Qn n).X i)`, by the existing definition.
* `beta h` is termwise D.ordinaryReduction and `q h` is
  `spSemilinearChainTransition`, the termwise `strictSystemTransition` whiskered
  with D.equivalence.functor. The normalized
  ordinaryReduction_eq identifies beta with its scalar-adjunction transpose.
  The first square equates localized q, restriction factorization and
  Res(e_m) with e_n followed by the derived adjunct of the original reduction.
  This adjunct is the original semilinear transition, by D's normalization.
* By its actual definition, every q_(n,m), in every degree and on every site
  object, is the original transition of the strict tower P. Those strict
  transitions satisfy identity/composition; this includes all longer composites
  and m=n, rather than just the adjacent transitions.
* The pure-tensor equation is `beta(c tensor x) = c • q(x)` using the dependency's
  `systemModelTmul`. The explicit `@id` gives the result its original B_m-module
  type; `ModuleCat.smul` explicitly uses that module's own B_m scalar action,
  since the restricted target otherwise exposes only the B_n action.
  This is the paper's x tensor b formula with the existing scalar-first convention.
* For every m≤n the universal counit on Qn n is asserted invertible and the
  displayed square identifies its localized beta, followed by e_m, with
  derived tensor of e_n followed by the ORIGINAL `(D.reduction h).app C`.
  This is the K-flat computation of the canonical derived reduction, not an
  arbitrary isomorphism or tensor map.
* U is an existential exact additive functor to strict R-module towers. `hU n`
  requires its entire level functor (objects AND maps) to equal exact evaluation
  followed by actual scalar restriction Res n. Its additional HEq equation
  fixes every horizontal transition sectionwise, so the underlying sheaf,
  scalar action, every morphism and every transition are prescribed.
* UP is the termwise image under U. `b` is the inverse localization comparison
  followed by D(U)(a), an actual isomorphism from Q(UP) to D(U)(C) in the derived
  category of strict R-towers. The evaluation equation uses the canonical exact
  composition isomorphisms to identify its evaluations with the SAME e_n after
  restriction. No uniqueness of b is claimed.
* The final equation is projection naturality for b after total derived inverse
  limit. It is quantified over its universal derived pair RF,eta and the actual
  derived evaluation presentation V,epsilon. Each `pi n` is a natural projection
  RF to the nth evaluated level; the first Roos-triangle arrow composed with
  product projection is exactly such a transformation by the recorded strict
  tower homotopy-limit theorem. The equation holds for every n, so it in
  particular gives all the projections specified by that theorem.

Dependency declarations used (module suffixes below refer to Sheaf unless Mathlib
or WeilConjectures is written explicitly):

* `Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`, `spCoefficientRings`,
  `spCoefficientRing`, `sp_completed_coefficient_limit`; full declarations read.
* `Paper.SmoothPurityCoefficientTowersAbelian`: `spCoefficientCommRings`,
  `spCoefficientEvaluation`, `SpCoefficientTowersAbelian` and all its normalization,
  reduction and exactness fields; full structure and proof docstring read.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, the unchanged underlying sheaf with restricted action.
* `Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
* `Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
* `CategoryTheory.SystemLevelLeftExtensionBasic`: `systemLevelKFlat`,
  `strictSystemTransition`, `systemRestriction`, `systemDerivedTensor`, `systemTensorAdj`,
  `systemDerivedTensorAdj` and the strict-system transition identity/composition.
  Its already-landed node is added to stmt_deps for these exact shared notions.
* `CategoryTheory.SystemScalarModel`: `SystemScalarModel` and `systemModelTmul`
  from `def-weil-pbc-system-scalar-model`; its normalization specifies both adjunctions.
  This definition node is cited in stmt_deps; no model is chosen from the scalar-model
  existence theorem. Derived localizations use `HasDerivedCategory.standard` from
  `def-weil-abstract-derived-category`.
* `Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel.ε` and `.computes`, the canonical K-flat counit.
* `CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`, including its universal
  pair, evaluation factorization, natural first arrow and product projections.
* `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategory`, `mapDerivedCategoryFactors`, `mapDerivedCategoryCompIso`,
  `mapDerivedCategoryNatIso`.
* The proof imports the recorded `DiagramSiteTopology`, `RingedToposMorphism`,
  `KFlatResolutionIndependentCoefficients`, `KFlatRingedToposPullback`, and
  `SystemScalarModel` modules. Their signatures/docstrings and Stacks 06YS/0G7E
  were read. No missing dependency declaration is replaced by an arbitrary map.

Edge cases checked before writing: empty T; zero/unbounded C; the first positive
level (Lean zero); m=n (strict identity and canonical tensor unitor); arbitrary
m<n (strict composites); the nonflat quotient O/ell²→O/ell; ramification, so ell
is not substituted for a uniformizer. No constructibility, boundedness, Tor
amplitude, normalization, surjectivity or flatness of coefficient maps is assumed.
Independent site object t+1, site morphism t, and coefficient max u (t+1) universes
are retained. The existence of P and a says only that C has a strict representative,
as already implicit in localization; compatibility comes from that ONE representative.

Searches for an existing exact statement:

* msearch.py leanfinder, "A derived tower over quotient ring sheaves admits
  compatible flat term K-flat representatives with strict semilinear transitions":
  eight hits about smooth/ordinary flat modules and adic completion; no match.
* msearch.py loogle, `"IsKFlat", "tower"`: zero hits.
* msearch.py grep, `KFlat|kflat`, Algebra/Homology: zero hits.
* msearch.py leansearch, "Compatible K-flat models of semilinear towers of sheaves
  of modules": eight ordinary module flatness/tensor-product hits; no match.
* rg in lean/WeilConjectures and lean/Sheaf for semilinear/KFlat/tower combinations
  and the item id: no existing exact theorem. Upstream NormalizedTower concerns
  towers in one constant-ring ModuleCat-valued sheaf category; its hypotheses and
  conclusion are not this ordinary derived varying-coefficient tower statement.
  KFlatScalarTowerRealization concerns an augmented scalar-extension tower from
  one fixed complex, not arbitrary C in D(Tow). Reuse of the existing strict
  systems and normalized reduction maps avoids copying either notion.

No STATEMENT-DISPUTED issue found. The implementation makes no changes to the
mathematical statement and introduces no new DAG node. The maintainer performs
the independent delivery review; this report does not claim a second agent reading.

## Returned-delivery repair

Repaired the H2 return on immutable head `699f8168deb0`. The saved packet was
compared with the current main node: its non-delivery fields are unchanged.
Replaced the added theorem statement dependency `lem-pur-system-scalar-model`
with the live definition node `def-weil-pbc-system-scalar-model`. Its recorded
`SystemScalarModel` and `systemModelTmul` are the exact definitions used in the
statement, including the fields `.model.ε`; all model data come from `D.scalar`.
The theorem `nonempty_systemScalarModel` is not used by the statement. The
existence theorem stays in proof_deps and in the step-7 proof plan. Its module
is now a public import because the definition node owns the statement's data.

Replaced the explicit `systemRingHasDerived R` and the prioritized
`systemRingHasDerived` local instance by `HasDerivedCategory.standard`.
The completed-ring module and tower categories both use the explicit standard
localization in universe `max u (t + 1) + 1`, as allowed by
`def-weil-abstract-derived-category`. The local irreducibility list no longer
contains the theorem-module instance. No mathematical clause or hypothesis was
changed and no new definition or dependency module was introduced.

The advisory was checked against the predicates: the evaluation equation is the
naturality square for the exact-localization comparison, and the last equation
is the naturality square for every derived-limit projection. Both are retained.
The previously accepted completed projections, pinned D and U interfaces,
strict chain transitions, flat-term K-flatness, normalized reduction adjuncts,
pure tensors and reduction squares remain verbatim.

Repair validation: `scompile.py` compiled both the isolated sandbox module
(54.4 s) and its library-path module (49.2 s), without errors or warnings.
The recorded theorem signature matches the file verbatim, all Lean lines are
at most 100 characters, and the sole postponed proof is the named item theorem.
The dependency change preserves all reviewed edge cases, including independent
site/coefficient universes, the first level, equal levels and nonflat reductions.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
