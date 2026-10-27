## Worker report

The module `Sheaf.Paper.SupportedImageTorsionReductionsCd` states
`AlgebraicGeometry.ProEtale.supported_image_torsion_reductions_cohomology_vanishes`.
It has one theorem, with `sorry`, and introduces no definitions. The existing node's
statement, proof, proof dependencies and accepted split are unchanged.

Hypothesis and clause correspondence:

- The affine base is `(X : Scheme.{u}) [IsAffine X]`; the prime is `(ℓ : ℕ)
  [Fact ℓ.Prime]`; the nonnegative integer bound is `(d : ℕ)`.
- `_hcd` quantifies over every affine scheme V and every etale V → X, using
  `V.HasTorsionEtaleCohomologicalDimensionLE d`. Its definition quantifies over all
  locally torsion abelian sheaves, with no common annihilator required.
- A finite support chain is `(tree : QcqsOpenClosedTree X) (p : tree.Path S)`.
  Each open edge is a quasi-compact open immersion, and each closed edge has its
  complementary quasi-compact open sibling. Since X is affine, all chain vertices
  are qcqs. Conversely every chain of the node extends to such a finite binary
  tree by inserting complementary leaf siblings. Paths can stop at any vertex,
  so they do not require a support chain to end at a leaf. The root is the empty
  chain. Different complementary trees give the same specified path composite.
- The functor J is exactly `p.extension R`, whose recursion composes the published
  `CondensedRing.openImmersionLowerShriek` and `CondensedRing.lowerStar`, and is the
  identity at the root. No arbitrary extension functor is assumed.
- `(U : Scheme.{u}) (v : U ⟶ X) (_hv : proAffineEtale v)` uses exactly the affine
  pro-etale convention in `sk-def-pe-morphisms`: a small nonempty cofiltered
  presentation by absolutely affine etale X-schemes. `proAffineEtale.isAffine`
  supplies affineness of U; no extra hypothesis is required.
- The first conjunct quantifies over `(A : Type u) [CommRing A] [Finite A]` with
  `[TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]`. The topology
  instances express the specified discrete topology, which exists for every
  finite ring; they impose no extra algebraic condition. The coefficient is the
  existing `FiniteDiscreteOrdinary.coefficient A`, namely the continuous condensed
  ring object of A. `(∃ a : ℕ, ∀ x : A, (ℓ ^ a) • x = 0)` is precisely the common
  annihilating power of ℓ in this clause, including the zero ring.
- The first conjunct's L, M are internal modules over `condensedRingObj ... S`.
  Its two separate `HasFiniteConstantLocalModel` premises retain independent
  pro-etale covers and scalar presentations. `(f : L ⟶ M)` is arbitrary.
- `image f` is the actual image in that abelian module category. The term
  `(CondensedRing.upperStar R v).obj ((p.extension R).obj (image f))` is F_R,v(I_f).
  `DerivedCategory.singleFunctor _ 0` puts it in degree zero. Applying
  `(condensedModuleSections R U).rightDerivedFunctor` takes ordinary uncompleted
  module-derived sections into D(Ab), and `DerivedCategory.homologyFunctor` at q
  followed by `IsZero` states exactly the claimed vanishing for every integer
  `q` with `(d : ℤ) < q`.
- The second conjunct quantifies over every `(E : Type u) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]`. The published
  `DerivedNakayama.integerRing ℓ E` uses the spectral absolute value's norm
  topology on `Padic.coefficientExtensionIntegers ℓ E`. Thus B is O_E, with the
  norm topology, rather than the discrete constant sheaf. `AdicCompletion.Modules`
  is the category of modules over its pulled-back internal ring, without any
  completeness condition. The L, M, f and both finite-model premises are repeated
  over this coefficient, so integral torsion models and arbitrary integral maps
  are included.
- After forming the supported image in degree zero, the second conjunct applies
  `AdicCompletion.derivedReduction ℓ E U n` and then
  `AdicCompletion.restrict ℓ E U n`. By their definitions these are total left
  derived extension along the actual quotient B_U → (B/pi^(n+1))_U and exact
  derived restriction of scalars. The displayed order is exactly
  Res(K_f ⊗^L_B k_(n+1)), never the image of a reduced map. `n : ℕ` indexes all
  positive powers once, by n+1. The fixed uniformizer in the coefficient interface
  entails no loss: every uniformizer generates the same maximal ideal, and its
  nth power generates that ideal's nth power, as recorded in the coefficient
  extension node. The case E = Q_ℓ is included. The cohomology bound is q > d in
  this conjunct also, with no extra degree of vanishing lost or gained.
- All schemes, coefficient rings and sites use the fixed small indexing universe
  u; abelian sheaves and cohomology groups are in u+1, exactly as in the published
  coefficient and section interfaces. All binders are explicit and
  `set_option autoImplicit false` is enabled.

Dependency declarations read and used:

- Mathlib: `AlgebraicGeometry.Scheme`, `Scheme.smallEtaleTopology`, `Scheme.ProEt`,
  `IsOpenImmersion`, `IsClosedImmersion`, `QuasiCompact`, `Etale`,
  `CategoryTheory.Mod`, `DerivedCategory`, `DerivedCategory.singleFunctor`,
  `DerivedCategory.homologyFunctor`, and the abelian `CategoryTheory.Limits.image`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedRingObj` and the pulled-back coefficient ring instances.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, `CondensedRing.lowerStar`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`:
  `AlgebraicGeometry.proAffineEtale`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel` (the existing scalar-presentation definition).
- `Sheaf.Paper.QcqsOpenClosedTree`: `QcqsOpenClosedTree`, `Path`, `Path.extension`.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`: `condensedModuleSections`.
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`:
  `Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
- `Sheaf.Paper.FiniteDiscreteOrdinaryEncoding`: `FiniteDiscreteOrdinary.coefficient`.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`: `AdicCompletion.Modules`,
  `derivedReduction`, `restrict`, and their existing continuous integral coefficient
  `DerivedNakayama.integerRing` from `Sheaf.Paper.DerivedNakayamaResolution`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` retains the recorded
  coefficient-extension construction and its positive finite quotient interface.
- `Sheaf.Paper.CondensedModuleDerivedPushpull` and
  `Sheaf.Paper.LocalizingAdmissibleCoefficients` retain the existing ordinary
  derived and coefficient conventions; they are not replaced by new definitions.

The statement dependencies gain the already landed definition nodes
`def-sfb-qcqs-open-closed-tree`, `def-sfb-condensed-module-sections`, and
`sk-def-pe-derived-completion` to record the interfaces used. No new node or
replacement dependency module is needed. Every stated proof dependency's module
is imported; the unstated `lem-sfb-supported-image-koszul-comparison-nonpositive`
is named explicitly in the docstring and is not imported. The theorem docstring
contains all nine reviewed proof steps and their dependency ids. In particular,
its integral assertion remains the WANTED obligation, not an assertion that
classical comparison alone proves it. No proof is supplied in this stage.

Edge cases checked before writing: root path/empty chain; empty schemes including
empty U and S; zero finite ring; zero/identity maps; zero image; d = 0; first
positive reduction n+1 = 1; E = Q_ℓ; torsion integral local models; unrelated covers
and scalar modules; arbitrary continuous integral matrix entries. The signature
excludes none of these. There is no Nontrivial, nonzero image, flatness of the
image, completeness, classicality of reductions or common-cover hypothesis.
No concrete counterexample is known; no STATEMENT-DISPUTED flag is added.

Searches:

- `msearch.py ... leanfinder "Torsion etale cohomological dimension bound for
  supported finite coefficient sheaf images and derived reductions of integral
  images"`: eight hits about etale loci and module support dimension, none an
  exact supported-image or derived-reduction cohomology bound.
- `msearch.py ... loogle "DerivedCategory.homologyFunctor, Limits.image"`:
  no hits; reports unknown identifier `Limits.image` in the external index.
  The actual image declaration is supplied by the imported abelian category API.
- `msearch.py ... grep "supported.image|torsion.reductions"` and
  `... grep "supported_image_torsion|SupportedImageTorsion"`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` for the item id and supported-image/torsion names:
  no exact statement. `rg` in `lean/Sheaf` finds only the consumer comments in
  `SupportedThreeTermScalarCd.lean`, whose theorem is the different d+2 bound on
  three-term homology; it is not this image/reduction statement. Searches for
  support paths, finite constant models and reductions found the existing
  `QcqsOpenClosedTree`, `HasFiniteConstantLocalModel`, and `AdicCompletion`
  definitions, which this delivery uses without duplication.
- Read current `literature/blueprint/latest/.../det-sf-comp-coherence-refinement.proof.md`:
  its present refinement proof is the different proper-base-change route; this
  item's reviewed agent obligation retains its explicit WANTED provenance.

## Second reading by O2

Author cross-check against the node and final signature; no second worker was
started because the dispatch brief prohibits other agents. The maintainer's
independent review is still required. This section does not claim an independent
worker read occurred.

The cross-check checked both conjuncts, the repeated separate L/M local-model
premises, arbitrary f, actual `image f`, functor order, and the strict bound q>d.
The finite reduction index is n+1, so the first level is included, not level zero.
The tree-path encoding follows the already reviewed sibling
`SupportedThreeTermScalarCd` and imposes no leaf condition. For the affine pro-etale
variable the item explicitly cites `sk-def-pe-morphisms`; the chosen binder uses
that recorded ind-etale presentation interface, not an arbitrary weakly etale
map. The only elaboration correction was attaching `.rightDerivedFunctor` to its
preceding parenthesized functor across a line break. No mathematical statement
change was needed. Long lines were shortened without disabling the linter.

## Validation

All compilation uses the prescribed scompile.py wrapper. Final clean compile completed for both sandbox and library module names, exit 0,
with no errors or warnings. The compiler used the live published library.

Read the local HRS PDF, Section 8, condition (8.1) and Lemma 8.6. Its torsion
paragraph passes to an affine-etale presentation and uses torsion cohomological
dimension; its integral passage cites Lemma 7.9 and Theorem 7.7. This agrees with
the DAG source warning: the arbitrary supported integral-image reduction bound
is an additional WANTED obligation, not a direct quotation of classical comparison.
