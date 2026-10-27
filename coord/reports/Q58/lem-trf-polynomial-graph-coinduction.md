## Worker report

The module `Sheaf.Algebra.Homology.PolynomialGraphCoinduction` states
`ModuleCat.polynomial_graph_coinduction`, with its entire proof postponed as `sorry`.
There are no statement corrections, new nodes, dependency-record repairs, or disputed statements.
All changes to the existing node are confined to `lean`. The real-data helpers belong to this
node's graph construction and are enumerated in `lean.declarations`.

Clause-by-clause reading against the node:

- `A : Type u` with `[CommRing A]` is an arbitrary commutative ring. `n : ℕ` permits zero,
  and `a : Fin n → A` is its ordered tuple. `MvPolynomial (Fin n) A` is exactly S;
  `MvPolynomial.C` is i and `MvPolynomial.eval₂Hom (RingHom.id A) a` is e. No algebra
  action is supplied by a hypothesis. `MvPolynomial.eval₂Hom_comp_C` supplies ei=1.
- `polynomialGraphKoszul` abbreviates the dependency's actual
  `ExteriorAlgebra.koszulComplex` on `X j - C (a j)`, extended along
  `ComplexShape.embeddingDownNat`. Thus homological degree k becomes cohomological -k.
  The first two conjuncts assert `Module.Free` and `Module.Finite` in every integer
  degree and `IsZero` outside [-n,0], not merely perfection or existence of some resolution.
- The witness ε is an actual complex morphism to the degree-zero ordinary module A,
  with its S-action obtained by `restrictScalars e`. `QuasiIso ε` says it resolves A.
  The equation at `polynomialGraphWedge ... 0` sends the empty wedge, i.e. the generator
  1 of K⁰=S, to 1. S-linearity therefore fixes ε⁰ as evaluation, so this is the
  augmentation specified by the node rather than an arbitrary quasi-isomorphism.
- χ is `derivedCoinduction e` applied to S[0], with target the original ordinary
  A-module A[0] shifted by `-(n : ℤ)`. This retains the precomposition A-action;
  no underlying S-object isomorphism is substituted for an A-object isomorphism.
- The top normalization is encoded by a complex map
  `z : K⟦-n⟧ ⟶ S[0]` sending the ordered top wedge to 1. The displayed equation is
  `Q(ε[-n]) ; U(χ.inv) ; counit = Q(z)`, with the canonical Q/shift and exact
  restriction comparisons inserted by `polynomialGraphShiftedAugmentation`.
  Thus the inverse of χ is the actual adjunct of the ordered top functional;
  an arbitrary isomorphism or an unspecified orientation would not satisfy this equation.
  The map z only has a nonzero component on K's top exterior power. Pulling it through
  the graph augmentation and evaluating is exactly the cohomology identification
  `[lambda] ↦ e(lambda(e_1 wedge ... wedge e_n))` in the node's proof.
- `polynomialGraphExtension` abbreviates the existing K-flat `leftDerivedFunctor`
  of `extendScalars C`; its objects are S tensor_A^L T with S-action on the polynomial
  factor. α is a **natural isomorphism of functors**, from this extension followed by
  the recorded coinduction to `shiftFunctor ... (-n)`. It therefore gives the requested
  comparison for every T and every morphism in the unbounded derived category.
- β identifies the extension of A[0] with S[0]. Its adjunct is the explicitly constructed
  coefficient map, so β is the canonical unit comparison, not an arbitrary rescaling.
  The equation for `α.hom.app (polynomialGraphUnit A)` identifies it with χ after β.
  This ensures that the tensor comparison uses the already oriented A-action on C_e(S).
- For every `h : n = 0`, the last equation normalizes α on **every** T. The map
  `polynomialGraphQuotient` is defined as the extension-adjunct of the inverse canonical
  restriction identification induced by ei=1. If n=0 it is the canonical equivalence
  S tensor_A^L T → U_e T. The final composite with `U_e(α.inv)` and the actual
  coinduction counit equals the identity. After the standard shift-zero map this
  characterizes the identity coinduction comparison under the empty-polynomial ring
  equivalence. In particular no literal equality of MvPolynomial (Fin 0) A with A
  is assumed. The empty-wedge normalization fixes χ on the unit as well.
- There are no Noetherian, nonzero-ring, Tor, boundedness, flatness, or choice-of-map
  assumptions. `DerivedCategory (ModuleCat.{u} A)` is the ordinary unbounded category
  in the library's usual selected derived universe, available for every such ring.

Dependency declarations read and used (their modules are imported):

- `def-weil-pbc-mv-polynomial-ring`: Mathlib.Algebra.MvPolynomial.Basic, `MvPolynomial`
  and `MvPolynomial.algHom_ext`; evaluation from Mathlib.Algebra.MvPolynomial.Eval,
  `MvPolynomial.aeval`, with `eval₂Hom` the same evaluation as a ring homomorphism.
- `def-weil-pbc-koszul-complex`: WeilConjectures.AlgebraicGeometry.KoszulComplex,
  `ExteriorAlgebra.koszulComplex`, the exterior-power terms and contraction differential.
- `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory` and `DerivedCategory.Q`, with the shared shift convention.
- `def-trf-derived-coinduction` and `lem-trf-derived-coinduction-adjunction`:
  Sheaf.Algebra.Homology.DerivedCoinductionAdjunction, `ModuleCat.derivedCoinduction`,
  `ModuleCat.derivedCoinductionAdjunction`, and its evaluation counit.
- `def-pur-derived-internal-hom`:
  Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom,
  `CategoryTheory.ordinaryModuleDerivedInternalHom`; this exposes the existing derived
  closed monoidal structure used by the tensor and projective-Hom proof interfaces.
- `lem-pc-derived-tensor-second-factor-functor`:
  Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor,
  `DerivedCategory.exists_derivedTensor_second_factor_functor`. This records the
  K-flat mixed total-tensor computation and naturality used in steps 5–6.
  K-flat scalar extension itself uses the existing upstream
  `Functor.leftDerivedFunctor`, with `ModuleCat.extendScalars_preservesKFlatQuasiIso`
  from WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso. Its additive instance
  is `ModuleCat.baseDerivedTensor_extendScalars_additive` from the existing
  WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel.
- The remaining proof imports are WeilConjectures.RingTheory.KoszulDualComplex,
  `ExteriorAlgebra.koszulDualComplex`; WeilConjectures.RingTheory.KoszulComplementaryEquivalences,
  `ExteriorAlgebra.exists_koszul_complementary_equivalences`;
  WeilConjectures.RingTheory.RegularSequenceKoszulRegular,
  `RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular`;
  Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`;
  Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel,
  `CochainComplex.projective_hom_evaluation_model`;
  Sheaf.Algebra.Homology.ChangeOfRingsKFlat,
  `SheafOfModules.changeOfRings_isKFlat_of_flat_terms`;
  Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor,
  `DerivedCategory.perfect_algebra_coinduction_tensor`; and
  Mathlib.Algebra.Homology.DerivedCategory.TStructure,
  `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`.
  These are ordinary proof imports, as required for the next stage; no private
  reimplementation of their notions is supplied.

Source and mathematical edge checks:

Read Stacks `dualizing.tex`, `lemma-RHom-is-tensor-special` (0BZE), and `duality.tex`,
`lemma-regular-immersion-ext` (0BQZ), including their proofs. This item is the existing
agent polynomial specialization recorded by the node, not the blueprint unit itself.
The theorem docstring carries all six accepted DAG proof steps and the exact sign
`(-1)^(np)` of tensor cancellation. No source-based correction was needed.

Checked the empty tuple: the Koszul complex is the rank-one term in degree zero;
its empty wedge is 1, both top and augmentation normalizations are the identity,
and the last equation fixes the functor comparison after the canonical polynomial
carrier equivalence. Checked n=1: the complex is `[S --(x-a)--> S]`, its dual has
cohomology A in degree 1, and χ has target A[-1]. The map z sends the top basis to 1.
Checked A=0: every term and derived object is zero, all normalization equations
have 1=0 in the zero ring, and finite freeness and quasi-isomorphism still hold.
Checked a nonreduced base A=Z/4 and a=2: x-2 is monic, so coefficient comparison
still proves successive injectivity; no nonzerodivisor hypothesis on a is imposed.
Checked unbounded T: it ranges over the whole derived category as a functor argument;
no representative, support, Tor or K-flatness hypothesis on T appears in the theorem.
The auxiliary definitions are abbreviations or compositions of existing maps; none
uses a theorem-with-sorry to choose data, and all variables and universes are explicit.

Searches for an existing statement (2026-10-24, via prescribed msearch.py):

- LeanFinder: `Polynomial evaluation graph derived coinduction is the shift by minus
  the number of variables, computed by its ordered Koszul resolution`. Eight hits
  (PolynomialLaw.φ, PreSubmersivePresentation.aevalDifferential, polynomial-module
  evaluation and cotangent-complex formulas); none states graph derived coinduction.
- Loogle: `MvPolynomial.eval₂Hom, DerivedCategory`. Zero hits.
- Mathlib grep: `Koszul|coinduction|coinduct` in RingTheory. One hit, the TODO about
  Koszul regularity in Regular/RegularSequence.lean, no matching theorem.
- LeanSearch: `Polynomial evaluation derived Hom of the quotient with the polynomial
  ring is the quotient shifted by minus the number of variables`. Eight hits, on
  ordinary evaluation and the one-variable quotient equivalence; no derived result.
- Project rg: `graph.coind|polynomial.*[Cc]oind|graph.*Koszul|polynomial.*[Dd]ual` in
  lean/Sheaf and lean/WeilConjectures found broader diagonal-class constructions and
  geometric polynomial duality, not this arbitrary-ring ordered graph theorem.
  The only direct item-id citation is in the downstream
  ArbitraryPolynomialGraphClassBaseChange proof docstring; grep of WeilConjectures
  for the item id has no hit. Explicit searches of all new full declaration names
  in Mathlib and both project roots have no hit. The existing graph Koszul helper
  on PolynomialKoszulChart concerns a localized polynomial chart tensor a base;
  the present abbreviation uses the same shared koszulComplex and adds no independent
  definition of a Koszul complex or notion of coinduction.

Validation: every compile uses scompile.py. The file was checked both as its sandbox
module and as `Sheaf.Algebra.Homology.PolynomialGraphCoinduction`. Initial elaboration
repairs supplied the explicit Q coefficient category and used Mathlib's semilinear
restriction equivalence for the coefficient map, avoiding an incorrect definitional
identification between its two scalar actions. The final version is recompiled and
validated by deliver2.py preflight and per-file compilation before push.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
