## Worker report

Item: lem-per-rational-stratum-finite-free-model. Group Q12, stage 2, 2026-10-24 UTC.
The delivery changes only the item's `lean` record and supplies
`Sheaf.Paper.RationalStratumFiniteFreeModel`. The long statement is represented by five
named theorems in the same module, all recorded in `lean.declarations`, all with `sorry`.
Their construction abbreviations and explicit coefficient maps contain no postponed data.
There are no new DAG notions, dependency repairs or statement corrections.

### Source and hypotheses

Read Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.2, the paragraph
before Definition 6.8.6, Definition 6.8.10, Proposition 6.8.11(3), and Proposition
6.8.14(2), from the local PDF. Also read the current blueprint's
`sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-smooth-pullback-t-exact.md`.
The auxiliary finite-presentation and balanced-tensor calculation is exactly the one
spelled out in the DAG statement and its nine proof steps.

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`, explicitly declared in the section.
- A = O_E and its chosen uniformizer: `A l E` abbreviates the universe lift of the
  dependency's `Padic.coefficientExtensionIntegers l E`. Its ideal, quotient and chosen
  uniformizer are the original coefficient constructions imported by
  `CoefficientExtensionFinite` and `ContinuousCoefficientImmersionRestriction`.
- Noetherian X: `(X : Scheme.{u}) [IsNoetherian X]` in the immersion, chosen-model and
  final theorems. This is the scheme Noetherian hypothesis, including compactness.
- Small pro-etale site: exactly `Scheme.ProEt.topology X`, with objects in universe
  u+1 and morphisms in u. Module and coefficient universe is u+1. No site universes
  are equated and no independent smaller test-object universe is used.
- Completed and localized coefficients: the statement expressly identifies them with
  continuous coefficients using the recorded normalized theorem. Accordingly the module
  uses `integralCoefficientSheaf l X E` and `rationalCoefficientSheaf l X E`, and the
  *actual* normalized `integralRationalCoefficientMap`. It does not introduce a new
  completion or substitute constant rings for the continuous rings. The imported
  `continuousCoefficientImmersionRestriction` gives the quotient-projection,
  localization and immersion identifications with these presentations.
- M: `Modules (integralCoefficientSheaf l X E)`, where `Modules` is the recorded
  `ringedSiteModules` specialization in `ProEtaleTensorComparison`, hence Mathlib's
  `SheafOfModules` over the underlying ring sheaf.

### Clause-by-clause rendering

1. The first paragraph's natural immersion comparison is `immersionComparison`.
   `integralPullback` and `rationalPullback` specialize the existing canonical
   `continuousCoefficientPullback`; they are not arbitrary coefficient maps.
   `restrictIntegral` and `restrictRational` apply the recorded module inverse image
   and change rings along these maps. For an immersion into noetherian X the recorded
   coefficient comparison makes this precisely the stated h-inverse restriction.
   The existential family `e M` compares
   `restrictRational h (rationalize X M)` with
   `rationalize S (restrictIntegral h M)`. Its first equation specifies the image of
   every original pulled-back pure tensor, using `inverseSection`,
   `scalarExtensionSection`, and the actual precomposition `rationalSection`.
   Taking its scalar `a = 1` gives localization-unit compatibility, since
   `rationalSection` is a ring map on sections and preserves 1. The next equation
   gives naturality in *every* module morphism. The last clause restricts the
   comparison to every `U : S.ProEt`.
2. Ordinary constant-module sheaves are exactly `constantModuleHomFunctor`, namely
   `siteConstantModuleFunctorGeneral` transported through its canonical constant-ring
   isomorphism. `integralModel` uses the existing `extension` construction for
   `B_S tensor_(A^c_S) N_S`; `rationalModel` uses it for
   `E_S tensor_(E^c_S) V_S`. Their coefficient maps `integralConstants` and
   `rationalConstants` are specializations of
   `continuousCoefficientConstantComparison`, which is the sheafification adjunct of
   actual constant functions. No constant-sheaf functor is redefined.
3. N is `ModuleCat.{u+1} (A l E)` with `Module.FinitePresentation (A l E) N`.
   `vectorSpace` is Mathlib's ordinary `(ModuleCat.extendScalars (inclusion l E)).obj N`,
   i.e. E tensor_A N. `vectorUnit` is its actual adjunction unit n -> 1 tensor n.
   There is no flatness, injectivity, torsion-freeness, chosen global basis or rank
   hypothesis on N.
4. The two scalar isomorphisms are in `scalarModels`. The first, `reassociation`, is
   the *existing* `scalarExtensionTowerIso` with this exact ring-sheaf tower.
   Its displayed equation sends a tensor (b tensor x) to a*inclusion(b) tensor x,
   even for arbitrary local sections x of the constant module sheaf. The second
   family `e N hN` maps `directModel N` to `rationalModel (vectorSpace N)` and is
   normalized by a tensor n -> a tensor (1 tensor n) on every constant generator.
   Constant generators locally generate the sheafified constant module, so this
   characterizes the requested map on all local pure tensors. The final equation
   is naturality in each map between finitely presented modules. Restricting these
   sheaf isomorphisms by `SheafOfModules.overFunctor` gives the last slice clause;
   their section formulas are natural transformations, so the same formulas hold
   after restriction to each object of that slice.
5. Every specified finite presentation is included in `presentationModels`:
   arbitrary `m n : ℕ`, `D : Matrix (Fin n) (Fin m) (A l E)`, the specified arrow
   `q : A^n -> N`, `Function.Exact (Matrix.toLin' D) q`, and
   `Function.Surjective q`. There is deliberately no `Function.Injective D`.
   `matrixOverField` is precisely the entrywise inclusion image D_E.
   The existential `dS` is characterized at *every* object, section and coordinate
   by the entrywise constant-section matrix. This uniquely specifies D_(E_S).
   The maps `pE`, `pS` and isomorphisms `v`, `w`, with
   `pE ≫ v.hom = cokernel.π D_E` and `pS ≫ w.hom = cokernel.π dS`, give the two
   normalized cokernel presentations. `pE` is fixed on every basis vector by
   `vectorUnit (q e_j)`; `pS` is fixed on all constant vectors by the corresponding
   sheafification-unit formula. Thus these are the specified presentations, not
   bare isomorphisms between unmarked objects.
6. The specified elimination clause quantifies over rho, the necessary matrix sizes
   rho <= n,m, `P : Matrix.GeneralLinearGroup (Fin n) (K E)` and
   `Q : Matrix.GeneralLinearGroup (Fin m) (K E)`, and the exact equation
   `P * D.map inclusion * Q = rankMatrix E m n rho`.
   `rankMatrix` has entry 1 precisely at i=j<rho and 0 elsewhere.
   The resulting `p`, `q'` are changes of basis of the finite-power sheaves,
   with *both* their forward and inverse maps specified by the constant-section
   matrices of P,P^-1 and Q,Q^-1. Being actual isomorphisms explicitly preserves
   inverses. The constant-section map is a ring homomorphism, so it also preserves
   the displayed elimination equation. The cokernel isomorphisms `a`, `b` identify
   the cokernels with `E^(n-rho)` and `E_S^(n-rho)` and are fixed by the exact
   formula `[x] -> tail(P*x)` on original vectors or local sections.
   `tailIndex` uses the canonical final coordinates rho+j. The slice clause retains
   every object U; all specified matrix maps are sheaf maps, so the formulas and
   inverse identities restrict without additional choices.
7. `chosenLocalModel` takes an arbitrary *specified* local model isomorphism on an
   arbitrary U and concludes finite freeness on that U. The rank is existential
   per object, without a refinement of U.
8. `rationalStratumFiniteFreeModel` takes the supplied
   `Scheme.FiniteLocallyClosedStratification X`, cover index types `I k`, objects
   `U k i`, `CoversTop (U k)`, and finitely presented local models on these objects.
   It concludes `∀ k i, ∃ r, Nonempty (...over (U k i) ≅ ...freeModel r...)`.
   Thus exactly the same strata and cover objects remain, while ranks may differ
   with k and i. The second conjunct is `rationalConstructible`.
9. `rationalConstructible` calls the dependency's `IsContinuousConstructible` after
   the explicit `rationalLatticeRingIso`. That isomorphism is the actual pointwise
   commutation between continuous functions valued in `ULift E` and the `ULift` of
   continuous E-valued functions, with pointwise inverses. The topology on E is the
   prescribed `coefficientExtensionNormedField`. This handles the existing coefficient
   presentations without a second definition of constructibility or a chosen
   arbitrary ring isomorphism. The final docstring explains that locally closed
   subsets of noetherian X are constructible, so the supplied finite locally closed
   stratification converts to the dependency's `Scheme.Stratification`.

### Dependency declarations read and used

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Topology.FiniteLocallyClosedStratification`,
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, retaining the actual sheafified tensor;
  scalar models use `changeOfRingsOfUniverses` from its public import closure.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`:
  `CategoryTheory.siteConstantModuleFunctorGeneral`; used via the canonical
  `constantModuleHomFunctor` and `constantModuleHomUnit` in
  `Sheaf.CategoryTheory.SiteConstantModuleHom` and the recorded finite-presentation
  extension module. Their full construction and ring transport were read.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its imported coefficient constructions.
- `Sheaf.Paper.AdicCoefficientDatum`:
  `AlgebraicGeometry.Scheme.completedReductionTower`,
  `AdicCoefficients.completedRing` and the actual quotient-coefficient tower;
  the present module only uses degree-zero coefficients, through the normalized
  continuous completion identification, not an independently chosen derived tower.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.Paper.ContinuousConstructibleModule`:
  `AlgebraicGeometry.ProEtale.IsContinuousConstructible` and its constant-module models.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `CategoryTheory.ringedLocalizationRingOfUniverses` and its canonical ring-unit map;
  the coefficient restriction theorem supplies the identified continuous presentation.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
  `AlgebraicGeometry.Scheme.continuousCoefficientImmersionRestriction` and the
  coefficient definitions in its public `ContinuousCoefficientBasic` import.
  `ContinuousCoefficientCompletion` and `ContinuousCoefficientPullback` are explicitly
  imported for their existing constant maps and canonical pullbacks.

All stated proof dependencies are imported. Ordinary tensor right exactness is the
Mathlib match `lTensor_exact`/`rTensor_exact` in
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`, imported as a proof dependency.
The other imported proof modules and theorem docstrings follow the node's nine steps.

### Edge cases

- N=0 gives V=0; every finite-power conclusion permits rank zero.
- N=A/(varpi^a), a>0, rationalizes to zero. Neither scalarModels nor the cokernel
  theorem has a torsion-free or flatness assumption on N.
- N=A^r gives the usual free rational model and its ordinary basis maps.
- m=0: the matrix has no columns. The exact presentation is allowed, and the
  cokernel formula gives the automorphism induced by P on E^n and its sheaf power.
- n=0: surjectivity forces N=0; the zero-rank cokernel and free power are included.
- rho=n: `Fin (n-rho)` is empty; the tail and the finite power are the zero module.
- rho=0 and the zero presentation matrix retain the entire codomain.
- Empty X, a zero-stratum stratification, empty strata, empty covering index types
  where `CoversTop` permits them, and all empty-matrix combinations are admitted.
- Ranks are below the quantifiers over k and i; there is no uniform rank or global
  trivialization requirement, and no cover refinement is inserted.
- Finite locally closed strata, rather than the stronger constructible-stratum
  structure, are input. Constructibility of those subsets follows from noetherian X
  only for the final use of the existing constructibility predicate.

### Searches and validation

- msearch leanfinder: "Rationalization of finitely presented integral continuous
  coefficient module sheaves is locally finite free on the same locally closed strata".
  Eight generic local-generation/finitely-presented sheaf hits; no exact statement.
- msearch loogle: "SheafOfModules.changeOfRings, Module.FinitePresentation".
  No hits; service reports unknown identifier SheafOfModules.changeOfRings.
- msearch grep: "changeOfRings.*(comp|assoc)|extendScalars.*cokernel". No hits.
- msearch leansearch: "rational scalar extension continuous coefficient sheaves
  locally finite free finitely presented module". Eight hits on generic finite
  presentation/tensor scalar extension; no complete normalized stratum assertion.
- Local rg of WeilConjectures and Sheaf for rational stratum, finite free model,
  scalar-extension towers, continuous constant maps and matrix coordinates found
  the existing scalarExtensionTowerIso and finite-power/constant-module interfaces,
  which are used. The related `RationalStratumIntegralModels` concerns *integral*
  models of rational filtration quotients, and does not state this node.
- Local rg of WeilConjectures for the exact item id returned no matching declaration.
  No project or Mathlib declaration found has the full normalized statement.
- scompile.py in module mode is the sole compiler used. Universe metavariables in
  scalar extension, finite powers and sheafCompose were resolved by writing the
  actual u/u+1 universe parameters; no universe equation was added as a hypothesis.
  Diagnostic #check commands were removed. All lines are at most 100 characters.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q12

Reread the node and the finished module clause by clause. This is the worker's own
second pass; the maintainer performs the independent delivery review.

Checked the prime/finite-extension binders; Noetherian X; the actual small pro-etale
site and module universe; normalized continuous B/E presentations; canonical coefficient
pullbacks; localization-unit formula (set a=1); arbitrary M and morphisms; every U;
constant-module sheafification and coefficient transport; finite presentation of N;
ordinary V=E tensor_A N; both scalar formulas and naturality; every specified exact
right presentation; both marked cokernels; the exact entrywise coefficient matrix;
P,Q, both inverse matrices and the prescribed tail maps; all zero dimensions; the
chosen local model theorem; and the exact original strata and covers in the final
conclusion. Checked that rationalConstructible uses the recorded predicate, through
an explicit pointwise isomorphism, rather than a second predicate with fewer clauses.

The compile-driven fixes on this pass were explicit universe arguments and removal
of diagnostics/one overlong line. No mathematical hypothesis, conclusion, node
statement or dependency statement changed. No unsupported arbitrary map or existence
choice is used in a definition. All five postponed theorems have their node-matching
source and complete proof plan in their docstrings and are listed in the Lean record.
