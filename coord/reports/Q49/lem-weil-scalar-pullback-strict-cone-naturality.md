## Worker report

Item: lem-weil-scalar-pullback-strict-cone-naturality. Module:
`Sheaf.Paper.ScalarPullbackStrictConeNaturality`; main declaration
`WeilConjectures.scalarPullbackStrictConeNaturality`.

The delivery states the existing DAG statement, without changing its statement,
source, dependencies, proof, or status. There is one postponed theorem, the main
statement. All thirteen auxiliary declarations have real data or are explicit
predicates/structures expressing this theorem's witnesses; none introduces another
coefficient system, tensor product, inverse image, K-flatness predicate, or derived
category. The natural-language proof in the theorem's docstring follows all eleven
DAG proof steps. No proofs are supplied in stage 2.

Hypotheses and clauses were read against the node and rendered as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` in the explicit section variables. |
| Finite extensions E and L of Q_ell, and E included in L | Explicit fields, `Algebra ℚ_[l]`, `FiniteDimensional ℚ_[l]`, and `(ι : E →ₐ[ℚ_[l]] L)`. An algebra homomorphism of fields is injective, so this includes exactly the specified inclusions. |
| Valuation rings, chosen uniformizers, finite quotients | The recorded `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and `coefficientExtensionRing`, through the existing integral coefficient constructions. No valuation or uniformizer is chosen again. |
| A scheme morphism, with ell invertible on X and Y | `{X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)` and the two explicit hypotheses `∀ x, IsUnit (l : X.residueField x)` and its Y analogue. In a field this says ell is nonzero; at every point this is precisely invertibility of ell on the scheme. |
| Small pro-etale sites and completed coefficient sheaves R and S | `X.ProEt`, `Y.ProEt`, `integralTowerModules l E W`, and `completedIntegralCommRingSheafUnrestricted l F W`. Site objects retain size t+1, morphisms size t; coefficients/modules have size max u (t+1). |
| Positive levels m >= 1 | Each `n : ℕ` denotes m=n+1, exactly the existing tower convention; n=0 is exponent one, never exponent zero. |
| The quotient maps iota_m, rho_m and completion projections | `integralScalarQuotientSheafMap`, `integralScalarRho`, and `completedIntegralCommRingProjectionUnrestricted`, from the recorded extension and completed coefficient modules. |
| Any cochain complex P and Q=P tensor S | `CochainComplex (integralTowerModules l E Y) ℤ` and `(completedOrdinaryScalarComplex l E L ι Y).obj P`. There is no boundedness or flatness assumption on strict inputs. |
| D^F_m(M) and its quotient transitions | The existing `integralOperationsPullbackLevel` and `integralOperationsPullbackTowerFunctor`. They use ordinary reduction, the canonical constant-coefficient module pullback, and restriction along the completed projection. |
| Module inverse image and its coefficient structure maps | `integralOperationsLevelPullback` is the recorded `Scheme.coefficientProEtaleModulePullback`, adjoint to pushforward with the constant-section ring map. The helper `scalarPullbackGenerator` uses its existing adjunction-unit generator. |
| A_F(M)=Cone(1-s)[-1] | The existing `integralOperationsPullbackComplexFunctor` and `integralOperationsRoosFunctor`; `scalarPullbackRoosEnd` merely names the existing transition endomorphism to expose its coordinates. |
| Existence and uniqueness of natural strict tower maps d_m | `ScalarPullbackStrictConeData.level` is a natural transformation between functors into the category of strict towers of cochain complexes. `Nonempty` gives existence; `Subsingleton`, together with the fixed formulas, gives uniqueness of the normalized witnesses. |
| The exact local tensor formula, including a, b, s and p | `ScalarPullbackGeneratorFormula` quantifies every P, n, degree i, pro-etale V over Y, section p, finite coefficient section a, finite coefficient section b on its base change, and completed scalar s there. Its left side is d applied to `s tensor (b * g^*(a tensor p))`; its right side is the L-generator with `p tensor 1`, coefficient iota(a), and multiplier `iota(b) * pi_L(s)`. Thus the target p is explicitly p tensor 1 in Q, as required in proof Step 1. |
| Balancedness | The generator formula is required of an actual morphism of sheaf modules produced from the existing sheafified tensor constructions, for all generators and all coefficient sections. Such a map factors through all tensor balances, rather than being a function on formal symbols. |
| Commutes with differentials, quotient transitions, and every chain map | A component of `level` is a morphism of strict towers; its components are actual cochain maps. Naturality of `level` is in every chain map P -> P'. All three requirements are encoded in the types, not omitted. |
| Canonical tensor/product maps are isomorphisms and basis independent | `scalarPullbackProductMap` is literally `Pi.lift` of the ordinary scalar functor applied to each projection; the first conjunct asserts `IsIso` for every countable family of complexes on X. No basis is an input, so both this map and its unique inverse are independent of a basis. |
| Identification of tensor A_E(P) with the Roos cone of the tensor tower | `ScalarPullbackStrictConeData.cone` is the natural isomorphism between these two existing complex functors. `ScalarPullbackConeFormula` fixes both its degree-i first coordinate and its degree-(i-1) shifted coordinate to the canonical product comparison. |
| Delta_P applies product d_m on both coordinates | `scalarPullbackConeMap` is `κ.hom ≫ Functor.whiskerRight d integralOperationsRoosFunctor`. The existing `integralOperationsRoosMap` is the shifted cone map of the square whose two arrows are both `Pi.map (fun n => d.app (op n))`. Thus it fixes both cone coordinates, without a third-arrow choice. |
| Flat-term K-flat representatives and their scalar extensions | The theorem's second conjunct asserts that ordinary scalar extension carries every object of the recorded `integralOperationsGoodComplex l E Y` into `integralOperationsGoodComplex l L Y`. This property is exactly independent-coefficient K-flatness plus flatness of every term. |
| Interpretation of the source cone after ordinary derived extension | The third conjunct asserts invertibility of `completedScalarCounit` on A_E(P) for every good P. It does not require A_E(P) to be K-flat: finite-free scalar extension is exact on all complexes. |
| Natural derived transformation C_X Lg_E^* -> Lg_L^* C_Y | `ScalarPullbackStrictConeData.derived : integralDerivedPullback l E g ⋙ completedDerivedScalarExtension ... X ⟶ completedDerivedScalarExtension ... Y ⋙ integralDerivedPullback l L g`. These are the existing completed pullback and ordinary derived scalar functors, respectively. |
| Representative [delta_P] under the canonical comparisons | `ScalarPullbackDescentFormula` is the equality obtained by following the derived transformation with the Y scalar counit and the L pullback comparison, versus the E pullback comparison, the X scalar counit on A_E(P), and `DerivedCategory.Q.map (δ.app P)`. It quantifies every good P and every proof that its ordinary scalar extension is good, whose existence is supplied by the second conjunct. |
| Independence of K-flat resolution; naturality for arbitrary derived morphisms | `derived` is a natural transformation on the full derived category, not only a transformation on representatives. The normalized representative equation together with `Subsingleton` expresses uniqueness and hence resolution independence. The docstring explains localization, including inverse quasi-isomorphisms. |
| E included in L included in F | `ScalarPullbackCompositionFormula` quantifies every finite Q_ell-extension F and algebra homomorphism j from L. It uses normalized data for L,F and E,F with inclusion `j.comp ι`. These exist by the same theorem at those extensions; they are not arbitrary unconstrained maps. |
| Level maps compose after canonical tensor associators | The composition predicate supplies actual natural tensor association isomorphisms αX and αY, fixed on every tensor generator by `ScalarPullbackAssociationFormula`. It asserts the square: extend d_EL to F, apply d_LF, then apply D_F to αY = αX at D_E(P) followed by d_EF. |
| Cone maps compose after those associators | The same predicate explicitly asserts the corresponding equation for the chain maps `scalarPullbackConeMap`, with A_F applied to αY and αX evaluated at A_E(P). |
| Identity extension | `ScalarPullbackUnitFormula` states both level and whole-cone equations after the published `completedScalarIdentityMultiplication` on X and Y. The final conjunct quantifies every normalized identity-extension witness. Existence of one follows by instantiating this same existence theorem with L=E and the identity algebra homomorphism. |

Recorded dependency declarations used (their full signatures and relevant docstrings
were read in the source):

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, with the imported coefficient constructors.
- `def-weil-scheme-morphism-properties`: a convention node with no declaration of its
  own; the statement uses Mathlib schemes, morphisms and residue fields directly.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`.
- `def-weil-completed-integral-coefficients`:
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, with the public completed
  coefficient sheaves, projections and finite coefficient sheaves.
- `def-weil-integral-scalar-extension`: `Sheaf.Paper.IntegralScalarExtensionUniverses`,
  retaining `integralScalarQuotientSheafMap` and `integralScalarRho`; ordinary extension
  below uses the canonical completed coefficient map, not the completed scalar functor I.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, with the actual
  sheafified tensor and recorded change-of-rings constructions.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `Scheme.proEtaleBaseChange`; its independent-coefficient interface
  `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses` supplies
  `coefficientProEtaleModulePullback` and its adjunction, already used by the pullback levels.
- `def-pur-integral-derived-operations`: `Sheaf.Paper.IntegralDerivedOperationsOnSlices`,
  publicly retaining `integralDerivedPullback` and `integralDerivedPullbackComparison`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, inside the recorded good-complex property.
- `lem-pur-integral-operations-well-defined`: `Sheaf.Paper.IntegralOperationsWellDefined`,
  all the recorded strict pullback levels, transitions, towers, Roos maps, and good models.
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem. The scalar
  functor and counit used here are the canonical ones already exposed by the next dependency.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory` and `DerivedCategory.Q`.
- `lem-weil-finite-free-completed-scalar-comparison`:
  `Sheaf.Paper.FiniteFreeCompletedScalarComparison`, `completedCoefficientMap`,
  `completedOrdinaryScalarExtension`, `completedOrdinaryScalarComplex`,
  `completedDerivedScalarExtension`, `completedScalarCounit`,
  `completedScalarTensorSection`, `completedScalarIdentityMultiplication`, and
  `finiteFreeCompletedScalarComparison`.

The stated proof dependencies are also imported: strict Roos model and homotopy
functor, independent-coefficient K-flat resolution, K-flat change of rings, site
derived tensor descent, exact-functor derived factorization, and localization
universal property. Statement dependencies reached publicly through the recorded
modules retain their exact existing declarations; no dependency repair is needed.

Source check: I read the local PDF at Definition 3.4.10, Proposition 3.5.1, and
Lemma 6.5.9(4). They supply completion context, not a literal scalar-naturality
theorem, exactly as the node's source/proof_origin says. Lemma 6.5.9 concerns
qcqs pushforward and its adjunction; the present node asserts an explicit strict
construction for the already recorded completed-pullback functor on arbitrary
schemes, and does not claim that pushforward adjunction for arbitrary schemes.
Its eleven agent-formulated steps are the source of the strict maps and descent.
No qcqs, constructibility, finite-dimensionality of schemes, Noetherian condition,
or cohomological bound was added to this node.

Edge cases checked mathematically before and during writing:

- P=0, zero maps and arbitrary chain differentials: the formula is linear in p;
  the strict map and both diagonal cone coordinates give zero as required.
- Empty X or Y: the same sheaf constructions and pointwise unit hypotheses apply;
  no nonemptiness or chosen point appears.
- g the identity: the adjunction-unit formula specializes to the usual tensor
  coefficient inclusion, with the same quotient transitions.
- L=E and the identity inclusion: the coefficient formula becomes multiplication;
  the explicitly stated unit equations use the published multiplication isomorphisms.
- n=0 is exponent one. For a ramified extension such as adjoining a square root
  of ell, the same-index quotient map need not be flat or injective. No such
  hypothesis is imposed; exactness is used only for completed finite-free extension.
- Triple fields with one or both inclusions identities remain included in the
  quantified composition predicate and its multiplication formula.
- Complexes may be unbounded in either direction. Products are termwise products;
  the finite-free argument uses a finite basis sum, never a finite cochain range.
- Independent scheme/coefficient universes remain t and u throughout, with actual
  small-site object/Hom sizes t+1 and t. No equality of those site universes is imposed.

Searches actually run with msearch.py (2026-10-21):

- LeanFinder: "Finite free extension of completed coefficient sheaves commutes with
  strict pullback towers and both coordinates of their Roos cones, naturally on the
  derived category". Eight results included `SheafOfModules.freeFunctorCompPullbackIso`,
  `pullback_map_ιFree_comp_pullbackObjFreeIso_hom`, `pullbackObjFreeIso`, and affine
  transition-limit constructions. None is this coefficient-tower/cone statement.
- Loogle: `CategoryTheory.Localization.fullyFaithfulWhiskeringLeft`. One exact hit
  in `Mathlib.CategoryTheory.Localization.Predicate`; it is the general localization
  tool already represented by the proof dependency, not this item.
- Mathlib grep: `scalarPullback|scalar_pullback|Roos|roos` in `CategoryTheory`.
  Zero results.
- LeanSearch: "A natural chain map between finite coefficient pullback towers
  induces a diagonal map on both coordinates of the Roos cone and descends to a
  natural transformation on unbounded derived categories". Eight results included
  `Limits.PullbackCone.map`, `AlternatingFaceMapComplex.map`,
  `NatTrans.leftDerivedToHomotopyCategory`, and `Functor.rightDerivedNatTrans`.
  No result supplies this statement or its local coefficient formula.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for scalar/pullback and strict/cone
  combinations found general scalar exchange and unrelated cone modules; those
  do not state the completed strict tower assertion. The focused final names
  `ScalarPullbackStrictConeData|scalarPullbackGenerator|ScalarPullbackGeneratorFormula|
  scalarPullbackProductMap|ScalarPullbackAssociationFormula|scalarPullbackStrictConeNaturality`
  have no existing project/Mathlib matches.
- `grep -rn` of the item id in `lean/WeilConjectures` found no existing declaration.
  The same id was also searched in `lean/Sheaf`, with no match.

Validation: the final file compiled in both sandbox and library module contexts
through the required scompile.py wrapper (36.1 s and 28.9 s respectively). No errors
or unexpected warnings. All definitions are explicit, every variable and universe
is bound, and all lines are at most 100 characters. Only the item's lean field is
changed in its JSON copy. No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q49

This is the delivering worker's separate final rereading; the dispatch explicitly
forbids starting another agent and assigns independent review to the maintainer.
I reread the node and the complete module, including the displayed generator and
all composition/unit equations. The tensor scalars occur in the required order:
iota(b) times the residue of s, while the target p is p tensor 1. I checked that
both cone-coordinate equations use the same canonical product map and that the
shifted coordinate is evaluated at i-1. Naturality is in the actual chain-map and
derived-category functor types, rather than a restriction to resolution maps.
The descent equation uses the scalar counit on A_E(P) and explicitly asserts its
invertibility without requiring A_E(P) K-flat. Finally I checked both composition
squares and both unit equations: their domains, codomains, associator orientations
and multiplication unitors match the DAG's final sentence. During this rereading,
I restricted the ancillary good-representative and counit assertions to the Y
representatives and X pullback cones used by this node, and the product assertion
to X, avoiding unrelated universal assertions about other schemes. The final
version was recompiled cleanly after those changes. No node, dependency record,
statement correction or new independent notion is needed.
