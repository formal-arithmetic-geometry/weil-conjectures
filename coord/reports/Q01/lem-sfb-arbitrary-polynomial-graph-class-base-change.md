## Worker report

The module `Sheaf.Algebra.Homology.ArbitraryPolynomialGraphClassBaseChange` states
`lem-sfb-arbitrary-polynomial-graph-class-base-change` in four named theorems. All four
proofs are exactly `by sorry`; there are no new definitions, axioms or instances.
The original mathematical statement and proof are unchanged.

Read the item, every statement dependency and its recorded Lean declaration (or the
Mathlib match), the stage rules, the example compact-object module and its current
upstream replacement, and Stacks `dualizing.tex`, the proofs and statements of
`lemma-relative-dualizing-noetherian` and `lemma-base-change-relative-dualizing`.
The source explicitly gives arbitrary-ring flat finite presentation and arbitrary
base change in 0E2F. Exact ordered-class equality is the agent refinement already
identified by the item's source and nine-step proof; it is not attributed verbatim
to Stacks. The existing diagonal-data module specifies that refinement precisely.

### Hypotheses and objects

- Arbitrary commutative rings and their ring map: `{R B : Type u}`,
  `[CommRing R] [CommRing B] [Algebra R B]`. An algebra structure specifies exactly
  the unital homomorphism R -> B; no field, Noetherian or nonzero assumption occurs.
- Flatness and finite presentation: `[Module.Flat R B]` and
  `[Algebra.FinitePresentation R B]`. The recorded `RingHom.Flat` definition and
  `RingHom.flat_algebraMap_iff` identify the former with flatness of this ring map.
- Nonnegative n, ordered variables and the polynomial surjection: a
  `C : PolynomialKoszulChart R B` supplies `C.n : ℕ`, coordinates indexed by `Fin C.n`,
  and `C.quotient` with `C.surjective`. `Function.Bijective C.coordinates` specifies
  an ordinary polynomial algebra, up to its specified algebra isomorphism, rather
  than a genuinely localized polynomial chart. Every presentation in the item is
  represented by coordinates = identity, localization element = 1. The ambient
  carrier need not literally be the implementation of `MvPolynomial`; this avoids
  replacing the existing chart notion by a duplicate.
- Ordinary unbounded derived categories, L and C: `C.coefficient` is the single
  complex on `⋀[C.P]^C.n (KaehlerDifferential R C.P)` in degree `-C.n`.
  The existing `C.coefficientShiftIso` identifies it with Omega^n[n].
  `C.model` is `ModuleCat.derivedCoinduction C.quotient.toRingHom` applied to this
  coefficient. Coinduction uses its existing K-injective construction and retains
  the precomposition action; it is not an arbitrary chosen right adjoint.
- Q, p1, C1: `C.firstPullback` is the existing K-flat derived scalar extension of
  `C.model` along the first inclusion B -> B tensor_R B.
- T, q and e: the existing `C.graphQuotient` and `C.graphEvaluation` have domain
  `C.P ⊗[R] B`; their definitions are the quotient tensor identity and its composite
  with multiplication. `C.graphEquations` is the ordered tuple t_i - bar(t_i).
  `C.graphCoefficientComplex` is the base-changed top differential line in degree -n,
  with `C.graphVolume` its ordered volume.
- R' and the scalar-extended objects: in the second theorem, S is R', D is B',
  E.P is P', and F is the recorded `KoszulDiagonalChartChange C E`.
  `hbase` is the pushout of R -> B by `F.base`; `hquotient` is the pushout of
  P -> B by `F.ambient`. Thus D = B tensor_R S, and E.P = P tensor_R S through
  their canonical identifications; the chart structure requires the same number
  and order of coordinates. The latter is precisely the scalar-extended polynomial
  presentation: its coordinate equation fixes the image of every polynomial
  variable, and `ambient_comm` fixes the coefficient map. For any R -> S the usual
  tensor-algebra presentation supplies such E and F, including nonflat maps.
  This carrier-independent pushout encoding is the scalar-extension branch of
  the already recorded diagonal-data interface. No flatness or finite-presentation
  hypothesis on the target is added: these follow by base change from the source.
- The top coefficient comparison: F.differential is semilinear over F.ambient, and
  F.volume sends the specified ordered volume to the target volume. For polynomial
  charts the top line is free rank one, so this specifies the differential comparison
  on the entire line; it is not a choice of a generator up to an unspecified unit.

### Conclusions, clause by clause

1. `arbitraryPolynomialGraphClass_exists` supplies
   `κ : C.diagonalHom ≅ koszulDiagonalUnit B` with
   `IsKoszulDiagonalNormalization C κ`. Expanding that existing predicate gives
   the graph exchange beta, its invertible scalar/restriction and coefficient
   comparisons, the evaluation-counit equation for beta, the graph trace tau,
   its top-functional normalization and the equation composing beta, canonical
   coinduction transitivity and tau to kappa. This includes the first identification
   in the item; no independent invertibility premise is substituted for it.
2. `C.diagonalClass κ` is exactly the already defined coinduction adjunct of
   `κ.inv`, including the canonical comparison of the degree-zero source. The
   first theorem's second conjunct is `IsIso (relativeDualizingModuleClassMap ...
   (C.diagonalClass κ))`. This is the actual transposed multiplication map
   B -> RHom_Q(B,C1) defined from multiplication of the diagonal algebra, not
   merely an assertion that the two objects happen to be isomorphic. Its underlying
   Q-object is the RHom in the item; the coinduction interpretation restores its
   B-action and conservative restriction detects its invertibility.
3. `arbitraryPolynomialGraphClass_baseChange` supplies an isomorphism c together
   with `F.IsComparison c`. That predicate fixes the coefficient map as the scalar
   mate of the ordered differential map, asserts the required Tor comparison is
   invertible and equates the extended evaluation counit with the target counit.
   Thus it is the specified counit exchange, not an arbitrary model isomorphism.
4. For every normalized source and target kappa, the scalar theorem asserts
   `F.PreservesClass κ κE c`. This existing predicate supplies the canonical
   degree-zero diagonal isomorphism and proves the actual equation
   `extension.map (C.diagonalClass κ) ≫ F.firstPullbackMap h c =
   d.hom ≫ E.diagonalClass κE`.
   Its `d` is the source comparison B tensor_Q^L Q' -> B' in the informal statement;
   `F.firstPullbackMap h c` is the informal comparison of C1, built from c and
   scalar tensor associators. This is exactly the requested equality after identifying
   its source by that canonical isomorphism. There is no undetermined unit or sign.
   Existence of normalized target kappa is the first theorem applied to the scalar
   presentation, whose flatness and finite presentation follow from `hbase`.
5. `arbitraryPolynomialGraphClass_identity` identifies any normalized identity c
   with `koszulDiagonalExtensionId`. Combined with the class square this is the
   identity law on the specified class. Ring and ambient maps are required to be
   identities; these specify the identity chart change, rather than restricting
   the class theorem to a special base extension.
6. `arbitraryPolynomialGraphClass_composition` identifies the composite of cF and
   cG with cFG under `koszulDiagonalExtensionComp`. Its maps on base, quotient and
   polynomial rings are explicitly required to compose, with the two pairs of
   scalar-extension pushouts. Hence this is exactly the successive-base-extension
   situation; the composite pushouts follow by pushout pasting. Each c is required
   to be the recorded counit exchange. The equation and the preceding actual class
   squares give the successive-extension law for xi itself. These are equations
   using the canonical scalar associator, not an existential coherence witness.
7. No theorem assumes that B is perfect over Q or that any scheme is proper;
   no trace-pair map or proper-adjoint identification appears.

### Dependencies and imports

Recorded statement declarations used, either directly or through the public imports
of the existing diagonal-data module:

| Node / notion | Module and declarations |
| --- | --- |
| flat maps | `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`; `Mathlib.RingTheory.Flat.Basic`: `Module.Flat` |
| finite presentation | `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` |
| polynomial algebra | `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; `Mathlib.Algebra.MvPolynomial.Eval`: evaluation |
| derived category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q` |
| coinduction | `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`: `ModuleCat.derivedCoinduction`, `ModuleCat.derivedCoinductionAdjunction` |
| ordinary derived internal Hom | `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`: `CategoryTheory.ordinaryModuleDerivedInternalHom`; the closed Hom used by `relativeDualizingModuleClassMap` |
| derived tensor | `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`: `DerivedCategory.exists_derivedTensor_second_factor_functor`; `AlgebraicGeometry.relativeDualizingDerivedExtension` in the imported affine comparison module |
| differentials | `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D` |
| exterior powers | `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra`; `Mathlib.LinearAlgebra.ExteriorPower.Basic`: `exteriorPower.ιMulti` |
| module tensor | the Mathlib leaf `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; the universal property is `TensorProduct.lift` in `.Basic` |
| perfect coinduction exchange | `Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange`: `ModuleCat.perfectCoinduction_torIndependent_exchange`, with the normalized scalar-pair interfaces |
| normalized chart data | `Sheaf.Algebra.Homology.PolynomialKoszulDiagonalData`: `PolynomialKoszulChart` and its coefficient, model, firstPullback, graph, diagonalHom and diagonalClass declarations; `IsKoszulDiagonalNormalization`; `KoszulDiagonalChartChange`, `IsComparison`, `PreservesClass` |
| canonical scalar identity/composition | `Sheaf.Algebra.Homology.PolynomialKoszulDiagonalSystem`: `koszulDiagonalExtensionId`, `koszulDiagonalExtensionComp` |

Added the already landed `def-sfb-polynomial-koszul-diagonal-system` to stmt_deps
solely for its two real canonical scalar identifications. No Noetherian assignment
or compatibility-system hypothesis is used. No existing node is repaired, and no
new node or private copy of a definition is introduced.

Proof-only imports also include the Mathlib matches for flat base change, flat tensor
exactness, exterior-power basis, right-adjoint composition and mate pasting. The
existing perfect-coinduction exchange module is imported for proof step 2 and the
scalar clause. The proof dependencies `lem-sfb-arbitrary-polynomial-dual-properties`,
`lem-trf-polynomial-graph-coinduction`, `lem-sfb-koszul-evaluation-pasting` and
`lem-sfb-flat-algebra-derived-module-tensor-exchange` currently have no recorded
Lean module and therefore cannot yet be imported; their ids and uses are retained
in the unchanged DAG proof and in the relevant theorem docstrings. They are proof
inputs, not missing objects needed to type these statements.

### Edge cases and scope

- n = 0 is permitted by `C.n : ℕ`, `Fin 0`, and the existing empty-wedge and
  degree-zero definitions. It includes a nontrivial flat quotient R -> B; it is
  not silently replaced by the identity ring map.
- Zero rings are allowed: no `Nontrivial` instance or field hypothesis occurs.
  Polynomial coordinate bijections, top volumes, isomorphisms in the zero module
  category and pushouts still have their usual meanings.
- A nonflat base extension, e.g. Z -> F_p, is permitted; no flatness hypothesis
  on S, F.base or F.ring appears.
- The dual-numbers example B = k[z]/(z²) is covered, even though its diagonal need
  not be perfect. Only the source algebra is assumed flat and finitely presented.
- All ring carriers can be put in one sufficiently large universe u, as in the
  existing chart interface. Test rings are in the same universe as the given rings,
  not an independently smaller universe. There are no auto-bound variables, local
  notation, private helpers or file-local instances.

### Searches

- `msearch.py`, leanfinder: "Normalized polynomial graph Koszul diagonal class is
  preserved by arbitrary scalar extension of a flat finitely presented commutative
  algebra". Eight hits: `Algebra.SubmersivePresentation.baseChange`,
  `Algebra.kerTensorProductMapIdToAlgHomEquiv`, standard-smooth base-change results,
  presentation Jacobian base change, cotangent exactness and cotangent complex base
  change. None states a normalized derived graph class or its scalar compatibility.
- `msearch.py`, loogle: `"coind", "baseChange"`: zero hits.
- `msearch.py`, grep: `koszul.*[Dd]iagonal|[Dd]iagonal.*koszul|coinduc.*baseChange|baseChange.*coinduc`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for arbitrary polynomial graph,
  graph class base change, `IsKoszulDiagonalNormalization` and `PreservesClass`:
  only the existing diagonal-data and diagonal-system definitions; no theorem
  states the item. The exact item id has no occurrence in `lean/WeilConjectures`.
- Read the full existing diagonal-data and system declaration signatures and their
  normalization docstrings. They supply the notions used here but assert no
  existence theorem, so they are reused rather than recorded as an existing match.

### Validation

`scompile.py Q01 lem-sfb-arbitrary-polynomial-graph-class-base-change` compiled
both its private sandbox view and the actual library module successfully, in 8.4 s
and 6.7 s respectively. No errors or non-sorry warnings were reported. All lines
are at most 100 characters. The delivery dry run and final delivery are run through
the prescribed wrapper, without direct repository edits, direct Git commands or
a global build.

The first delivery dry run passed server preflight and compilation (commit 233951de50a).
The final packet also makes the two recorded tensor/exchange statement imports public
and lists the four declarations in its module docstring; it is checked again before push.

No statement dispute or statement correction was needed.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
