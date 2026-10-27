## Worker report

This is stage 2, not a repeat of the reviewed Q17 stage-1 split. The live node has
`reviewed` from Q17 but no `lean` or `reviewed_lean`. The previous worker's stale
stage-1 objection therefore does not apply. The statement and all original DAG
fields are unchanged; only `lean` is added.

The module `Sheaf.RingTheory.InjectiveStandardResolutionQuotients` constructs
`Algebra.CotangentResolution.quotientAugmentation` as a genuine simplicial ring
pushout and states `isPolynomialResolution_quotient_of_injective` with `sorry`.
The helper is the quotient construction belonging to this very node, not an
independent notion, and is listed in `lean.declarations`. No new nodes or
dependency repairs are needed.

Hypothesis and conclusion correspondence:

- Commutative rings A, B, C and homomorphisms A → B → C are the explicit
  `{A B C : CommRingCat.{u}}`, `f : A ⟶ B`, `j : B ⟶ C` binders.
- Injectivity of B → C is exactly `hj : Function.Injective j`.
- The standard augmented simplicial A-algebras resolving B and C are `P` and
  `Q`, with `hP : IsStandard P` and `hQ : IsStandard Q`. These predicates
  identify their terms, coefficient maps, augmentations, faces and degeneracies
  with the dependency's actual recursively defined standard polynomial formulas.
  They encode the specified standard resolutions, rather than imposing an
  additional mathematical condition on A, B or C.
- The standard functoriality map is `h : AugmentedMap ... P Q`, with the ring
  square having left arrow `𝟙 A` and right arrow `j`. The `hh` hypothesis
  identifies every component with the dependency's `standardSquareMap`, hence
  completely specifies the canonical map. There is no arbitrary map hypothesis.
  Instantiating these data with `Coherence.standard`, `standard_spec`,
  `standardMap` and `standardMap_formula` gives the dependency's chosen data.
- The quotient is `quotientAugmentation f j P Q h`. Its algebra is
  `pushout h.map P.augmentation`, whose terms are Q_n ⊗_(P_n) B: colimits in
  functor categories are pointwise, and pushouts of commutative rings are tensor
  products. Its B-structure is `pushout.inr`. Its augmentation is
  `pushout.desc Q.augmentation (const.map j)`, uniquely specifying the map
  q ⊗ b ↦ ε_Q(q) j(b), with compatibility from `h.augmentation`.
- Every quotient term is a polynomial B-algebra: the first conjunct of the
  dependency's `IsPolynomialResolution`, quantified over all `n : ℕ`, gives an
  isomorphism from `MvPolynomial E B` commuting with the coefficient map.
- Every quotient augmentation is surjective: its second conjunct is exactly
  `∀ n : ℕ, Function.Surjective (...)`.
- The quasi-isomorphism to C[0] is its final conjunct
  `QuasiIso (additiveAugmentation ...)`. This is the dependency's alternating
  face complex extended along `ComplexShape.embeddingDownNat`, so degree n
  becomes cochain degree -n and all positive terms vanish. Although the
  predicate tests the underlying abelian-group complex, the augmentation and
  operators preserve the B-structure. Forgetting B-modules is exact and reflects
  isomorphisms, so this says exactly that the augmentation of B-module complexes
  is a quasi-isomorphism. This does not replace the given complex or weaken the
  condition.
- No flatness of C/B, finiteness of variables, nonzero-ring condition or
  injectivity of A → B is required. No derived-category instance is needed.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Augmentation`, `AugmentedMap`, `IsStandard`,
  `standardSquareMap`, `IsPolynomialResolution`, `additiveAugmentation`,
  `negativeComplex`; the full dependency module and docstrings were read.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval`. The polynomial
  notion is used through `IsStandard` and `IsPolynomialResolution`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct` and its generators;
  `Mathlib.LinearAlgebra.TensorProduct.Basic`: `TensorProduct.lift`, `ext'`;
  `Mathlib.LinearAlgebra.TensorProduct.Map`: `LinearMap.rTensor`. The tensor
  object is used through the equivalent commutative-ring pushout construction,
  imported from `Mathlib.Algebra.Category.Ring.Colimits`.
- Proof dependencies with recorded declarations are imported: the coherence
  module, `Mathlib.RingTheory.Flat.Basic` and
  `Mathlib.RingTheory.TensorProduct.MvPolynomial` (the latter supplies the
  polynomial scalar-extension computation). Tensor and polynomial definitions
  are also available from the public statement imports.
- `lem-sfb-simplicial-flat-base-change-quasi-iso` has no Lean record or Mathlib
  match in the read clone, so no proof import exists yet. Its exact use remains
  in the theorem's complete proof docstring; no missing statement notion results.

Source checked: `literature/stacks-project/cotangent.tex`, remark-triangle,
lines 1407–1484, Tag 08SD. The diagram has Q_n = A[...A[C]...], and the node
correctly uses Q resolving C/A. The preceding source prose says “over B”; as
already explained in Q17's review, the diagram and tensor calculation identify
this as a source typo. The node needs no statement correction.

Edge cases checked before writing: zero rings (including the all-zero case),
A → B noninjective (for example Z → Z/2 with j the identity), identity j, n=0,
empty complementary variable sets, arbitrary infinite variable sets and
nonflat injective B → C. The last case includes the diagonal embedding
Z → Z × Z/2: tensor resolution acyclicity uses flatness of each Q_n over P_n,
not flatness of C over B. Empty complements yield the constant polynomial ring;
zero-ring cases remain meaningful without a Nontrivial hypothesis. All three
rings can be placed in a common universe by the usual universe lift; no bound
on cardinality or variables is introduced. Explicit universes and
`set_option autoImplicit false` prevent accidental binders.

Searches performed using the prescribed msearch wrapper:

- LeanFinder: “For an injective ring map B to C the quotient of standard
  simplicial polynomial resolutions Q tensor over P with B is a polynomial
  resolution of C”. Eight hits, headed by
  `Algebra.Presentation.tensorModelOfHasCoeffsInv`,
  `tensorModelOfHasCoeffsHom`, and `Algebra.PreSubmersivePresentation.baseChange`.
  These concern ordinary polynomial presentations, not the simplicial quotient
  resolution and its acyclicity; no exact match.
- Loogle: `"SimplicialObject", "MvPolynomial"`: zero hits.
- Mathlib grep: `standardResolution|polynomialResolution|simplicial.*polynomial|polynomial.*simplicial`:
  five hits, all in representation-theoretic standard resolutions; no match.
- LeanSearch: “An injective map B to C induces standard simplicial polynomial
  resolutions whose pushout over the resolution of B is a polynomial B algebra
  resolution of C”. Eight hits: injective resolutions of categorical objects and
  polynomial pushout instances; no simplicial quotient-resolution theorem.
- Project and upstream rg: `CotangentResolution|IsPolynomialResolution` and
  standard/quotient-resolution patterns found the coherence module, ordinary
  scalar extension in `TorIndependentCotangentBaseChange`, and transitivity
  modules. The former tensors over the constant base A and assumes Tor
  independence, so is a different assertion. The construction here tensors
  over the varying simplicial ring P. No existing exact theorem was found.
- Project and upstream rg for `quotientAugmentation|standardQuotient|isPolynomialResolution.*[Ii]njective|injective_standard`:
  only unrelated quotient augmentations in other namespaces. No name collision.
- Exact blueprint-id search in `lean/WeilConjectures`: no match.

No STATEMENT-DISPUTED flag and no node fault affecting the statement.

## Second reading by N0

The dispatcher prohibits starting other agents, so this is the author's separate
second reading; independent review belongs to the maintainer. I reopened the
node and compared it with the module. The two standardness predicates cover
all operators, not just polynomial terms. The `hh` equation is needed: without
it an arbitrary augmented map would be stronger than the specified standard
case. Both legs of the pushout originate at P, so the coefficient ring is B
and the tensor base is P_n, rather than A. The augmentation is the canonical
one, and its structural triangle is checked by the pushout computation, with
no postponed data. The reused resolution predicate contains all three clauses;
its additive test is equivalent to the B-linear quasi-isomorphism assertion
because this quotient retains its B-action. No source hypothesis or case is
lost. The single postponed theorem has a proof docstring covering the five
DAG proof steps. No statement correction, new node or dependency repair is
necessary.
