## Worker report

The module `Sheaf.Algebra.Homology.CoinductionPolynomialRefinement` states
`ModuleCat.coinduction_polynomial_refinement`, with its entire proof `sorry`.
It introduces no definitions. The node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:

- Commutative rings R, P, A: `{R P A : Type u}` with the three `CommRing` instances.
  A common ambient universe contains any finite collection of rings by enlargement;
  this is the same ordinary-module universe used by the recorded scalar extension API.
- The maps R → P → A: `(ρ : R →+* P) (ψ : P →+* A)`.
- The nonnegative number of variables and their ordered values: `(m : ℕ)` and
  `(g : Fin m → P)`. `Fin m` lists exactly m ordered variables.
- Q = P[y₁,…,yₘ]: `MvPolynomial (Fin m) P`.
- The evaluation quotient π: `MvPolynomial.eval g`. This standard ring homomorphism
  is the identity on constants and sends variable i to `g i`. Constants give its
  surjectivity, so no additional hypothesis on an arbitrary map is substituted.
- χ = ψπ: `ψ.comp (MvPolynomial.eval g)`.
- The structural map R → Q is
  `(MvPolynomial.C : P →+* MvPolynomial (Fin m) P).comp ρ`.
- Ordinary unbounded D(T): `DerivedCategory (ModuleCat.{u} T)`, using the existing
  canonical small-Hom localization for modules supplied by the imported library.
  No truncation or bounded subcategory appears.
- Derived coinduction C_B^T, including its B-action: `ModuleCat.derivedCoinduction`.
  Its definition is the total right derived `coextendScalars`; the recorded
  K-injective model has `(b • h)(b') = h(b'b)` and maps by postcomposition.
- Derived extension - tensor_T^L B: `ModuleCat.ordinaryDerivedExtendScalars`.
  Its recorded universal pair has the K-flat computation counit. This reuses the
  existing ordinary-module presentation of the change-of-rings dependency.
- The first displayed comparison is the first `Nonempty`: the composite extension
  from R to Q, coinduction along χ, and `shiftFunctor ... (m : ℤ)` is naturally
  isomorphic to extension along ρ followed by coinduction along ψ.
- The second comparison is the second `Nonempty`: coinduction along π is naturally
  isomorphic to extension along π followed by `shiftFunctor ... (-(m : ℤ))`.
  The conjunction asserts both exist. An isomorphism in a functor category is a
  natural isomorphism, so these are stronger than mere individual object comparisons
  only in exactly the way the node explicitly requests.
- Dependence on the order and g is allowed: both are theorem parameters, and no
  equation comparing different choices is imposed.
- There is no flatness, surjectivity of ψ, Noetherianity, nontriviality or boundedness
  binder. The theorem has no mathematical hypotheses beyond those in the node.

Statement dependencies read and reused:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.C`,
  `MvPolynomial.algHom_ext`; `Mathlib.Algebra.MvPolynomial.Eval`:
  `MvPolynomial.aeval`, `MvPolynomial.eval`. The latter directly represents π.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction`, with its full signature, construction docstring,
  `coinductionComplexFunctor`, and `derivedCoinductionModel` read.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the chosen localization and shift convention.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.ordinaryDerivedExtendScalars`, `ordinaryDerivedChangeOfRings`,
  `OrdinaryDerivedChangeOfRings` (universal pair and K-flat computation).

Proof dependencies are imported without `public` where not already public statement
imports: `PerfectRingComplexGeneral`, `CartierQuotientDerivedDual`,
`PerfectAlgebraCoinductionTensor`, `DerivedTensorSecondFactorFunctor`, Mathlib
`CategoryTheory.Adjunction.Unique` (and its Basic import), and upstream
`WeilConjectures.Algebra.Homology.KFlatModuleBaseChange`. The adjunction and
coinduction proof dependencies already occur in the public coinduction module.
The docstring gives all six node proof steps, including the one-variable free
resolution, algebra action, shift signs, induction, K-flat substitutions and final
shift cancellation.

Source read directly: `literature/stacks-project/dualizing.tex`,
`lemma-compute-for-effective-Cartier-algebraic` (0BZH) and `lemma-well-defined`
(0BZJ), including their proofs. The one-variable computation uses only the monic
regular element y−g; the additional Noetherian/surjectivity assumptions of the
surrounding polynomial-presentation theorem are not needed for this auxiliary
calculation when g is already supplied.

Edge cases checked before writing:

- m = 0: `Fin 0` is empty, the polynomial ring is canonically P, evaluation and
  constants are inverse, both shifts are zero and the comparisons become identities.
- Zero rings: no `Nontrivial` assumption appears; the free resolution, evaluation
  quotient and zero derived categories retain the asserted identifications.
- Rings with zero divisors, e.g. P = ℤ/4: y−g remains monic, hence regular; the
  leading-coefficient argument does not use a domain hypothesis.
- Nonflat P/R and nonsurjective ψ: the extension argument uses K-flat resolutions
  and the restriction/coinduction adjunction, which do not impose those restrictions.
- Arbitrarily unbounded inputs are covered by isomorphisms of the entire derived
  functors, not a list of bounded complexes or degreewise cohomology isomorphisms.
- Shift direction: Ext¹ for one evaluation variable gives [-1] on the second
  comparison, and cancellation gives [+m] on the first comparison.

Searches for an existing statement (2026-10-24):

- `msearch.py leanfinder`: “Derived coinduction along evaluation of finitely many
  polynomial variables is derived scalar extension shifted by minus the number of
  variables”. Eight hits, including Ext, Tor, derived linearity and polynomial
  derivations; none states this natural isomorphism.
- `msearch.py loogle`: `"DerivedCategory", "MvPolynomial"`: zero hits.
- `msearch.py leansearch`: “Derived coinduction along a polynomial evaluation quotient
  equals shifted derived extension of scalars”. Eight hits concerning ordinary
  polynomial evaluation, derivations and quotient rings; no derived comparison.
- `msearch.py grep`, Mathlib Algebra/Homology:
  `coinduct|polynomial.*[Dd]ual|[Dd]ual.*polynomial`: five hits, all the unrelated
  homotopy construction `mkCoinductive`.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  `coinduction_polynomial|coinductionPolynomial|coinduction.*refinement|coinduction.*[Ee]val`.
  Existing action/evaluation and graph/Koszul comparison modules appeared, plus a
  docstring citation of this node; no declaration states both node comparisons.
- `grep -rn lem-trf-coinduction-polynomial-refinement lean/WeilConjectures`:
  no hits. The upstream and project searches confirm the chosen full declaration
  name is unused and the node is not already stated by an exact match.

Validation: the prescribed `scompile.py Q71 lem-trf-coinduction-polynomial-refinement`
compiled this module in both sandbox and library mode, each in 1.6 seconds, with
no errors or unexpected warnings. All variables and the universe are explicit,
`autoImplicit` is false, and every line is at most 100 characters.
No statement dispute, missing notion, dependency repair or statement correction arose.

## Second reading by Q71

Author's second reading, with the original node and completed file reopened;
the independent maintainer review is separate, as prescribed for this dispatcher.
I checked each binder and both sides of both `Nonempty` natural isomorphisms.
The first source is D(R), its target is D(A), and its shift is +m after
coinduction; the second source is D(Q), target D(P), and shift is −m after
extension. The same `MvPolynomial.eval g` occurs in χ and in both factors of
the second comparison. Constants composed with ρ are the structural R → Q map.
The conjunction includes the complete second comparison. Both comparisons use
the existing dependency constructions, and no extra regularity, nonzero-ring,
Noetherian or resolution hypothesis is present. m = 0 and unbounded complexes
are retained. No mismatch was found and no node correction was made.
