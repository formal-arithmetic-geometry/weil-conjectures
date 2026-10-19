## Worker report

The module `Sheaf.TraceFormula.UpperShriekBoundedCoherent` states the two clauses
of `lem-trf-upper-shriek-bounded-coherent`. Both theorem bodies are `sorry`;
there are no definitions, helper existence assumptions, or proved theorems.
The node copy changes only `lean` and lists both declarations.

Source read: `literature/stacks-project/dualizing.tex`, lines 4411–4445,
Tag 0BZK, `lemma-shriek-boundedness`, especially (2) and its polynomial-factorization
proof. Part (1) supplies bounded-below preservation, while (2) supplies bounded-above
preservation for a perfect map; their bounded coherent consequence is precisely
this node. The node already spells out the polynomial-perfectness condition.
No statement correction or disputed statement was needed. No repair note exists
for this item in the shared checkout.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings: `{R A : CommRingCat.{u}}`, with arbitrary explicit universe `u`.
- Both rings Noetherian: `[IsNoetherianRing R] [IsNoetherianRing A]`.
- The map and its finite type: `(φ : R →+* A) (hφ : RingHom.FiniteType φ)`.
- A polynomial presentation: `(n : ℕ) (p : MvPolynomial (Fin n) R →+* A)`
  with `_hp : Function.Surjective p` and `_hc : p.comp MvPolynomial.C = φ`.
  These are explicit witnesses for the presentation appearing in the node, allowing
  every presentation for which the required perfectness holds, including zero variables.
- Perfectness of A over this presentation: `_hperfect` is the recorded predicate
  `DerivedCategory.IsPerfectRingComplex` applied to the degree-zero derived object
  of `(ModuleCat.restrictScalars p).obj (ModuleCat.of A A)`. This is the actual
  regular A-module with its P-action induced by the specified ring map p. It is
  not a free P-module, an arbitrary P-module, or an independently chosen action.
- The algebraic upper-shriek functor: `S : AlgebraicGeometry.AlgebraicShriekCalculus.{u}`
  and `S.shriek φ hφ`, exactly the package recorded by the statement dependency.
  Its `polynomialModel` field identifies the chosen functor with scalar extension,
  derived coinduction with its A-action, and shift by n. The package is quantified
  explicitly, not extracted from its postponed existence theorem. The conclusion
  holds for every allowed choice; no further compatibility condition is assumed.
- Arbitrary input: `K : AlgebraicGeometry.algebraicShriekD R`.
- Bounded cohomology: `_hbounded : ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b`.
  Mathlib's `DerivedCategory.isGE_iff` and `isLE_iff` identify these with vanishing
  of cohomology below a and above b. No order restriction on chosen bounds is added.
- Finite generation in every degree: `_hfinite : ∀ i : ℤ, Module.Finite R
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)`.
- The main conclusion in `shriek_bounded_finite_homology` is the conjunction of
  existential lower and upper cohomological bounds for `(S.shriek φ hφ).obj K`
  and `Module.Finite A` for each of its cohomology modules, indexed by all integers.
- The explicit “in particular” is `shriek_unit_bounded_finite_homology`, with the
  same ring-map and perfect-presentation hypotheses. It applies the same conclusion
  to `(DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)`,
  the regular module in degree zero. This second theorem has no input K and no
  assumed boundedness or finiteness conclusion.

Dependency declarations read and used:

- `Sheaf.TraceFormula.AlgebraicShriekCalculus`:
  `AlgebraicGeometry.AlgebraicShriekCalculus` (full structure and its docstring),
  particularly `shriek`, `polynomialModel`, `coinductionAdj`, `coinductionModel`,
  together with `algebraicShriekD` and `algebraicShriekModuleDerived`.
  The latter supplies the standard localization universe `u+1` for modules in `u`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, the bounded finite-projective model
  predicate with an independent localization universe.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, retained as the recorded public
  dependency; the shriek calculus supplies the required action-bearing specialization
  as derived coinduction, so no private RHom construction is made here.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; cohomology and degree-zero objects use
  `DerivedCategory.homologyFunctor` and `DerivedCategory.singleFunctor`.
  `DerivedCategory.IsGE` and `IsLE` are the standard t-structure bounds.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, exactly the dependency's
  recorded notion for a bare ring homomorphism.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` and `MvPolynomial.C`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.

All stated proof dependencies are imported, with proof-only imports non-public:
`RingPseudoCoherent`, `Mathlib.Algebra.Module.Projective`, `BoundedFlatKFlat`,
`DerivedChangeOfRingsCochainModel`, `AffineProjectiveComplexDerivedHom`,
`Mathlib.RingTheory.Flat.Basic`, `NoetherianPseudoCoherentCohomologyCriterion`, and
`Mathlib.RingTheory.Noetherian.Basic`; finite-type Noetherianity and perfect complexes
are already among the public statement dependencies. The main docstring transcribes
all seven proof steps, including the lower truncation, finite Hom calculation,
restriction of scalars and final degree-zero specialization.

Edge cases checked against the statement and Stacks proof:

- `n = 0` is allowed (`Fin 0`); no positive-relative-dimension assumption appears.
- Zero rings and zero modules are allowed; there is no `Nontrivial` assumption.
  In particular, the regular module is still generated by 1 over a zero ring.
- Zero complexes satisfy all vanishing and finite-generation conditions; arbitrary
  lower/upper bounds are allowed without an unnecessary `a ≤ b` hypothesis.
- The input is only bounded with finite cohomology, not assumed perfect or flat.
  Neither flatness nor finite Tor amplitude of the input has been added.
- Cohomological bounds are indexed by all integers, and the proof's shifted interval
  is `[a-v-n,b-u-n]`, consistent with the cohomological shift convention.
- Rings and modules range over arbitrary `u`; the standard larger localization
  universe is inherited from the calculus, with no equality between the module
  universe and derived morphism universe imposed.

Searches actually run (all with this item and group through `msearch.py`):

- LeanFinder: “Algebraic upper shriek of a perfect finite type map of Noetherian
  rings preserves bounded finitely generated cohomology”. Eight hits, concerning
  locally Noetherian schemes, finite morphisms, finite type sheaves, finite
  generation in algebra towers, and cotangent modules. No matching shriek theorem.
- Loogle: `"shriek"`. Zero hits.
- Mathlib grep: `upperShriek|shriek|BoundedCoherent`. Zero hits.
- Direct `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` for bounded
  coherent/finite cohomology and shriek boundedness: related perfect-complex and
  étale/pro-étale constructibility statements, no algebraic upper-shriek result.
- Direct `grep -rn` of upstream for the exact node id: no match.
- Direct `rg` of `dag/lean_names_upstream.json` for the node id and an algebraic
  shriek boundedness name: no match.
- Direct `rg` in Mathlib, upstream and `lean/Sheaf` for the proposed
  `algebraicShriek_bounded` / shriek finite-homology names: no match.
- Read Mathlib's `TStructure.bounded`, `DerivedCategory.IsGE`, `IsLE`,
  `isGE_iff` and `isLE_iff`; boundedness is expressed directly with these existing
  predicates rather than introducing a second bounded-coherence notion.

Validation: the prescribed `scompile.py Q22 lem-trf-upper-shriek-bounded-coherent`
compiled the sandbox module and its library-path overlay cleanly, with no errors
or unexpected warnings (reported file times 1.9 s and 2.1 s). All universes and
variables are bound explicitly, and every Lean source line is at most 100 characters.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
