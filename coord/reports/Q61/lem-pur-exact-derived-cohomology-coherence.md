## Worker report

The module `Sheaf.CategoryTheory.ExactDerivedCohomologyCoherence` states
`CategoryTheory.Functor.exactDerivedCohomologyCoherence`, with its sole proof `sorry`.
There are no new definitions and no changes to the mathematical node, its accepted split,
or its dependencies. The source read was Stacks derived.tex,
`lemma-right-derived-exact-functor` (Tag 015F), including its unbounded assertion and proof.
The additional coherence is the explicitly agent-formulated strengthening already in this node;
its seven-step kernel/quotient and localization proof is reproduced in the theorem docstring.

Hypotheses and clauses, matched against the node:

- Abelian categories A, B, C: the three explicit `Type` variables, `Category` instances and
  `Abelian` instances. Object, morphism and derived-localization universes are independent
  (`uA vA wA`, `uB vB wB`, `uC vC wC`). `HasDerivedCategory` implements the chosen morphism
  size in the recorded abstract-derived-category dependency, not a mathematical restriction.
- Exact functors F and G: `F : A ⥤ B`, `G : B ⥤ C`, with `Additive`, `PreservesFiniteLimits`
  and `PreservesFiniteColimits` for each, precisely the node's definition of exactness.
- Integer degree: `a : ℤ`. The derived cohomology functors are
  `DerivedCategory.homologyFunctor A a` and similarly for B and C.
- Termwise derived functors DF, DG and D(GF): the recorded
  `CategoryTheory.Functor.mapDerivedCategory` applied to F, G and their composite.
- Canonical theta, its existence, naturality on every derived morphism and representative
  independence: use the existing `mapDerivedCategoryHomologyFunctorIso` itself, a natural
  isomorphism `H_A ⋙ F ≅ DF ⋙ H_B`. No arbitrary isomorphism or comparison hypothesis is
  introduced. Reading its definition and `_hom_app_Q` shows that its hom on Q(K) is
  `F(lambda_A) ≫ t_F ≫ lambda_B.inv ≫ H_B(sigma_F.inv)`, exactly the node's normalization.
  Here `t_F` is the inverse of `mapHomologicalComplexHomologyIso`; the latter is built from
  `ShortComplex.mapHomologyIso` and the homology data of the three-term short complex.
  Its kernel and homology quotient normalization was checked in PreservesHomology.lean.
  This existing construction supplies the existence/normalization clauses; the new theorem
  supplies the remaining two equations, rather than duplicating the construction.
- Compositor c: the existing `mapDerivedCategoryCompIso F G` has precisely the direction
  `D(GF) ≅ DF ⋙ DG`; its `_fac` equation is the termwise-identity normalization.
- First displayed equation: the first conjunct universally quantifies K and reads
  `theta_GF ≫ H(c) = G(theta_F) ≫ theta_G`. Lean composition is left-to-right, so this
  is exactly the node's right-to-left mathematical composition equation.
- Arbitrary exact L and eta: the second conjunct universally quantifies `L : A ⥤ C`, all
  three exactness instances, `eta : F ⋙ G ≅ L`, and `K : DerivedCategory A`.
- d and second displayed equation: d is literally
  `(mapDerivedCategoryCompIso F G).symm ≪≫ mapDerivedCategoryNatIso eta`.
  The conjunct is `G(theta_F) ≫ theta_G ≫ H(d) = eta_H ≫ theta_L`, exactly as in the node.
- Arbitrary unbounded complexes: every K has type `DerivedCategory A`. There is no plus
  category, boundedness, resolution, faithfulness or invertibility assumption beyond those
  already inherent in the specified natural isomorphisms.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`, its complete class
  definition and docstring (lines 103–117), for `def-sp-abelian`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q` and its localization instance (lines 72–98), for
  `def-weil-abstract-derived-category`; `HomologySequence.lean` lines 34–43 give
  `homologyFunctor` and `homologyFunctorFactors`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `Functor.mapDerivedCategory`
  and `mapDerivedCategoryFactors` (lines 38–48 and their docstrings), the recorded exact
  functor dependency. The public upstream extension imports this module.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryNatIso` and `_fac`, `mapDerivedCategoryCompIso` and `_fac`,
  `mapDerivedCategoryHomologyFunctorIso` and `_hom_app_Q` (definitions and signatures
  read in lines 103–213 and 258–302). These are existing real constructions.
- Proof-only imports: `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
  (`Functor.preservesHomologyOfExact`, `ShortComplex.mapHomologyIso` and its normalization
  and naturality); `Mathlib.CategoryTheory.Localization.Predicate` (`lift`, `Lifting`,
  `liftNatTrans`, `liftNatIso`, `natTrans_ext`, lines 278–363). These are the recorded
  matches of the node's homology-preservation and localization proof dependencies.
- Proof-only upstream `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso`
  supplies `mapDerivedCategoryHomologyFunctorIso_hom_app_naturality`, read with its full
  signature/proof, for the eta step. It proves only that step, not the composite equation.

Edge cases checked: a = 0 and negative a are included by ℤ; the zero complex, zero functors
and zero abelian category require no exclusions; identity F or G and eta = identity are
included. The equations have the right arrow endpoints even for the zero case. No extra
universe equality was imposed. Composite finite-limit/colimit preservation is supplied
explicitly with Mathlib's `comp_preservesFiniteLimits F G` and
`comp_preservesFiniteColimits F G`, rather than assumed or enabled by a file-local instance.
`set_option autoImplicit false` rules out auto-bound variables.

Searches actually made (msearch.py, Q61/item, with WEIL_SANDBOX set to this sandbox):

- LeanFinder: "Exact functors on unbounded derived categories commute with cohomology
  naturally and coherently for composition"; 8 hits, principally derived-functor
  factorization and Ext functoriality; none states the full composite/eta coherence.
- Loogle: `DerivedCategory.homologyFunctor, Functor.mapDerivedCategory`; service returned
  zero hits and unknown identifier `Functor.mapDerivedCategory`, recorded as such.
- LeanSearch: "Canonical homology isomorphism for derived exact functor compatible with
  composition"; 8 hits, including ShortComplex.mapHomologyIso' and factorization laws;
  no complete match.
- Mathlib grep: `mapDerivedCategory.*[Hh]omology|mapHomologicalComplexCompIso|mapHomologyIso`
  under Algebra/Homology; 8 hits for short-complex homology and complex compositors.
- Direct rg over lean/WeilConjectures and lean/Sheaf for derived/cohomology comparison
  names found the existing canonical construction used here and the eta naturality
  theorem. Direct rg for `HomologyFunctorIso.*[Cc]omp|[Cc]omp.*HomologyFunctorIso` found
  single-functor and other special-case results, but no full composition equation.
  Read the candidate upstream ExactFunctor and MapDerivedCategoryHomologyNatIso modules,
  plus the relevant portions of SubterminalModuleLocalCalculus. Grep for this exact node
  id in lean/WeilConjectures returned none. The fresh declaration name was also searched
  in Mathlib, both project trees and dag/lean_names_upstream.json: no collision.

No statement fault or STATEMENT-DISPUTED issue was found. No new nodes or dependency
repairs are needed. The module compiled cleanly with scompile.py, both its sandbox pass
and its named-library pass (1.1 s and 1.2 s), with no unexpected warning. A diagnostic
scratch probe was also compiled in module mode; it is outside the delivered lean tree.

## Second reading by Q61

This is the dispatcher's single-worker rereading; the maintainer's independent reading
is still to follow, as prescribed in the brief. I reopened the completed module and node
and checked both arrow orientations: theta_GF followed by H(c), and G(theta_F) followed
by theta_G followed by H(d). In particular d uses c inverse before D eta, not the opposite
compositor. The eta component is evaluated at H_A(K), and theta_G at DF(K). The selected
existing theta points F(H) to H(DF), whereas the complex homology comparison points the
opposite way; the definition's inverse and representative formula confirm the required
normalization. The theorem quantifies arbitrary L and eta in its second conjunct and
arbitrary derived K in both clauses. The only adjustment found during elaboration was
that composite preservation is not a globally active instance; passing the two existing
Mathlib proofs explicitly fixed this without adding a hypothesis or a local instance.
