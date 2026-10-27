## Worker report

The module `Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary` states the entire
unchanged node in the namespace `DerivedCategory`. All four theorems have `sorry`
proofs; their docstrings supply the corresponding steps of the accepted DAG proof.
Definitions contain actual Mathlib constructions. No statement correction, new node,
or dependency repair is needed.

Hypotheses and clauses, checked against the node:

- The abelian category is `{A : Type u} [Category.{v} A] [Abelian A]`, using
  `CategoryTheory.Abelian` from the Mathlib match for `def-sp-abelian`.
- The chosen derived category is `[HasDerivedCategory.{w} A]`, with independently
  bound object, category-morphism and derived-morphism universes. This uses
  `DerivedCategory` and `HasDerivedCategory` in the recorded module
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` for
  `def-weil-abstract-derived-category`.
- The objects and differential are `{M F : A} (d : M ⟶ F) (G : A)`.
  There is no projectivity, injectivity, enough-projectives, or enough-injectives
  hypothesis.
- `K=[M → F]` is directly Mathlib's
  `CochainComplex.mappingCone ((CochainComplex.singleFunctor A 0).map d)`.
  The cone has terms `M` in degree -1 and `F` in degree zero, with differential
  `+d`, under its canonical biproduct/single-complex identifications. No second
  two-term-complex definition is introduced. This is the same Mathlib expression
  wrapped by the existing `CochainComplex.monoCokernelComplex`; that wrapper's
  module also imports unrelated specialized ringed-site material, so this file
  uses the underlying Mathlib constructor directly.
- Objects in degree zero use `CochainComplex.singleFunctor A 0` before
  localization and `DerivedCategory.singleFunctor A 0` afterward. In the pinned
  Mathlib their compatibility is `singleFunctorIsoCompQ`, the identity isomorphism.
- `Ext¹(K,G)` is literally `Q.obj K ⟶ ((singleFunctor A 0).obj G)⟦(1 : ℤ)⟧`.
  `Ext⁰(K,G)` uses the canonically equivalent unshifted Hom `Q.obj K ⟶ S.obj G`.
- The specified quotient is `twoTermQuotient d`: negate the cone triangle's
  third chain map (which is the negative projection), apply `Q.map`, and compose
  with `Q.commShiftIso`. Its restriction to the shifted M summand is the positive
  identity, and its restriction to the F summand is zero. Thus it is the specified
  quotient, not an arbitrary connecting morphism or a sign-ambiguous choice.
- `twoTermBoundary d G` is a genuine additive homomorphism. Its forward map is
  exactly `δ ↦ twoTermQuotient d ≫ ((singleFunctor A 0).map δ)⟦1⟧'`, using
  `Preadditive.leftComp` and `Functor.mapAddHom`. Additivity is inherited from
  existing Mathlib constructions, with no postponed definitional obligations.
- The preceding arrow is `Preadditive.leftComp G d`, i.e. `θ ↦ d ≫ θ`.
  `twoTermBoundary_exact` states `Function.Exact` of this arrow and the boundary.
  Mathlib defines this as boundary-zero iff membership in the preceding image,
  so both directions of middle exactness are retained.
- `twoTermCokernelProjection d` is `mappingCone.descShortComplex` on the actual
  short complex `M → F → cokernel d`, mapped by the single functor. It is zero
  on the M summand and `cokernel.π d` on the F summand, exactly the canonical
  chain map specified in the node.
- `twoTermCokernelHom d G` is precomposition by `Q.map` of that projection
  after the single embedding. `twoTermCokernelHom_bijective` states its
  bijectivity. `twoTermCokernelHomEquiv d G` is the resulting `≃+`, constructed
  by `AddEquiv.ofBijective` from this specified additive map. Only the inverse
  proof/factorization is postponed; the forward map and the object are fixed.
- `twoTermDerivedHom_postcomp` quantifies over every `g : G ⟶ G'` and gives
  the postcomposition identity for the first arrow, the boundary, and the
  cokernel additive equivalence, with every input morphism quantified.
  The first identity is associativity, included because the node expressly
  requires naturality of both arrows of the displayed sequence.
- `twoTermSquareMap d d' a b h` is Mathlib's actual cone map on the single
  functor applied to the square `h : d ≫ b = a ≫ d'`. The equality passed to
  `mappingCone.map` is obtained from `h` and the functor's composition laws.
  `twoTermDerivedHom_square` gives naturality of all three arrows under every
  such square, using `Q.map twoTermSquareMap` on K and the actual
  `cokernel.map d d' a b h` on cokernels. Neither map is supplied arbitrarily.
  The forward naturality equations determine inverse naturality of the additive
  equivalence as well.

Sources read: `literature/stacks-project/derived.tex`, lemma-representable-homological
(Tag 0149, lines 386ff) and lemma-negative-exts (Tag 06XS(1), lines 8713ff).
The first supplies cohomological representable Hom exactness; the second gives
`Ext⁰(K,G)=Hom(H⁰(K),G)` in the present amplitude, with `H⁰(K)=coker d`.
The cone normalization was checked in Mathlib's `mappingCone.triangle` and
`inl_v_triangle_mor₃_f`: the latter has the negative identity on M, so our
explicit negation has the correct positive sign.

Dependency declarations and imports:

- Statement: `Mathlib.Algebra.Homology.DerivedCategory.Basic` provides
  `DerivedCategory`, `HasDerivedCategory`, `Q`, `singleFunctor`, and
  `singleFunctorIsoCompQ`, and exposes the ambient Mathlib abelian and
  triangulated structures. `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`
  provides `CochainComplex.mappingCone.descShortComplex`; the cone, its triangle
  and its square map come from its Mathlib prerequisites.
  `Mathlib.Algebra.Exact.Basic` provides `Function.Exact`.
- Proof-only imports explicitly carry the recorded proof plan:
  `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful` provides the full and
  faithful instances for `singleFunctor` (the match for
  `lem-weil-pbc-derived-single-fully-faithful`);
  `Mathlib.Algebra.Homology.DerivedCategory.ShortExact` provides
  `triangleOfSESδ`, `triangleOfSES`, and `triangleOfSES_distinguished` (the
  record for `lem-weil-pbc-complex-ses-triangle`);
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure` provides
  `DerivedCategory.TStructure.t` (the match for
  `def-sbc-standard-tstructure-derived-category`) and exposes
  `CategoryTheory.Triangulated.TStructure` (the match for `def-weil-t-structure`).
  The other proof matches, `CategoryTheory.Pretriangulated`, `IsTriangulated`,
  and `Pretriangulated.Triangle.yoneda_exact₂`/`yoneda_exact₃`, are in the
  public prerequisites of `DerivedCategory.Basic`. Each recorded signature
  and docstring was read in the local Mathlib source.

Edge cases checked mathematically before writing:

- If d=0, K is the direct sum F[0] ⊕ M[1]; the first arrow is zero and the
  boundary is injective on the M[1] summand. Degree-zero Hom is Hom(F,G), since
  Hom(M[1],G[0]) vanishes. The positive quotient convention gives δ, not -δ.
- If d is the identity, K is contractible, the first arrow is surjective,
  and the cokernel and derived Hom are zero.
- M=0 reduces the cokernel isomorphism to the fully faithful single embedding;
  F=0 gives K=M[1], degree-zero Hom zero and the boundary the shifted embedding.
- G=0 makes all Hom groups zero. No nonzero-object assumption occurs.
- The zero category and arbitrary independently sized abelian categories are
  admitted; there is no module-category, smallness-equality, or resolution
  restriction.

Searches (all on 2026-10-24, using prescribed msearch.py Q72/item wrapper):

- LeanFinder: "For a two term complex M to F in degrees minus one and zero the
  boundary Hom M G to derived Hom K G shifted is exact and Hom K G is Hom
  cokernel d G". Eight hits: short-exact-sequence `singleδ`, Ext exact sequences,
  Ext class compatibility, and `triangleOfSESδ`. None states this arbitrary
  differential's cone-boundary/cokernel result.
- Loogle: "CochainComplex.mappingCone, CochainComplex.toSingle₀Equiv,
  DerivedCategory.singleFunctor". Zero hits.
- Mathlib grep: `twoTerm|two_term|mappingCone|toSingle₀Equiv` in Algebra/Homology.
  Twenty-five reported hits, including the canonical mapping cone and its maps
  and natural-number-indexed single-complex Hom equivalences. No exact theorem.
- LeanSearch: "Derived category morphisms from two term complex to object in
  degree zero equal homomorphisms from cokernel and connecting boundary
  exactness". Eight hits: fromSingle₀Equiv, ConnectData, comp_δ, and short-complex
  homology constructors. No matching derived boundary/cokernel theorem.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `twoTerm|two_term|two-term` found specialized complexes and calculations,
  including the generic cone wrapper `monoCokernelComplex`, but not this theorem.
  The narrower search `twoTerm.*(Hom|[Bb]oundary)|two_term.*(hom|boundary)|
  monoCokernelComplex|mappingCone.*cokernel` likewise found no match.
  `grep -rn lem-sfb-two-term-derived-hom-boundary lean/WeilConjectures` found none.

Validation: prescribed `scompile.py` compiled this single file in both its sandbox
and final module identities cleanly (8.1 s and 3.3 s), after adding the required
`Function.Exact` import. There are no diagnostic probe lines, no auto-bound
implicits, no private/local definitions or notations, and no lines over 100 columns.

## Second reading by Q72

I reread the unchanged node and the completed module clause by clause. This is a
self-review: the dispatcher's explicit instruction forbids starting other agents;
the maintainer's independent review is still required. I do not claim a second
agent reviewed this file.

The abelian category and independent derived-category size are the inherited
binders. The differential and G are arbitrary. I verified the quotient sign against
Mathlib's actual cone-triangle formula rather than assuming its last map was q.
Exactness is for the actual precomposition arrow and the explicit additive boundary.
The degree-zero equivalence's forward function is the actual cokernel chain-map
pullback, and its inverse is determined by bijectivity, with no arbitrary chosen
comparison. Both naturality theorems include the preceding arrow as well as the
boundary and the cokernel equivalence; their source/target directions agree with
the contravariance in the differential square and covariance in G. The final
statements neither introduce nor silently assume resolutions. No node mismatch or
statement dispute was found. The only compile repair was the missing import for
`Function.Exact`; no mathematical statement changed.
