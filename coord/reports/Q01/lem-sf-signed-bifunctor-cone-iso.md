## Worker report

The module `Sheaf.CategoryTheory.SignedBifunctorConeIso` states
`CochainComplex.exists_signedBifunctorConeIso`. Its only theorem has proof `sorry`.
The two helper definitions `bifunctorHomConeY` and `bifunctorHomConeX` are real
composites of the canonical shift degree isomorphism with the existing cone
projections. They introduce no replacement complex or independently chosen maps.
The node changes only in `lean`; there are no new nodes, dependency repairs,
statement corrections, or disputed statements.

Source read: Stacks `sites-cohomology.tex`, Tag 08JC,
`lemma-RHom-triangulated` (lines 8948 onwards). Its proof reduces to termwise
split Hom and says “Details omitted.” The node gives the explicit general
separately additive calculation; the module docstring carries all eight steps.
I read `BifunctorHomComplex.lean`, including its differential, projections,
precomposition map and composition law, and the Mathlib cone, shift and
commuting-square map signatures and docstrings.

Hypothesis and clause correspondence:

- The abelian categories A, B, C are `[Abelian A] [Abelian B] [Abelian C]`, with
  separately bound object universes u₁,u₂,u₃ and morphism universes v₁,v₂,v₃.
  `[HasCountableProducts C]` is exactly the stated product assumption.
- `H : Aᵒᵖ ⥤ B ⥤ C`, `[H.Additive]`, and
  `[∀ M : Aᵒᵖ, (H.obj M).Additive]` state separate additivity. The fixed target
  `I : CochainComplex B ℤ` is arbitrary.
- `U(V)` is precisely upstream `bifunctorHomObj H V I`. Its degree-n product
  is indexed by `HomComplex.Triplet n`, i.e. triples (p,q,p+n=q), canonically
  the integer-indexed product in the node. `bifunctorHomObj_d_π` gives exactly
  the node's signed differential. No second Hom construction is defined.
- `U(g)` is upstream `bifunctorHomMapLeft (H := H) (Y := I) g`, whose projection
  formula is componentwise precomposition. `f : K ⟶ L` is arbitrary.
- `E` is actual `mappingCone f`; `mappingCone.inr f` is i : L → E and
  `(mappingCone.inl f).v (p+1) p ...` is the K^(p+1) summand inclusion.
  Mathlib's cone orders K[1] before L. Its `d_fst_v` and `d_snd_v` give
  (-d_K k, f k + d_L l), exactly the node's (d_L l + f k, -d_K k)
  after ordering the summands as in the node.
- The existential family θ ranges over every K,L,f and takes values in
  `bifunctorHomObj H (mappingCone f) I ≅
  (mappingCone (bifunctorHomMapLeft ... f))⟦(-1 : ℤ)⟧`.
  This is the requested chain isomorphism, retaining the stronger explicit
  chain-level conclusion needed by the consumer; it is not merely cohomology
  isomorphisms or an assertion about unrelated representatives.
- `bifunctorHomConeY ... n` targets U(K)^(n-1), using shifted cone `snd`;
  `bifunctorHomConeX ... n` targets U(L)^n, using shifted cone `fst`.
  Thus the coordinate order (y,x) is exactly Y^(n-1) ⊕ X^n.
- The first conjunction states y_(p+1) = (-1)^p a_p, equivalent to
  y_j = (-1)^(j-1) a_(j-1); restriction to the K summand is rendered by
  `H.map (...inl...).op`. The second states that x_p is restriction to L,
  rendered by `H.map (...inr...).op`. All are morphism equalities after
  product projections, with arbitrary integers n,p,q and p+n=q.
- The third conjunction states a_p = (-1)^p y_(p+1) for θ.inv, and the fourth
  retains x for θ.inv. No element notation or concrete-category hypothesis
  is used. Arbitrary test morphisms can be precomposed with these equalities.
- The fifth states that the degree-n component of U(i) is θ.hom followed
  by the x projection, for every n.
- The sixth states that d followed by the y projection of θ is
  -d_Y y - t x. A canonical `XIsoOfEq` identifies (n+1)-1 with n;
  its equality proof only transports integer indices.
- The seventh states that d followed by the x projection of θ is d_X x.
  The fact that θ itself is an isomorphism of complexes ensures the
  transported differential is the actual shifted cone differential.
- The final conjunction quantifies over arbitrary u:K→K', v:L→L' with
  `comm : f ≫ v = u ≫ f'`. It uses the actual `mappingCone.map` on the source,
  and the actual shifted cone map induced by U(v),U(u) on the target.
  Its equation runs from U(Cone f') to Cone(U(f))[-1], so the direction is
  contravariant. The proof argument to that cone map is derived by the
  existing `bifunctorHomMapLeft_comp` and `comm`, with no extra assumption.
- There is no boundedness, exactness of products, quasi-isomorphism,
  K-injectivity, or chosen-derived-category hypothesis. A derived-category
  module is imported for the recorded dependency's cone/shift conventions;
  the conclusion remains explicitly the node's chain-level comparison.

Dependency declarations used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (full class and derived binary
  biproduct instance read). This is a Mathlib leaf and requires no new record.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, with `DerivedCategory` and
  `HasDerivedCategory` read. This item uses its complex/cone/shift portion,
  supplied by `CochainComplex.mappingCone`, `mappingCone.inr`, `inl`, `fst`,
  `snd`, `map` and `shiftFunctorObjXIso` from its public Mathlib imports.
- Existing signed Hom API:
  `WeilConjectures.Algebra.Homology.BifunctorHomComplex`, declarations
  `bifunctorHomObj`, `bifunctorHomπ`, `bifunctorHomMapLeft`,
  `bifunctorHomObj_d_π`, `bifunctorHomMapLeft_f_π`,
  `bifunctorHomMapLeft_comp`. They already supply the notions the node defines
  inline, so no missing notion or helper theorem needs a new DAG node.

Edge cases checked on the formulas: f=0 gives the direct split differential;
K=0 retains only x, L=0 retains only the reindexed signed y coordinate;
negative p are covered by `Int.negOnePow`, and adjacent indices have opposite
signs; characteristic two makes the minus signs coincide without invalidating
any equality; n=0 has y in degree -1. All complexes are unbounded. Products
are indexed by integers, never assumed exact. Naturality was checked with
identity squares, and its general direction and order of U(u),U(v) were checked
against the typed domain and codomain.

Searches actually run via msearch.py for Q01 and this item:

- LeanFinder: “Contravariant signed product bifunctor Hom complex of a mapping
  cone is isomorphic to shifted mapping cone of precomposition”. Eight hits,
  including `mappingCone.mapHomologicalComplexIso` and its degree components,
  plus `mappingCone.shiftIso`. These are covariant termwise functors and
  shifting an existing cone, not this signed contravariant product Hom.
- Loogle: `"bifunctorHom", "mappingCone"`. Zero hits.
- LeanSearch: “Signed contravariant Hom product complex mapping cone shifted
  cone natural isomorphism”. Eight hits on `mappingCone.map_δ`, `shiftIso`,
  the termwise cone comparison and homology shift comparisons; no match.
- Mathlib grep service, `Algebra/Homology`:
  `bifunctorHom.*[Cc]one|[Cc]one.*bifunctorHom|mappingCone.*Hom`.
  Hits concern ordinary cones and covariant termwise functors; no exact match.
- Local rg of Mathlib homology, project WeilConjectures and Sheaf for
  `bifunctorHom.*[Cc]one|[Cc]one.*bifunctorHom`, plus signed-cone keywords:
  no existing comparison; the consumer's docstring refers to this unstated node.
  `HomComplexMappingCone.lean` is a different, covariant sheaf-Hom comparison.
  Searching the upstream declaration index and both source trees for the three
  proposed declaration names found none. Searching WeilConjectures for the
  item id found none. The exact signed Hom definition and maps were found and
  reused, rather than duplicated.

Validation: scompile.py compiled both the sandbox module and its library module
with no errors or warnings. The first compiler pass found that an unqualified
`shiftFunctor` in the naturality equation resolved to `CochainComplex.shiftFunctor`;
qualifying `CategoryTheory.shiftFunctor` fixed it. All declarations explicitly
bind universes and variables with autoImplicit disabled. No diagnostic commands,
local notation, local instances, private definitions, or theorem proofs beyond
`sorry` remain. The prescribed deliver2.py dry run and delivery follow this report.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
