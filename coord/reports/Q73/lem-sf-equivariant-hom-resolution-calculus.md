## Worker report

The module `Sheaf.Algebra.Homology.EquivariantHomResolutionCalculus` states
`CochainComplex.exists_equivariantHomResolutionCalculus`, with one postponed proof.
`CochainComplex.productHomResolutionMap` is a real definition: it is exactly
`F.map (X := (op K, I)) (Y := (op K', I')) (t.op, v)`. This exposes the canonical
bifunctor action with explicit endpoints, avoiding elaboration ambiguity about
morphisms of product categories. It introduces no new mathematical notion.
No definitions choose data from the postponed theorem. The theorem existentially
constructs the bifunctor and its projections together with their entire calculus.
No new nodes, dependency repairs, or statement corrections are needed.

Hypotheses and clauses, in the order of the node:

1. Abelian categories A and B: independent `Type uA`, `Category.{vA}` and
   `Type uB`, `Category.{vB}`, with `[Abelian A] [Abelian B]`.
   Ordinary derived categories and their localizations: independently sized
   `[HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]`, `DerivedCategory.Q`.
2. Countable products in B: `[HasCountableProducts B]`. No exactness of products,
   arbitrary-small-product assumption, or boundedness assumption is introduced.
3. The separately additive bifunctor: `H : Aᵒᵖ ⥤ A ⥤ B`, `[H.Additive]`, and
   `[∀ X : Aᵒᵖ, (H.obj X).Additive]`. Curried additivity in the first variable
   says componentwise additivity, because addition of natural transformations
   is componentwise. Uncurrying yields precisely the node's product-category form.
4. Integer-indexed cochain complexes: every complex is `CochainComplex A ℤ`.
   The existential `F` is the uncurried bifunctor on these complexes.
   `π K I n p q hpq` is its projection to `H(K^p,I^q)` for `p+n=q`.
   The first conjunct, `Nonempty (IsLimit (Fan.mk ...))`, says that the degree-n
   object with these projections is the product over all integer source degrees.
5. The differential: the second conjunct identifies its component with
   `π ... ≫ (H.obj ...).map (I.d r q) - n.negOnePow •
   (π ... ≫ (H.map (K.d p s).op).app ...)`, for `m=n+1`, `r=p+n`,
   and `s+n=q=p+m`. Thus `s=p+1` and the sign is exactly the node's `(-1)^n`.
   Square-zero and the vanishing of non-successive differentials are built into
   the objects of `CochainComplex B ℤ` supplied by F.
6. Componentwise `H(t,v)` is `productHomResolutionMap F t v`. The third conjunct
   specifies its components using `(H.map (t.f p).op).app ...` followed by
   `(H.obj ...).map (v.f q)`. Identities and composition are the laws of F.
7. A homotopy uses Mathlib `Homotopy`, whose equation is
   `t.f i = dNext i h.hom + prevD i h.hom + t'.f i`.
   In a preadditive category this is exactly `t-t'=dh+hd`.
8. Source homotopies: the fourth conjunct supplies S and specifies every nonzero
   degree-minus-one component by `n.negOnePow • (π ... ≫ H(h.hom p r,-))`,
   with `r+1=p` and `m+1=n`. This is exactly `(-1)^n f^(p-1) h^p`.
   All other components vanish by the shape condition in `Homotopy`.
9. Target homotopies: the fifth conjunct supplies R with component
   `π ... ≫ (H.obj ...).map (h.hom r q)`, where `r=p+n` and `q=p+n-1`.
   This is the formula `h'f`, with no additional sign.
10. Descent to both homotopy categories: the sixth conjunct constructs G and a
    natural isomorphism `F ⋙ quotient B ≅ (quotient A).op.prod (quotient A) ⋙ G`.
    This states descent of the full bifunctor, including its morphisms.
11. Respect for the category structures and additional equivariance: every
    projection, differential, homotopy component and map is a morphism in B;
    H acts on actual morphisms in A. The formula is categorical, not an equation
    on hypothetical elements of B objects. For additional compatible equivariance,
    take A and B to be the corresponding categories with structure: the same
    formulas and product universal property produce morphisms preserving that
    structure. No unrelated functor is asserted to preserve products. This is
    precisely the interpretation in proof step 5 of the node. The mixed square
    is also explicitly included, for all maps t and v.
12. The degree-zero source: `HomologicalComplex.single A (.up ℤ) 0` and
    `(H.obj (op X)).mapHomologicalComplex (.up ℤ)` give X[0] and H_X(I).
    The seventh conjunct gives an actual chain isomorphism e, specifies its hom
    as π at source degree zero followed by the canonical single-term identification,
    and gives simultaneous naturality in `b : X' ⟶ X` and `v : I ⟶ I'`, in each
    degree. These component equations are exactly the chain-map naturality square.
13. Normalized changes of source resolutions: the eighth conjunct quantifies over
    K,L,J,J', `[J.IsKInjective] [J'.IsKInjective]`, α,β with `[QuasiIso α]`
    `[QuasiIso β]`, and a. It supplies u with
    `Q.map u = inv (Q.map α) ≫ Q.map a ≫ Q.map β`.
    Lean composes left to right, so this is precisely the node's displayed arrow.
    It also supplies `Nonempty (Homotopy (α ≫ u) (a ≫ β))` and uniqueness of u
    up to homotopy among all maps satisfying this normalization.
14. For every arbitrary complex I, the same conjunct gives a homotopy between
    `H(u,1) ≫ H(α,1)` and `H(β,1) ≫ H(a,1)`, then equality of the composites
    of their Q_B images. The specified source-homotopy clause supplies the induced
    signed homotopy for every witness of `α ≫ u ~ a ≫ β`.
15. Choice independence and arbitrary derived arrows: the ninth conjunct applies
    to every derived arrow q between K-injectives, supplies a representative u,
    and states that any other representative u' is homotopic and gives the same
    Q_B map for both precomposition and postcomposition, with any other complex K.
    There is no isomorphism assumption on q.
16. Changes of target representatives: the tenth conjunct takes any identification
    `e : Q.obj I ≅ Q.obj I'` and any representative v. It supplies an actual
    `HomotopyEquiv I I'` whose forward map equals v, and, for every source K,
    a `HomotopyEquiv` of Hom complexes whose forward map equals H(1,v).
17. Compatibility with source precomposition: the eleventh conjunct states the
    strict equality `H(t,1) ≫ H(1,v) = H(1,v) ≫ H(t,1)` with the appropriate
    endpoints, for arbitrary t and v. This applies to the resolution squares too.
18. Identity and composition after localization: the last two conjuncts cover,
    respectively, every representative of a derived identity and every w whose
    derived image is the composite of the images of u and v. They give the
    contravariant composition law for precomposition and the covariant law for
    postcomposition. All the complexes serving as these representatives are
    K-injective. This includes normalized changes after cancellation of Qβ.
19. The final negative scope statement is respected: no conclusion asserts
    quasi-isomorphism invariance for arbitrary sources or a derived-functor
    comparison. Homotopy equivalences and actual derived arrows between
    K-injectives are the comparisons covered.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: recorded module
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, declarations `DerivedCategory`
  and `HasDerivedCategory`; also `DerivedCategory.Q`, its localization instance,
  and `DerivedCategory.quotientCompQhIso`. This module is publicly imported.
- Proof dependency `lem-weil-pbc-kinjective-hom-derived`: Mathlib match
  `CochainComplex.IsKInjective.Qh_map_bijective`, module
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`, imported as a proof import.
  Its full signature and `IsKInjective.quasiIso_iff` were read; the node's
  bounded-below supplement `DerivedCategory.Plus.Qh_map_bijective_of_isKInjective`
  is not required by this item. `CochainComplex.IsKInjective` itself is publicly
  imported from `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` and has
  exactly the acyclic-source null-homotopy meaning used here.
- Mathlib `Homotopy`, `HomotopyEquiv`, `HomologicalComplex.single`,
  `HomologicalComplex.singleObjXSelf`, `Functor.mapHomologicalComplex`,
  `HomotopyCategory.quotient`, `HasCountableProducts`, and `Int.negOnePow`.

Sources read: sites-cohomology.tex, section-hom-complexes (0A8X), its product
formula, signed differential and equation-cohomology-hom-complex; derived.tex,
definition-K-injective and lemma-K-injective (070I). The current blueprint anchor
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-i-dl-a1-local/
lem-a1-local-boundary-duality.proof.md` was read, including its opening lisse
identity. The item remains the agent-formulated abstract calculus recorded in its
source; it is not the statement of that blueprint unit.

Edge cases checked by direct mathematical reading: zero categories and zero
complexes; H zero; X=0 or I=0 in the projection; arbitrary negative degrees
(the sign uses integer `negOnePow`); zero homotopies; identity and composite
resolution changes; unbounded complexes; arbitrary non-invertible derived arrows
between K-injectives; independent object, morphism, and localization universes.
The index is ℤ throughout and the product only needs countable products.
The inverse to Qα exists from `[QuasiIso α]`; no extra invertibility assumption
has been added. The source-resolution comparison does assume both J and J' are
K-injective as the node does, even though only J' is needed for that subclause.
No statement dispute or node fault was found.

Searches for an existing complete statement:

- `msearch.py ... leanfinder`: “Product total Hom of an additive bifunctor takes
  chain homotopies in either variable to chain homotopies with signed
  precomposition”. Eight hits include `mapBifunctorMapHomotopy₁/₂` and component
  lemmas. They concern coproduct totalization, not this product Hom convention.
- `msearch.py ... loogle '"bifunctorHom"'`: twelve hits, all for
  `Functor.mapBifunctorHomologicalComplex` and related bicomplex formulas.
- `msearch.py ... leansearch`: “Product Hom complexes preserve source and target
  homotopies and normalized changes of K injective resolutions”. Eight hits
  include ordinary injective resolutions, preservation of K-injectivity under
  homotopy equivalence, and `Functor.mapHomotopyEquiv`; no complete match.
- `msearch.py ... grep 'bifunctorHom.*[Hh]omotop|[Hh]omotop.*bifunctorHom'
  Algebra/Homology`: zero Mathlib hits.
- `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, the declaration index,
  and the item-id search upstream: no existing declaration of this theorem.
  Read `WeilConjectures.Algebra.Homology.BifunctorHomComplex`, including its
  object, differential projection, maps and source homotopy. Its differential
  is `(-1)^p (d_I f - f d_K)`, a different convention from the node's.
  Read `Sheaf.Algebra.Homology.BilinearHomComplex` and its DAG node in full.
  `ProductHomComplexSpecification` uses the right sign, but its API requires
  all small products (`HasProducts.{0}`) and common input/output universes.
  This delivery does not duplicate that definition: the product equations are
  written directly in the full theorem, with only the countable products and
  independent universes the item allows. The existing construction can help
  its eventual proof after a suitable interface generalization.

Validation: `scompile.py Q73 lem-sf-equivariant-hom-resolution-calculus <module>`
compiled both sandbox and actual module names cleanly (2.1 and 2.0 seconds).
The only postponed proof is the named main theorem, with its full ten-step
natural-language proof in the docstring. Every variable and universe is explicit.

## Second reading by Q73

This is the dispatcher's single worker; no second agent was started. I made a
separate clause-by-clause rereading of the node against the final file, recorded
above. The maintainer's independent review remains the independent second reader.
The rereading checked both differential signs, the direction of the source
homotopy, the source degree-zero canonical identification, and the two orders
of composition. The normalized derived arrow must be `inv (Qα) ≫ Qa ≫ Qβ`
in Lean notation, and the contravariant square consequently starts with H(u,1)
and then H(α,1); these agree with the final file. It also checked that q in the
arbitrary-arrow clause has no invertibility hypothesis, and that the target
identification uses the given e rather than an unspecified equivalence.
The only implementation repair was adding `productHomResolutionMap` with
explicit product endpoints after Lean rejected inference of the final composition
maps. This is the literal functor action, with no added premise or conclusion.
No mathematical mismatch or statement change was found.
