## Worker report

Item: `lem-pur-good-truncation-exact-normalization`, stage 2, Q09.
Module: `Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization`.
The ten declarations jointly render the node. The node is unchanged except for `lean`.
There are no new nodes, dependency repairs, statement corrections, or disputed statements.
Every theorem has a `sorry` proof; the two definitions have real data.

### Hypotheses and clauses

1. Abelian categories C, D (and E when composing functors) are the section binders
   `{C : Type u₁} [Category.{v₁} C] [Abelian C]`, and likewise for D and E.
   Their three object universes, hom universes, and derived hom universes are separately
   named. `[HasDerivedCategory.{w₁} C]` and its analogues implement the chosen ordinary
   localizations; no equality between category or localization universes is assumed.
2. The ordinary derived category, localization, and cohomology are `DerivedCategory C`,
   `DerivedCategory.Q`, and `DerivedCategory.homologyFunctor C n`. The single embedding
   is `DerivedCategory.singleFunctor C 0`. Good truncation and its inclusion are the
   recorded truncation dependency's `A.truncLE 0` and `A.ιTruncLE 0`.
3. Membership in Z_C is written inline, without a second definition:
   `∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K)`.
   All morphisms `a : K ⟶ L` are allowed; hence the naturality assertion is on the
   full subcategory, without a requirement that a be represented by a chain map.
4. `goodTruncationProjection` is the actual map p_A. It uses
   `HomologicalComplex.mkHomToSingle` on
   `(A.truncLEXIsoCycles 0).hom ≫ A.homologyπ 0`.
   The first factor identifies the truncation's zero term with ker(d⁰); the second
   is its cycles-mod-boundaries quotient. The single-map constructor gives this map
   in degree zero through the canonical single-term identification and zero in every
   other degree. `goodTruncationProjection_condition` is exactly its chain equation:
   the incoming differential followed by that quotient is zero. It is valid for every
   complex and is the named proof needed by the definition, never an embedded sorry.
5. `existsUnique_goodTruncationNormalization` says there is a unique isomorphism
   `e : K ≅ (singleFunctor C 0).obj ((homologyFunctor C 0).obj K)` whose H⁰ map,
   followed by `singleFunctorCompHomologyFunctorIso`, is the identity.
   `goodTruncationNormalization` selects this unique object with `Classical.choose`.
   This is choice from a uniqueness theorem that determines the isomorphism, not
   arbitrary choice from a mere existence claim. Its source is the specified roof;
   the roof theorem below verifies exactly that source normalization.
6. `goodTruncationNormalization_roof` quantifies over EVERY complex A and EVERY
   representative isomorphism `r : Q.obj A ≅ K`. Its first two conjuncts are
   `QuasiIso (A.ιTruncLE 0)` and `QuasiIso (goodTruncationProjection A)`.
   Its third conjunct states
   `Q(c_A) ≫ r.hom ≫ ε_K.hom = Q(p_A) ≫ S(H⁰(QA) ≅ H⁰(A))⁻¹ ≫ S(H⁰(r))`,
   with the additional canonical `singleFunctorIsoCompQ` identifying Q(single) with S.
   This is the displayed roof formula multiplied by Q(c_A); the first conjunct
   makes Q(c_A) invertible. Thus it is equivalent to the node's inverse formula,
   and does not introduce any noncanonical inverse. Taking r to be the identity
   gives the stated ε_QA formula. Quantification over r proves independence from
   the representative and from its identifying isomorphism.
7. `goodTruncationNormalization_naturality_hom` has three conjuncts. The first is
   `a ≫ ε_L.hom = ε_K.hom ≫ S.map (H⁰.map a)` (diagrammatic composition reverses
   the written order of the source's circle notation). The second is
   `Function.Bijective (fun f : K ⟶ L ↦ (homologyFunctor C 0).map f)`.
   The third quantifies over every b and states
   `S.map b = ε_K.inv ≫ a ≫ ε_L.hom ↔ b = H⁰.map a`.
   This specifies both existence and uniqueness of the b in the node, as well as
   identifying it with H⁰(a). Iso components already supply inverse maps and their
   inverse laws, so the natural family is a natural isomorphism.
8. Exact F is `(F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
   [PreservesFiniteColimits F]`. Its D(F) is the recorded
   `F.mapDerivedCategory`. The comparison χ is the existing
   `F.mapDerivedCategoryHomologyFunctorIso 0`, whose definition descends the
   preserved-homology comparison from complexes. The comparison σ is the recorded
   `F.mapDerivedCategorySingleFunctor 0`. These are fixed constructions, never
   arbitrary comparison maps supplied as hypotheses.
9. `goodTruncationNormalization_exact_concentrated` says Z_C is sent into Z_D,
   in every degree n unequal to zero. Its proof term is used only as the membership
   proof in the subsequent normalization; it does not choose any categorical data.
10. The first conjunct of `goodTruncationNormalization_exact` is the node's formula
    `ε_D(F)K = D(F)(ε_K) ≫ σ_F,H⁰K ≫ S_D(χ_F,K)`.
    The second is its χ naturality equation
    `χ_F,K ≫ H⁰(D(F)a) = F(H⁰(a)) ≫ χ_F,L`.
    The K and L concentration assumptions are exactly membership in the stated
    full subcategory; no boundedness, injectives, faithfulness, or nonzero-object
    assumption is introduced.
11. `goodTruncationNormalization_identity` states that χ for the identity, followed
    by H⁰ of the canonical derived identity comparison, is the identity, and that
    σ for the identity is that same canonical comparison on a single object.
    Thus both are identities after the specified canonical identifications.
12. `goodTruncationNormalization_composition` has the two composition clauses.
    Its χ equation is
    `χ_(F⋙G),K ≫ H⁰(comp_F,G,K) = G(χ_F,K) ≫ χ_G,D(F)K`.
    Its σ equation is
    `comp_F,G,S(B) ≫ D(G)(σ_F,B) ≫ σ_G,FB = σ_(F⋙G),B`.
    Here `Functor.mapDerivedCategoryCompIso F G` is the canonical termwise
    derived-composition comparison, normalized by its existing `_fac` theorem.
    Substitution of these two equations into the exact normalization theorem gives
    its composite form for ε. Identity coherence for ε likewise follows from that
    theorem and the identity comparison equations. No comparison is left unspecified.
13. The zero-category clause is retained: nothing assumes a nonzero object or
    nontrivial Hom set, and all degrees and all objects are quantified. In the zero
    category the quotient map, ε, χ and σ are the unique maps, and the Hom bijection
    is between singleton sets. This is Step 8 of the source proof, also documented
    in the theorem docstrings.

### Dependency declarations and imports

- `def-sp-abelian`: `CategoryTheory.Abelian` from
  `Mathlib.CategoryTheory.Abelian.Basic` (imported transitively). Its class signature
  and documentation were read; it supplies the preadditive, kernel and cokernel
  structures used by the genuine complexes and quotient maps.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, from `Mathlib.Algebra.Homology.DerivedCategory.Basic`, and
  `homologyFunctor`, `homologyFunctorFactors` from its `HomologySequence` module.
  The latter is the canonical H⁰(QA) ≅ H⁰(A) used in the roof.
- `def-kun-truncations`: the recorded
  `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` is publicly imported.
  Its module documentation explicitly maps good truncations to Mathlib's
  `CochainComplex.truncLE`, `ιTruncLE`, and `truncLEXIsoCycles`; those exact
  constructions are used. Its unrelated homotopy-colimit predicate is not copied.
- `lem-sf-exact-functor-derived-triangulated`: the recorded Mathlib
  `CategoryTheory.Functor.mapDerivedCategory` and
  `mapDerivedCategorySingleFunctor`, from
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, are reused.
- The public upstream module
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` supplies
  `mapDerivedCategoryHomologyFunctorIso`, `mapDerivedCategoryIdIso`, and
  `mapDerivedCategoryCompIso`. Their definitions and docstrings were read:
  the first is localization of the kernels/quotients comparison, and the latter
  two are precisely the termwise identity/composition localization comparisons.
  `_hom_app_Q`, `_fac`, and `_factorsh` document their normalization.
- `lem-weil-pbc-derived-single-fully-faithful`: the recorded full/faithful instances
  and `singleFunctorCompHomologyFunctorIso` from
  `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`, publicly imported
  because the single/H⁰ comparison occurs in signatures.
- `lem-weil-pbc-exact-functor-complex-cohomology` and
  `lem-sp-exact-functor-preserves-homology`: recorded
  `Functor.homologyFunctorIso`, `Functor.preservesHomologyOfExact`,
  `ShortComplex.mapHomologyIso`, from
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`, proof import.
- `lem-weil-pbc-exact-functor-derived-factorization`: recorded
  `Functor.mapDerivedCategoryFactors`, included by the exact-functor public import.
- `lem-weil-pbc-localization-universal-property`: recorded
  `Localization.lift`, `liftNatIso`, and natural-transformation uniqueness from
  `Mathlib.CategoryTheory.Localization.Predicate`, proof import.

No recorded dependency interface is unusable. In particular, the truncation node's
primary declaration concerns homotopy colimits, but its public imports and explicit
component mapping already supply the exact truncation notions required here.

### Sources, searches, and edge cases

Read the actual local Stacks sources: `homology.tex`, section-truncations, especially
its cochain τ≤ definition and cohomology; lemma-exact-functor (010N); `derived.tex`,
lemma-negative-exts (06XS)(2), and lemma-right-derived-exact-functor (015F).
The node's eight proof steps are distributed among the theorem docstrings with their
proof dependencies. The stronger normalization/coherence assertions are the node's
explicit agent-formulated assertions, not attributed verbatim to Stacks.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: “Good truncation gives canonical natural isomorphism between derived
  objects concentrated in degree zero and their single cohomology complex compatible
  with exact functors”. Eight hits, including `singleFunctorIsoCompQ`,
  `singleFunctorCompHomologyFunctorIso`, and truncation quasi-isomorphism instances.
  These provide ingredients, not the combined specified roof/coherence statement.
- Loogle: `DerivedCategory.singleFunctorCompHomologyFunctorIso,
  CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. Zero hits for this
  combined query; both known declarations were then read directly in their modules.
- Mathlib grep: `truncLE.*[Hh]omology|[Hh]omology.*truncLE|mapDerivedCategorySingleFunctor`
  in `Algebra/Homology`. Sixteen hits, including `TruncLEHomology` and the exact
  single-functor comparison. Reused these constructions.
- LeanSearch: “A derived object with cohomology concentrated in degree zero is
  canonically isomorphic to the single complex of its zeroth cohomology naturally
  and compatibly with exact functors”. Eight hits concerning right/left derived
  degree-zero functors, single-complex maps, and the derived zero object. No exact match.
- Direct rg searches in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `goodTruncationNormalization` and
  `goodTruncationProjection` found no existing declarations. The required blueprint-id
  search in `lean/WeilConjectures` also found none.
- Concept/API searches found the upstream exact-functor homology, identity and
  composition isomorphisms, and the existing bare Hom-bijection theorem
  `homologyFunctor_map_bijective_of_isGE_of_isLE`. These were inspected. The latter
  does not state the roof normalization, its unique-b description with that ε, or
  compatibility/coherence, so it is not an existing match for this node.

Checked: zero complex and zero abelian category; arbitrary acyclic representatives of
zero; single objects in degree zero; unbounded complexes acyclic outside zero;
negative and positive degrees, including the incoming degree −1 chain equation;
identity functor; zero exact functor; composites of exact functors; arbitrary derived
morphisms and arbitrary representative isomorphisms. None is excluded. No universe
identification is imposed, and the server compiler accepts all nine universe parameters.

Validation: scompile.py compiled this file both as sandbox and as the final module
against the live published build: clean, no warnings or errors, 9.2 s and 4.9 s.

## Second reading by Q09

This is the worker's separate second pass with the node and completed file open;
the maintainer supplies the independent review requested in the dispatch brief.
No other agent was started.

The map p has the required quotient component and actual chain-map data; c is the
recorded truncation inclusion. The roof theorem includes both quasi-isomorphisms
and quantifies over every representative r, rather than only some chosen model.
Its comparison directions were checked: the inverse of H⁰(QA) ≅ H⁰(A) carries
H⁰(A) back to H⁰(QA), after which H⁰(r) reaches H⁰(K). The single comparison first
carries Q(single H⁰(A)) to S(H⁰(A)). Multiplication by the invertible Q(c) recovers
the source's exact roof formula.

The H⁰ normalization uniqueness theorem fixes ε completely; no unknown data is
chosen. Naturality uses all derived maps in the full subcategory. The Hom bijection
and iff for b retain both surjectivity and uniqueness. Exactness binders include
additivity and preservation of both finite limits and finite colimits. χ and σ are
existing canonical maps, with the same orientation as the node. Identity and
composition statements include the canonical derived identity/composition maps,
so there is no silent strictification. The third category is only the codomain of
the composable second exact functor; its universes are independent as well.
The zero-category case is covered by the unrestricted binders.

No mismatch requiring a node correction was found. The alternate multiplied roof
formula and the family-of-isomorphisms presentation of a natural isomorphism are
mathematically equivalent presentations of the exact clauses, as detailed above.
