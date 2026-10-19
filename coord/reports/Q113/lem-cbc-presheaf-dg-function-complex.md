## Worker report

The delivery states `CategoryTheory.PresheafDGFunctionComplex.comparison_exists` in
`Sheaf.Paper.PresheafDGFunctionComplex`. Its proof is the sole `sorry`. The conclusion
is `Nonempty (Comparison C Λ)`: a model together with all the comparisons in the node.
The supporting definitions are explicit constructions or constrained data interfaces;
none chooses an object from this existence theorem. All helper declarations belong to
this node and are listed in `lean.declarations`.

Hypotheses and clauses, in the order of the informal statement:

1. An arbitrary small ordinary category is `(C : Type u) [Category.{v} C]`.
   The coefficient ring is `(Λ : Type w) [CommRing Λ]`. Write `s = max u v w t`
   in this report only. Presheaves are exactly `Cᵒᵖ ⥤ ModuleCat.{s} Λ` and complexes
   are Mathlib `CochainComplex ... ℤ`. No topology, finite limits on C, boundedness
   of the target, nonzero-ring hypothesis, or nonempty-category hypothesis occurs.
   The extra universe `t` allows enlargement. The chosen ordinary category of
   coefficient complexes is `[HasDerivedCategory.{s+1} AddCommGrpCat.{s}]`, the
   standard chosen-localization convention; `HasDerivedCategory.standard` supplies
   this size. It imposes no additional mathematical hypothesis on C or Λ.
2. Kernels and cokernels use the existing abelian functor-category instances.
   Cochains, shifts, cohomology and quasi-isomorphisms are the recorded Mathlib
   definitions. Enhanced localization is `Comparison.localizationMap` with the
   existing full coherent universal property `Comparison.isLocalization`.
   `enhanced` is a simplicial category, `locallyKan` imposes Kan mapping sets,
   and its actual coherent nerve is the target of the localization. The equations
   `localization_vertices` and `localization_mapping` identify the exact localization
   vertices and mapping simplices in every dimension. Each subset-poset simplex is
   sent to the degenerate simplex of the specified composite under `localize`; thus
   the entire localization nerve, including its higher coherences, is fixed. The
   recorded coherent-nerve comparison supplies its right-pinched mapping spaces. No arbitrary
   quasicategory or arbitrary equivalence predicate is substituted.
3. `freeRepresentable C Λ T` specializes Mathlib `Presheaf.freeYoneda T` to the
   rank-one module `ModuleCat.of Λ (ULift Λ)`. This is the existing coproduct
   construction, with one copy of Λ for every arrow V → T; the ULift only places
   that rank-one module in the coefficient-module universe. Its restriction maps
   are the coproduct maps induced by precomposition. This is not a second free
   module or representable definition.
4. `IsFreeBoundedAbove A` says `(∃ n : ℤ, CochainComplex.IsStrictlyLE A n)` and,
   for each integer p, there are a small type I and T : I → C with
   `Nonempty (A.X p ≅ ∐ fun i ↦ freeRepresentable C Λ (T i))`. Empty sums are allowed.
   `Comparison.free_comparison` asserts that the actual component of the natural
   transformation `comparison : ordinary ⟶ rhom` is a quasi-isomorphism for every
   such source and every complex G, including unbounded G.
5. `ordinary_obj` identifies each ordinary complex exactly with Mathlib
   `X.HomComplex G`. Its degree-r cochains are families of presheaf morphisms
   `X.X p ⟶ G.X (p+r)` (`HomComplex.Cochain` uses equality-indexed triplets).
   Mathlib's differential is `d_G h - (-1)^r h d_X`. `homMap f g` is the actual
   map h ↦ g h f, constructed from `Cochain.ofHom` and `Cochain.comp`.
   `ordinary_map` normalizes every bifunctor map to this map. Thus an unconstrained
   functor cannot replace the ordinary complex. Naturality in all source and target
   maps is the natural-transformation type of `comparison`.
6. The resolution characterization makes `rhom` genuine derived Hom:
   `replacements` supplies K-projective quasi-isomorphic sources;
   `rhom_inverts` inverts quasi-isomorphisms in both variables; and
   `projective_comparison` identifies ordinary Hom with this model on K-projective
   sources. For q : P → X, these fields give the natural zigzag
   Hom(P,G) → rhom(P,G) ← rhom(X,G), with both arrows quasi-isomorphisms.
   They specify the meaning of the derived-Hom model, rather than adding a
   replacement hypothesis to the node. No replacement is chosen by a definition.
7. `simplicialGroups` is literally the composite of Mathlib's
   `embeddingDownNat.truncLE'Functor` and `Abelian.DoldKan.Γ`. The former has
   degree m > 0 equal to E^(-m), degree zero `E.cycles 0`, and the induced
   differential, by the definitions of `truncLE'` and the boundary of this embedding.
   The latter is the inverse of `Abelian.DoldKan.N`, definitionally the normalized
   Moore complex. `realization` forgets these simplicial abelian groups to sets
   and lifts their universe to s+1. It is not the brutal truncation.
8. `realizationKan` supplies the Kan condition. `enrichedMaps enhanced localize`
   is the pullback of Mathlib's `eHomFunctor`; therefore its precomposition maps
   are the actual enriched composition maps. `mapping_bridge`, `mapping_left`,
   `mapping_right`, and their objectwise weak-equivalence assertions give a
   natural zigzag of actual simplicial maps between these mapping sets and
   `realization(rhom(X,G))`. This records a coherent natural comparison before
   passage to homotopy categories. The coherent nerve comparison identifies the
   enriched mapping sets with the dependency's right-pinched mapping spaces.
9. Arbitrary cochain models are retained by `derivedRealization` together with
   `realization_factors : Q ⋙ derivedRealization ≅ S ⋙ Q_spaces`. An isomorphism
   Q(E) ≅ Q(rhom(X,G)) therefore induces the specified representation in spaces
   for that model E, not only for the chosen `rhom` complex. The space category
   is exactly `SSet.Enhanced.spaceWeakEquivalences.Localization`, the body of the
   dependency's `spaceHomotopyCategory` definition, written unfolded so its
   existing localization category instance is available.
10. `components E` identifies π₀ of the geometric realization with E.homology 0;
    `components_natural` gives its naturality on the specified maps. `homotopy E m z`
    is a group isomorphism from π_(m+1) at the geometric point of vertex z to
    `Multiplicative (E.homology (-(m+1)))`. Thus every positive degree is covered.
    `homotopy_natural` is the naturality square for the actual realized map.
    Its HEq records the canonical equality between the image of a realized vertex
    and the realization of the image vertex, without choosing a basepoint path.
11. `translation_formula` fixes every simplex of `translation E z` to subtraction
    of the constant simplex at z. `translation_homotopy` says that its induced
    map is exactly the transport between `homotopy E m z` and `homotopy E m 0`.
    In particular the identifications at nonzero vertices are the translations
    of the zero-map identifications, not unrelated abstract group isomorphisms.
12. `precomposition_iff` tests the actual enriched precomposition by f against
    `IsIso (homologyMap (rhom.map (f.op, 𝟙 G)) r)` for every integer r ≤ 0.
    The map, the direction, and the degree-zero test are all explicit.
13. `shift k` is a natural isomorphism after the actual coefficient-complex
    localization, from the source-shifted rhom functor to rhom followed by shift
    -k. Its natural-isomorphism type includes compatibility with precomposition
    and with target maps for every integer k. The proof docstring gives the
    ordinary Hom formula with sign (-1)^(k*r) and checks both differential terms.

Dependencies read and reused:

- `def-weil-size-convention`: the recorded metatheoretic convention, no declaration.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, and
  `DerivedCategory.Q`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the full
  signatures and source documentation were read.
- `def-cbc-enhanced-diagrams-cones`: the source
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` was read, including
  `mappingSpace`, `mappingSpaceMap`, `IsWeakHomotopyEquivalence`, `componentsMap`,
  `homotopyGroupMap`, `spaceWeakEquivalences`, and `spaceHomotopyCategory`.
- Added already-landed dependency `def-coef-coherent-localization-interface`:
  `HomotopicalAlgebra.FiniteReedy.largeNerve`, `IsLocalization`, and `object` from
  `Sheaf.CategoryTheory.FiniteReedyLocalization`. Their full coherent functor-category
  signatures were read and used; their definitions are not copied.
- Added already-landed dependency `def-coef-coherent-nerve-infrastructure`:
  `CategoryTheory.CoherentNerve.SCat`, `hom`, `underlying`, `IsLocallyKan`, and
  `nerveFunctor`, `Sheaf.CategoryTheory.CoherentNerveInfrastructure`.
- Added already-landed dependency `lem-coef-coherent-nerve-comparison`:
  `CategoryTheory.CoherentNerveComparisonStatement` and its actual mapping-space
  comparison fields, `Sheaf.CategoryTheory.CoherentNerveComparison`. The source
  and its object, arrow, composition, and naturality conditions were read.
- `lem-sc-bounded-above-projective-kprojective` uses the existing
  `CochainComplex.isKProjective_of_projective`; its source signature was read.
  Its module is imported. The other proof-only nodes
  `lem-coef-dg-module-projective-resolution` and `lem-cbc-dold-kan-homology`
  currently have no Lean record in the shared DAG, so no nonexistent module is
  imported. They remain proof dependencies and are named, step by step, in the
  theorem's natural-language proof. The present statement needs none of their
  unstated interfaces: its constructions use the existing cochain, Dold--Kan,
  enriched-category, and coherent-localization definitions directly.

Edge cases checked by reading the constructions and formulas: C empty (the presheaf
category is still allowed); terminal C (ordinary module complexes); Λ the zero ring;
empty I and zero A; A a free representable in degree zero; arbitrarily unbounded G;
E with nonzero terms in positive degrees (good truncation uses Z⁰, not E⁰);
E concentrated in degree -m; an acyclic two-term E; m=0 in `homotopy` (π₁); π₀;
k=0, k=1, k=-1. Every degree and zero object is included. Source object, source
morphism, coefficient, and enlargement universes remain independent.

Searches made (UTC 2026-10-16):

- `msearch.py ... leanfinder "derived Hom complexes of module presheaves and Dold Kan
  derived mapping spaces"`: eight hits, mainly Dold--Kan functor maps and normalized
  Moore complex maps. No presheaf enhanced function-complex comparison.
- `msearch.py ... loogle "CochainComplex.HomComplex, DoldKan.equivalence"`: zero hits;
  the unqualified identifier DoldKan.equivalence was unknown. Direct source inspection
  located `CategoryTheory.Abelian.DoldKan.equivalence`, N, and Γ and reused them.
- `msearch.py ... grep "derivedHom|DoldKan|IsKProjective" Algebra/Homology`: ten hits
  on the existing K-projective interface and the ordinary derived-category comparison;
  none supplies this node's coherent mapping-space statement.
- `msearch.py ... leansearch "The hom complex of cochain complexes is a functor
  contravariant in the first argument and covariant in the second"`: eight hits,
  including `CochainComplex.HomComplex`, `Cochain`, `Cochain.mk`, `Cochain.v`, and
  `HomologicalComplex.asFunctor`. Reused HomComplex and its graded composition.
- Direct `rg` over the pinned Mathlib HomComplex, DerivedCategory, KProjective,
  enriched-category, Dold--Kan and generator modules located all the primitives above.
  `Presheaf.freeYoneda` was found in `Mathlib.CategoryTheory.Generator.Presheaf`
  and replaces an initially considered inline free-module construction.
- Direct `rg` over `WeilConjectures` for dgCategory, DoldKan, mappingSpace, derivedHom
  and the node id found no exact statement. Direct `rg` over `lean/Sheaf` found
  the existing hyperdescent consumer, coherent-nerve framework, and dg semi-free
  modules, but no existing declaration for this item. `rg` for the proposed names
  over Mathlib, upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no
  declaration-name collision (only differently named free-representable sheaf helpers).

The online source https://arxiv.org/pdf/1511.02828 was opened and Facts 3.10, 3.14
and Lemma 3.16 were checked. WANTED: archive that PDF and the Higher Algebra source
already named in the node's proof; this worker has no authorization to write the
shared literature directory. No statement correction or statement dispute was needed.
No new independent definition node or dependency repair module was needed. The three
added statement dependencies already have landed Lean records and are unchanged.

Validation: the prescribed `scompile.py` checks the sandbox and library module under
its unchanged 60-second per-file limit. The required final command is
`python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q113
lem-cbc-presheaf-dg-function-complex --no-push`; only the second reader delivers.

## Second reading by Q113

I independently read the current DAG node, the sandbox module, the worker report,
all six statement-dependency records, and their recorded source interfaces. There
is no repair note for this item. The node has no `statement_change`; comparison
with the current shared node confirms that its mathematical statement, source,
proof and proof dependencies have not changed. Its added statement dependencies
are the three already-landed coherent-localization and coherent-nerve interfaces.
There are no new definition nodes or dependency repair modules to audit.

Source check: I opened the node's actual source, [Homotopy theory of dg
sheaves](https://arxiv.org/pdf/1511.02828), especially the standing assumptions at
the start of Sections 2.2 and 3, Example 3.8, Fact 3.10, Fact 3.14, Lemma 3.16
and Corollary 3.17. The source fixes a small ordinary category and an arbitrary
commutative unital coefficient ring. Complexes are unbounded unless explicitly
bounded. The source's lower-bounded chain condition becomes the node's
upper-bounded cochain condition. The extra tensor-product condition of Lemma
3.13 is not an assumption of Lemma 3.16. This source is not a Stacks statement;
the node explicitly explains that distinction. I also read Stacks homology.tex,
`definition-shift-cochain` (011G), and Mathlib's Hom differential to check the
cochain shift/sign convention.

Objects, hypotheses and conclusion clauses, written out before accepting the
Lean correspondence (let s denote max u v w t only in this report):

1. Small ordinary C and commutative ring Λ: `comparison_exists` binds
   `(C : Type u) [Category.{v} C] (Λ : Type w) [CommRing Λ]`. Verdict: exact;
   source-object, source-arrow and ring universes remain independent.
2. P is the category of module presheaves, with objectwise kernels/cokernels:
   every presheaf in `Comparison` is `Cᵒᵖ ⥤ ModuleCat.{s} Λ`; the imported
   abelian functor-category instance supplies the objectwise abelian structure.
   Cochains, `QuasiIso`, shifts and `homologyMap` are Mathlib's recorded notions.
   Verdict: exact. No topology or finite-limit structure on C is assumed.
3. Enhanced D(P) is localization at objectwise quasi-isomorphisms:
   `enhanced`, `locallyKan`, `localizationMap` and `isLocalization` use the
   actual coherent nerve and `FiniteReedy.IsLocalization`. I read the latter's
   full coherent functor-category universal property, not merely its name.
   `localization_vertices` and `localization_mapping` identify all vertices
   and all mapping simplices with the strict functor `localize`. Thus the
   localization and the enriched maps refer to the same objects and arrows.
   `nerveComparison.mapping_space_comparison` compares these enriched maps with
   the dependency's right-pinched mapping spaces. Verdict: exact presentation
   of the enhancement, with no arbitrary equivalence predicate.
4. Free L_T(V) = Λ[Hom(V,T)]: `freeRepresentable` specializes the existing
   `Presheaf.freeYoneda T` to `ModuleCat.of Λ (ULift Λ)`. I read `freeYoneda`
   and its `Sigma.map'` restriction map. ULift is a universe copy of the
   rank-one module; the construction is precisely a sum indexed by Hom(V,T).
   Verdict: exact, with no competing free-representable construction.
5. A is bounded above, each A^p a small coproduct of these L_T, and G is
   arbitrary: `IsFreeBoundedAbove` contains `∃ n, IsStrictlyLE A n` and
   `∀ p, ∃ I T, Nonempty (A.X p ≅ ∐ fun i ↦ freeRepresentable C Λ (T i))`.
   `free_comparison` quantifies over all X,G with only that source condition.
   Verdict: exact; isomorphism to the specified sums is the categorical
   meaning of having those terms. No bound is placed on G.
6. Ordinary degree-r maps and differential: `ordinary_obj` gives exactly
   `X.HomComplex G`; I read Mathlib's `Triplet`, `Cochain`, `δ` and `HomComplex`.
   The family has indices p,q with p+r=q. In degree r+1, the second term in δ
   has sign (-1)^(r+1), giving d_G h - (-1)^r h d_X. `homMap` uses the
   existing graded composition and `ofHom`, and `ordinary_map` specifies
   every map as h ↦ g h f. Verdict: the actual complex and maps, with no
   alternative unconstrained bifunctor.
7. This complex computes derived Hom and the comparison is natural in A,G:
   `comparison : ordinary ⟶ rhom` is a natural transformation on the entire
   product category. `replacements`, `rhom_inverts` and
   `projective_comparison` identify rhom with ordinary Hom from K-projective
   replacements. For P → X they give Hom(P,G) → rhom(P,G) ← rhom(X,G),
   both arrows quasi-isomorphisms. `free_comparison` gives the stated special
   case. Verdict: genuine derived Hom; the replacement existence is part of
   the conclusion, not an additional hypothesis.
8. For arbitrary X,G use Dold--Kan of good nonpositive truncation:
   `simplicialGroups` is `embeddingDownNat.truncLE'Functor` followed by
   `Abelian.DoldKan.Γ`. I read `truncLE'XIso`, `truncLE'XIsoCycles`, its
   differential into cycles and the embedding n ↦ -n. Degree zero is Z^0,
   and positive degree m is E^(-m). I also read that the equivalence's
   forward functor is `normalizedMooreComplex` and its inverse is Γ.
   `realization` forgets to sets and lifts their universe. Using the underlying
   abelian groups preserves precisely the simplicial abelian group and space
   asserted here; the ordinary maps remain Λ-linear presheaf maps.
   Verdict: correct good truncation and normalized-chain inverse.
9. This is the derived mapping space, naturally before passage to homotopy
   categories: `enrichedMaps` uses Mathlib's actual `eHomFunctor`, pulled
   back along `localize`. `mapping_bridge`, `mapping_left`, `mapping_right`
   and their objectwise weak-equivalence fields form an actual natural zigzag
   with `rhom ⋙ realization`; `mapsKan` and `realizationKan` give Kan values.
   Verdict: the comparisons retain actual maps and their naturality.
10. The assertion applies to any cochain model, not just the selected rhom:
    `derivedRealization` and `realization_factors` factor the specified
    realization through `DerivedCategory.Q`. A derived isomorphism from any
    other model therefore gives the same representation in the dependency's
    localization of Kan complexes at weak equivalences. Verdict: all models
    are covered. The sole `HasDerivedCategory` instance is in the standard
    larger universe, supplied by `HasDerivedCategory.standard`; it adds no
    restriction on C or Λ.
11. π₀ = H⁰, and π_m = H^(-m) for all m ≥ 1, naturally at zero:
    `components` is an equivalence with `E.homology 0`, with
    `components_natural`; `homotopy E m z` is a group isomorphism in degree
    m+1 with `Multiplicative (E.homology (-(m+1)))` and
    `homotopy_natural` specifies the actual induced map. Verdict: degree
    zero and every positive homotopy degree are present, with the required
    additive cohomology group (written multiplicatively for the group API).
12. Translation handles other basepoints: `translation_formula` fixes every
    simplex to subtraction of the constant simplex of z;
    `translation_homotopy` ties the induced map to the identifications at z
    and at zero. The HEq fields handle equal realized vertex basepoints;
    they do not introduce a free choice of a basepoint path. Verdict: the
    other-basepoint identifications are translations of those at zero.
13. Precomposition is an equivalence iff all nonpositive cohomology maps are
    isomorphisms: `precomposition_iff` tests exactly the enriched map induced
    by `(f.op, 𝟙 G)` against `IsIso (homologyMap (rhom.map (f.op, 𝟙 G)) r)`
    for every integer r ≤ 0. Verdict: correct direction Y → X, includes
    degree zero, and concerns the specified map rather than some equivalent
    pair of spaces.
14. RHom(X[k],G) ≃ RHom(X,G)[-k], compatibly with precomposition:
    `shift k` is a natural isomorphism of the actual source-shifted rhom
    functor and the coefficient-complex derived shift by -k, for every
    integer k. Verdict: correct sign and naturality. The proof docstring
    gives the degree-r factor (-1)^(k*r) and checks both differential terms.

Dependency checks: I read `HasDerivedCategory`, `HasDerivedCategory.standard`
and `DerivedCategory.Q` in Mathlib; `SCat`, `underlying`, `hom`,
`IsLocallyKan` and `nerveFunctor` in `CoherentNerveInfrastructure`;
`largeNerve` and `IsLocalization` in `FiniteReedyLocalization`;
`CoherentMappingComparison` and `CoherentNerveComparisonStatement` in
`CoherentNerveComparison`; and the mapping-space, weak-equivalence and based
homotopy maps in `EnhancedDiagramsCones`. These are the interfaces the module
uses. The size node is a metatheoretic convention. The proof dependency
`CochainComplex.isKProjective_of_projective` was also opened: it takes exactly
bounded-above cochains and projective terms. The other two proof-only nodes
have no recorded Lean module, so no nonexistent import is needed.

Edge cases checked independently: empty C; terminal C; zero ring and every
characteristic; empty coproduct I; zero source and zero target; a free
representable in degree zero; arbitrarily unbounded G; E with positive-degree
terms; E concentrated in degree -m; an acyclic two-term E; π₀ and m=0 in the
positive-group field (π₁); k=0,1,-1. The index I lives in the presheaf-module
universe, and the extra t allows arbitrary enlargement. None of these cases
is excluded by a nonemptiness, nontriviality, boundedness or universe-equality
hypothesis.

Independent searches, using words different from the worker's:

- `msearch.py ... leanfinder "simplicial function complex module presheaves
  projective model structure"`: eight hits on projective resolutions and
  `isKProjective_of_projective`, no enhanced function-complex statement.
- `msearch.py ... loogle '"HomComplex"'`: twelve constituent hits, including
  the existing cochain families, cocycles and HomComplex used here; no match
  for the enhanced localization comparison.
- `msearch.py ... leansearch "Mapping space of derived category via Dold Kan
  and homology of hom complex"`: eight constituent hits including
  `Abelian.DoldKan.Γ`, derived homology functors and `DerivedCategory.Qh`;
  no exact statement.
- Direct `rg` in pinned Mathlib, upstream WeilConjectures, the project's
  `lean/Sheaf` and `dag/lean_names_upstream.json` for `derived.?[Hh]om`,
  `function.?[Cc]omplex`, `PresheafDGFunctionComplex`, `simplicialGroups`,
  `freeRepresentable` and the node id found constituent constructions,
  sheaf-internal derived Hom, and this item's consumers, not an existing
  presheaf enhanced function-complex comparison or a name collision. The
  existing `Presheaf.freeYoneda` is reused, as are Mathlib's Dold--Kan and
  Hom-complex constructions; the local helpers only specialize/assemble them.

Mismatches and changes: no mathematical signature mismatch was found, and no
Lean declaration was rewritten. Comparing with the current shared node found
that the sandbox omitted the current `lean_audit` field; I restored that field
verbatim to preserve metadata outside the permitted delivery delta. I appended
this independent reading and retained the worker report. There are no hollow
definitions, no theorem proved in this stage, and only `comparison_exists` has
`sorry`. Structural proof fields in definitions establish the explicitly
constructed maps. All declarations have source/blueprint docstrings; the theorem
carries all six proof steps. Every Lean line is at most 100 characters; all
variables and universe levels are explicitly bound, with autoImplicit disabled.
The node's `lean.statement` matches the theorem signature verbatim.

Validation: the prescribed `scompile.py Q113 lem-cbc-presheaf-dg-function-complex
lean/Sheaf/Paper/PresheafDGFunctionComplex.lean` compiled both the sandbox check
and the delivered library module cleanly, within the unchanged 60-second limit.
