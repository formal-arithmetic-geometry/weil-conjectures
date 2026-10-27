## Worker report

This delivery states lem-sfb-exact-postcomposition-kinjective-descent in
Sheaf.CategoryTheory.ExactPostcompositionKInjectiveDescent. Every theorem has proof
`sorry`; the four helper definitions have explicit bodies and only package the canonical
comparison unit or its normalization equations. No node statement or dependency is changed.

Hypotheses and clauses, read against the complete node:

- Abelian categories A0, A1, B (and A2 in the composition clause) are explicit `Type u`
  variables with independent `Category.{v}` and `Abelian` instances. Each derived category
  has its own `HasDerivedCategory.{w}` instance. There are no universe equalities or
  boundedness restrictions; `CochainComplex A ℤ` is the unbounded complex category.
- Enough K-injective resolutions is exactly `∀ N, ∃ (I) (a : N ⟶ I),
  I.IsKInjective ∧ QuasiIso a`, named h0, h1, h2 as appropriate. In particular no
  monomorphism condition on a and no Grothendieck-category assumption is added.
- H is `A1 ⥤ A0` with `H.Additive`. Its exact additive left adjoint is the binder
  `L : A0 ⥤ A1`, `[L.Additive]`, `[PreservesFiniteLimits L]`,
  `[PreservesFiniteColimits L]`, and `adj : L ⊣ H`. The composition theorem supplies
  separate LH, LJ, LP and adjH, adjJ, adjP for H, J, P.
- Each E_i has `Additive`, `PreservesFiniteLimits`, and `PreservesFiniteColimits`.
  None has a `PreservesKInjectiveComplexes` hypothesis. The specified c is
  `H ⋙ E0 ≅ E1`, using Lean's diagrammatic composition convention.
- RH is the dependency's `H.rightDerivedFunctorOfQuasiIsoResolutions h1`, not the
  upstream version requiring monomorphic resolutions. The helper `kInjectiveDescentUnit`
  is the dependency's canonical homotopy-category unit, transported through
  `DerivedCategory.quotientCompQhIso`. Its source is Q(HI), its target RH(QI).
- D(E_i) is exactly `E_i.mapDerivedCategory`. Its canonical localization comparison
  is `E_i.mapDerivedCategoryFactors`, with direction D(E_i)(QI) → Q(E_i I).
- `exists_unique_normalizedKInjectiveDescent` asserts `∃! r` of the required natural
  isomorphism type RH ⋙ D(E0) ≅ D(E1). `IsNormalizedKInjectiveDescent` asserts for
  every K-injective I that D(E0)(gamma_I), followed by r at QI and the E1
  localization comparison, equals the E0 localization comparison followed by Q(c_I).
- The second conjunct quantifies over EVERY N, I and resolution a with K-injective
  target and QuasiIso a. It compares r at QN followed by D(E1)(Qa) and the E1
  localization comparison with the dependency's canonical source resolution isomorphism
  followed by the E0 localization comparison and Q(c_I). This is precisely the stated
  component formula without requiring a preferred or monomorphic resolution.
- The last conjunct is the naturality equation for arbitrary X, Y and f in D(A1),
  not merely maps represented by a preselected resolution. `normalizedKInjectiveDescent_ext`
  says the normalization ALONE determines r; together these clauses give independence
  of all resolution choices. The source's unique homotopy-class representation is the
  existing Hom-bijection proof dependency, not a new representation hypothesis.
- Composition data have `d : P ≅ J ⋙ H`, `c' : J ⋙ E1 ≅ E2`, and
  `b : P ⋙ E0 ≅ E2`. The hb equation is the node's b = c' ∘ (cJ) ∘ (E0d), with
  the canonical `associator J H E0` inserted. `normalizedKInjectiveDescent_comp`
  concludes preservation of K-injectives by H, J and P, and existence of the normalized
  compositor RP ≅ RJ ⋙ RH. Its normalization explicitly uses the unit for H at JI,
  then RH applied to the unit for J at I, following Q(d_I); thus JI is the specified
  intermediate representative. `normalizedKInjectiveCompositor_ext` states uniqueness
  from this normalization alone. The composition theorem concludes the equation
  rb = (κ whiskered by D(E0)) ≫ associator ≫ (RJ whiskered with rc) ≫ rc'
  for all normalized rc, rc', rb, exactly the node's displayed formula.
- `normalizedKInjectiveDescent_id` gives the canonical R1 ≅ 1, normalized on EVERY
  complex by the degreewise identity comparison `mapHomologicalComplexIdIso`. For
  E1 = E0 and `c = leftUnitor E`, it identifies r with this canonical comparison
  whiskered by D(E), followed by the canonical left unitor. This is the identity
  clause with its required coherence maps, not a chosen arbitrary identification.
- `kInjectiveDescent_equivalence_resolutions` quantifies over additive exact
  equivalences U and states `I.IsKInjective ↔ (UI).IsKInjective`. It carries every
  specified resolution a to a quasi-isomorphism with K-injective target and also states
  enough resolutions in the equivalent category. Exactness and additivity are the
  node's hypotheses; there is no extra size constraint.
- `IsNormalizedKInjectiveSquare` records the unit-normalized RH transport square
  for α : U1 ⋙ H' ≅ H ⋙ U0. `exists_unique_normalizedKInjectiveSquare` states existence
  and uniqueness of that square under exact additive equivalences U0 and U1.
- `normalizedKInjectiveDescent_equivalence` includes W : B ≅ B' as an equivalence
  functor, ε0 : U0 ⋙ E0' ≅ E0 ⋙ W and ε1 : U1 ⋙ E1' ≅ E1 ⋙ W, and the pointwise
  underived compatibility equation from node proof step 10. It asserts exactly the
  corresponding derived equality, using the existing canonical
  `mapDerivedCategorySquareIso ε0` and `mapDerivedCategorySquareIso ε1`.
- `normalizedKInjectiveCompositor_equivalence` includes αH, αJ, αP, compatible
  d and d', normalized transport squares for H, J, P, and normalized κ, κ'. Its
  conclusion is the full equality transporting κ under the equivalences, including
  evaluation at RJ(X). Thus the last sentence of proof step 10 is included too.

Dependency declarations used (their full signatures and docstrings were read):

- Mathlib.CategoryTheory.Abelian.Basic: `CategoryTheory.Abelian` (def-sp-abelian).
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.quotientCompQhIso`
  (def-weil-abstract-derived-category).
- Mathlib.CategoryTheory.Limits.Preserves.Finite: `PreservesFiniteLimits`,
  `PreservesFiniteColimits` (def-galois-exact-functor); Mathlib.CategoryTheory.Preadditive.
  AdditiveFunctor: `CategoryTheory.Functor.Additive` (def-weil-pbc-additive-functor).
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its `Unit`,
  `Unit_isIso`, `ObjIso`, `universal`, and `unique` declarations
  (def-sfb-right-derived-functor). The actual module is imported publicly.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`
  (lem-weil-pbc-exact-functor-derived-factorization), publicly imported.
- WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate:
  `CategoryTheory.Functor.mapDerivedCategorySquareIso`, the existing canonical exact
  comparison under an underived square, publicly imported for the equivalence clause.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp:
  `CategoryTheory.Functor.PreservesKInjectiveComplexes` and
  `CategoryTheory.Adjunction.preservesKInjectiveComplexes`
  (lem-weil-pbc-right-adjoint-preserves-kinjective), imported as a proof dependency.
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction:
  `CategoryTheory.Adjunction.mapHomotopyCategory`
  (lem-weil-pbc-termwise-adjunction-homotopy), imported as a proof dependency.
- Mathlib.Algebra.Homology.DerivedCategory.KInjective:
  `CochainComplex.IsKInjective.Qh_map_bijective` and `quasiIso_iff`
  (lem-weil-pbc-kinjective-hom-derived), imported as a proof dependency.

Edge cases: zero categories and zero E_i make both normalization composites the unique
zero-category arrows; they introduce no nonzero or faithful hypothesis. Identity H, J,
P with identity d reduces the compositor normalization to the unit comparisons. With
H = identity and arbitrary automorphism c, normalization gives D(c); only c = identity
is asserted to give the identity. Non-monomorphic quasi-isomorphisms are accepted by the
resolution binders. Nontrivial choices of K-injective representatives are covered by
normalization-only extensionality. All object, morphism, and localization universes,
including primed transport categories, are independent explicit universes. The ordinary
zero and unbounded complexes are included. No need for E_i to preserve K-injectives is
introduced in any normalization or transport equation.

Searches for reuse:

- msearch.py leanfinder: "An exact functor after a right derived functor descends a
  natural isomorphism on K injective resolutions compatibly with composition and
  equivalences"; eight hits, concerning rightDerivedZeroIsoSelf and injective-object
  resolutions, not this unbounded comparison and coherence theorem.
- msearch.py loogle: "CategoryTheory.Functor.rightDerivedNatIso,
  CategoryTheory.Functor.mapDerivedCategoryFactors"; no combined hit. The generic
  `rightDerivedNatIso` source was also read: it assumes supplied universal derived pairs,
  rather than providing exact postcomposition descent with these normalizations.
- msearch.py grep: `rightDerived.*[Nn]at|[Kk][Ii]njective.*[Ee]xact|[Ee]xact.*[Kk][Ii]njective`
  in Mathlib/CategoryTheory; ten hits in generic and objectwise RightDerived modules.
- msearch.py leansearch: "A natural isomorphism after exact postcomposition of a total
  right derived functor is determined by its unit normalization on K injective complexes";
  eight hits, including generic totalRightDerivedUnit and rightDerivedNatIso, but no
  theorem stating this node's clauses.
- rg in lean/WeilConjectures and lean/Sheaf for `kInjectiveDescent`,
  `NormalizedKInjective`, `exact.*postcomposition`, and `exactPostcomposition`; no
  existing declaration with the complete statement. SupportedCohomologyHom's private
  exactPostcompositionDerivedIso concerns bounded-below derived functors and has neither
  this arbitrary-resolution API nor the normalization, compositor or equivalence clauses.
  SingleRightDerivedExactComposition concerns a single-complex comparison instead.
- grep for the item's id in lean/WeilConjectures: no result. The upstream name index
  has no existing declarations with the new names. The prescribed CompactObject example
  is now withdrawn and contains no declarations; its node records Mathlib's existing
  notion. This delivery follows the current module/public-section conventions instead.

Source checked directly in literature/stacks-project/derived.tex: lemma-K-injective
(Tag 070I), lemma-K-injective-defined (070Y), lemma-enough-K-injectives-implies (070K),
and lemma-adjoint-preserve-K-injectives (08BJ). Also read
sites-cohomology.tex, lemma-restrict-direct-image-open (0D6G). The node's explicit
normalized descent proof, including the expanded equivalence square in step 10, supplies
the coherence formulas beyond these basic source lemmas. No statement dispute found.

Validation: scompile.py Q101 lem-sfb-exact-postcomposition-kinjective-descent compiled
this file as sandbox and library module cleanly (9.2 s and 10.9 s). No compiler warning
other than allowed sorry warnings, and no diagnostic commands in the delivered file.

## Second reading by Q101

I reread the full node and module clause by clause in this resumed worker session.
This is a self-check, not an independent agent review: the dispatch explicitly forbids
starting other agents and assigns the independent reading to the maintainer. The
normalization arrow directions, the source resolution isomorphism, and the two whiskering
orders in composition and equivalence transport match. The identity clause uses the
canonical comparison, not an arbitrary isomorphism. Extensionality is stated for
normalization alone, so the auxiliary resolution and naturality conjuncts do not weaken
the uniqueness assertion. All theorem proofs are sorry and every helper has a real body.
No statement correction, new node, dependency-interface repair or omitted clause was
needed. The maintainer's independent delivery review remains to be performed.
