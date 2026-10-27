## Worker report

Module: `Sheaf.CategoryTheory.DerivedAdjointSESMates`.
Main statement: `CategoryTheory.derivedAdjointSESMates`.

This states the whole adjoint-sequence assertion, including the canonical boundary
and the three comparison squares. It does not replace the boundary by an arbitrary
triangle completion. The module has two postponed theorem proofs, `mates_zero` and
`derivedAdjointSESMates`, each with the source, blueprint id and natural-language
proof in its docstring. All helper data and maps are real structures or definitions.
They package this node's specified data and formulas, rather than introduce a
second definition of derived categories, exactness, K-injectivity or SES triangles.

Hypotheses, clause by clause:

- The abelian categories are `A`, `B` with independent object/morphism universes
  `uA/vA`, `uB/vB`. The theorem has `IsGrothendieckAbelian.{vA} A` and the
  corresponding instance for B. `HasDerivedCategory.{wA/wB}` independently
  specifies each derived Hom universe. There is no equality between these universes.
- `DerivedAdjointSESData.E`, `H`, `E_zero`, `H_zero` give the three functors,
  with index 0 the identity on both sides. `addE`, `exactE_left`,
  `exactE_right` render additive and exact; `adj` supplies each specified
  ordinary adjunction. `addH` records the induced additivity of right adjoints
  (redundant evidence, derivable by transposing sums as proof step 1 explains).
- `d`, `e`, `zero`, `shortExact X` are the natural objectwise short exact
  sequence in precisely the order E2, E1, E0. The equation used to construct
  its `ShortComplex` is evaluated from the natural-transformation equation.
- `P`, `F`, `addP`, `addF`, `adjPF` are the additive ordinary adjunction P ⊣ F.
- `resolving`, `resolves`, `LP`, `εP`, `leftDerived`, `computesP` give the
  specified resolving class, its quasi-isomorphic representatives, total left
  derived functor and its invertible comparison on that class. These use
  Mathlib's universal `IsLeftDerivedFunctor`, not an unconstrained functor.
- `injectiveResolves` and `injectiveResolvesB` render the assumed K-injective
  resolutions with injective terms in both categories, using actual quasi-isomorphisms.
  `CochainComplex.IsKInjective` is Mathlib's null-homotopy condition on maps from
  acyclic complexes; it is not redefined here.
- `R`, `ηR`, `rightDerived` specify R(FH_i) as total right derived functors of
  the actual termwise composite H_i ⋙ F. `shiftLP`, `shiftR`, `shiftεP`,
  `shiftηR` record the stipulated normalized standard cochain shifts. Requiring
  these standard comparison compatibilities does not select arbitrary shift structures.

Conclusions for one system are the fields of `DerivedAdjointSESResult`, which
is existentially supplied by the main theorem:

- `er`, `dr` are Mathlib `conjugateEquiv` applied to the specified adjunctions
  and e, d. They are ordinary right mates, in that order. `split J` gives a
  `ShortComplex.Splitting` for every injective J; such a splitting implies short
  exactness and asserts no natural choice in J. The auxiliary theorem
  `mates_zero` supplies precisely the zero composite needed to type the sequence.
- `kInjective` says each H_i sends every K-injective complex to a K-injective
  complex. `computesR` states invertibility of the normalized right comparison
  on every K-injective representative.
- `rightRow I` is constructed from the termwise mates after applying F. Its
  terms are FH0I, FH1I, FH2I, not replacements by their separate cohomologies.
  `right_exact`, `right_split` give its short exactness and splitting in each
  degree when I is K-injective with injective terms.
- `L i` is literally `LP ⋙ (E i).mapDerivedCategory`, thus D(E_i) LP in
  mathematical composition order. `εL` constructs the comparison by whiskering
  εP and the canonical `mapDerivedCategoryFactors`. `adj i` gives L_i ⊣ R_i;
  `normalize` is the equality of its Hom bijection with ordinary termwise
  transposition on every chain map. No arbitrary derived adjunction is substituted.
- `leftRow M` is the actual E2PM → E1PM → E0PM sequence. `left_exact` makes
  its Mathlib SES boundary available. `l21`, `l10`, `b` are natural arrows
  for the left triangle; `left_distinguished` and `left_first/second/boundary`
  characterize it on resolving representatives by that canonical SES triangle.
- `r01`, `r12`, `δ` and `right_distinguished` give the natural distinguished
  right triangle. `right_first`, `right_second`, `right_boundary` compare ALL
  three maps to `DerivedCategory.triangleOfSESδ (right_exact I)` through ηR.
  These equations hold for every such I; together with invertible `computesR`
  they assert independence under the normalized comparisons between resolutions.
  Thus the triangle data cannot be chosen by an arbitrary completion.
- `first_mate`, `second_mate` specify the first two derived arrows as mates.
  `boundary_mate` states the contravariant Hom sign explicitly: the transpose
  of δ after u is minus the shifted transpose of u after b. It includes the
  inverse R0 shift comparison to type the transpose into K[1].

Comparison hypothesis and conclusion:

- A primed system has its own four size universes and the same data/result
  interfaces. Applying the theorem to D' supplies its result as well; the
  comparison applies to any results with these canonical normalizations.
- `DerivedAdjointSESComparison.s`, `t`, `S`, `T`, `εS`, `εT`, `derivedS`,
  `derivedT` state that S and T are total left derived functors of additive
  abelian-category functors. `exactS`, `exactT`, `shiftS`, `shiftT`,
  `shiftεS`, `shiftεT` render exactness and the normalized cochain comparisons.
- `θ i : T ⋙ D'.L i ≅ D.L i ⋙ S` is exactly L'_i T ≅ S L_i. `shiftθ`
  records its stipulated compatibility with cochain shifts.
- `diagrams N` provides resolving representatives M of N and M' of TN and
  actual isomorphisms x, x'. It requires that S is computed by s on the three
  row terms and their cone, and that the termwise s-image row is short exact.
  These are the whole-resolution-diagram condition spelled out in DAG proof
  step 6, including its computation on the cone. The comparison is a map of
  the entire ShortComplex after localization, with all three component equations
  identifying its maps with θ via x, x', εL and εS.
- `DerivedAdjointSESDiagramPath` retains chain diagram maps, not three unrelated
  object maps. Forward steps are maps of short exact sequences. Backward steps
  invert their localized short-complex isomorphisms; these are exactly the
  objectwise quasi-isomorphisms. Composition allows arbitrary finite zigzags.
  Identities already occur as forward identity maps. No boundary square is
  assumed in this comparison structure.
- `derivedAdjointSESComparisonMate` constructs each β by the exact displayed
  formula: primed Hom transposition of θ at R_i K followed by S of the normalized
  counit, followed by φ. The theorem quantifies over every `φ : S.obj K ⟶ K'`.
- The three conjunctions in the theorem are precisely the two ordinary-arrow
  squares and the connecting square. The latter is T(δ_K), the canonical T
  shift comparison, then β0[1], equal to β2 followed by δ_K'. No β is assumed
  invertible, and no inverse of a β occurs.

Dependency declarations read and used:

- def-sp-grothendieck-abelian: `CategoryTheory.IsGrothendieckAbelian`,
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic (the recorded Mathlib match).
- def-weil-abstract-derived-category: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, Mathlib.Algebra.Homology.DerivedCategory.Basic.
- def-galois-exact-functor: `PreservesFiniteLimits`, `PreservesFiniteColimits`
  from Mathlib.CategoryTheory.Limits.Preserves.Finite; `exactFunctor_iff`
  from Mathlib.CategoryTheory.Limits.ExactFunctor verifies that these are exactness.
- def-weil-pbc-additive-functor: `Functor.Additive`,
  Mathlib.CategoryTheory.Preadditive.AdditiveFunctor.
- def-weil-triangulated-category: `Pretriangulated`, `IsTriangulated`,
  `Functor.IsTriangulated`, from the recorded Mathlib triangulated modules.
- All stated proof dependencies are imported: Injective (publicly available through
  the K-injective import); `Adjunction.preservesKInjectiveComplexes` from
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp;
  `exists_rightDerived_of_enough_isKInjective` from Sheaf.CategoryTheory.KInjectiveTotalDerived;
  `DerivedCategory.triangleOfSESδ`, `triangleOfSES_distinguished`, `triangleOfSES.map`
  from Mathlib.Algebra.Homology.DerivedCategory.ShortExact;
  HomotopyCategory.DegreewiseSplit and DerivedCategory.KInjective for the recorded
  split boundary and fully faithful localization results;
  `derivedAdjunctionOfResolvingClass` from Sheaf.SixFunctors.ResolvingDerivedAdjunction;
  `Adjunction.mapHomotopyCategory` from WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction;
  `CochainComplex.HomComplex.productHom_ses_boundary` from
  Sheaf.Algebra.Homology.ProductHomSesBoundary. The canonical definitions used in
  public signatures are publicly imported; proof-only infrastructure is imported normally.

Edge cases checked: all complex degrees are integers, with no boundedness restriction.
Zero complexes and zero objects satisfy the same diagrams; neither a nonzero object
nor a nonempty support is assumed. P need not be exact and F need not preserve
K-injectives. The sequence need not split naturally, nor split on arbitrary objects.
The comparison permits φ=0 and noninvertible β. Backwards zigzag steps are restricted
to objectwise quasi-isomorphisms; ordinary forward diagram maps need not be invertible.
All object, morphism and localization universes are explicit and independent.

Searches actually run:

- msearch leanfinder, "Derived adjunction mates of a short exact sequence of exact
  functors with canonical boundary compatibility": 8 hits on SES connecting maps,
  Ext functoriality and derived adjunction factorization, none the combined assertion.
- msearch loogle, "conjugateEquiv, triangleOfSES, derivedAdjunction": unknown identifier
  `conjugateEquiv` in that search service, so this search is inconclusive, not no match.
- msearch grep, `rightAdjoint.*triangle|triangle.*rightAdjoint|derivedAdjoint|conjugateEquiv`,
  CategoryTheory: existing mates infrastructure, no combined SES assertion.
- msearch leansearch, "Derived adjunction mates preserve canonical short exact sequence
  boundary": 8 hits on the derived-adjunction API; none the combined assertion.
- rg over lean/Sheaf and lean/WeilConjectures for derived-adjoint/SES-mate/resolving
  names, plus the prescribed grep for this node id upstream: no exact match. The
  one derived-base-change-open-transpose documentation hit explicitly excludes SES
  boundaries. rg over Mathlib, project sources and dag/lean_names_upstream.json for
  every new DerivedAdjointSES name found no collision.
- Read the full source signatures/docstrings of the recorded statement dependencies
  and the existing derived adjunction, exact-functor localization, mates, canonical
  SES triangle and signed product-Hom APIs. Read the local Stacks source at the
  labels lemma-derived-canonical-delta-functor, lemma-derived-adjoint-functors,
  lemma-adjoint-is-exact. No external mathematical assertion is substituted.

No statement correction, dependency repair or new DAG node was needed.
The helper structures merely group this node's own long hypotheses and conclusions.

Validation: the prescribed scompile.py compiles both sandbox and final module paths
cleanly, with no errors or warnings. The only proof holes are the two named theorems.

## Second reading by N6

Self-review with the node and completed module open; no separate agent was started,
as the dispatcher brief expressly forbids it. The maintainer performs the independent review.

I matched E0=id, H0=id, both exactness directions, all ordinary adjunctions, P/F
additivity, the resolving class, K-injective resolutions, and normalized derived
comparisons to the data fields above. I checked every conclusion against the result
fields: split ordinary mates, preservation of K-injectives, the degreewise split
FH sequence, natural distinguished triangle, canonical boundary, resolution independence,
L_i=D(E_i)LP, the normalized adjunction and its signed connecting identity. Finally I
matched s/t/S/T, all three θ maps and their WHOLE diagram lifts, arbitrary φ, the counit
formula for β, and all three final squares, including T's shift comparison.

The initial compile required exposing K-injectivity publicly and explicitly naming
its namespace on a computed complex; those are fixed. A review added the B-side
K-injective-resolution assumption to reflect the node's plural categories, and recorded
shift compatibility of the derived comparison maps so a nonstandard sign cannot be
silently chosen. The comparison path retains inverse objectwise quasi-isomorphisms
instead of excluding zigzags. The result's boundary equations are imposed for every
representative, and the right comparison is explicitly invertible there, which makes
the claimed resolution independence reviewable. No mismatch or disputed statement remains.
