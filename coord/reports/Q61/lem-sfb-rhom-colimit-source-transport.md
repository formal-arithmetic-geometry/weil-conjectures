## Worker report

Item: `lem-sfb-rhom-colimit-source-transport`. The new module is
`Sheaf.Algebra.Homology.RHomColimitSourceTransport`; its main declaration is
`CategoryTheory.RingedHomColimitTransport.source_transport`. Its proof is `sorry`.
The two helper definitions `strictColimit` and `target` are actual compositions of
existing functors, with no postponed data or proofs. They package precisely the two
endpoints of this node's comparison; neither defines another internal Hom or category.
The original mathematical statement, proof and proof dependencies are unchanged.

Hypotheses and objects:

- The small ringed site is `{C : Type c} [Category.{v} C]`,
  `J : GrothendieckTopology C`, with coefficient and module universe `max c v r`.
  The topology is the sheaf-theoretic site presentation used by the recorded module
  category, as also used in both recorded internal-Hom dependencies. Its modules are
  small relative to that universe. The separate object and arrow universes are retained.
- Commutativity is `R : Sheaf J CommRingCat.{max c v r}`. The underlying ring sheaf
  and module category are the existing `RingedHomUniverses.Modules J R`, definitionally
  `SheafOfModules` and the recorded `ringedSiteModules` specialization.
- `HasSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat` are the
  standard sheafification structures available in this small-site universe, needed by
  the existing abelian module category. They add no geometric assumption.
- `HasDerivedCategory.{w} (Modules J R)` is the size-convention choice of the ordinary
  unbounded localization. `D J R` and `Complex J R` are the existing abbreviations for
  this derived category and the integer-indexed cochain category; no bounded category
  or restricted source class is introduced.
- The small index category is `{I : Type (max c v r)} [SmallCategory I]`.
  Filteredness is explicitly bound on `source_transport` as `[IsFiltered I]`.
  This is deliberately a theorem binder: an unused section variable would otherwise
  disappear from Lean's elaborated statement. `HasColimitsOfShape I (Modules J R)`
  supplies the chosen sheaf colimits, which exist in this universe. Complex colimits
  are degreewise, using the project's degreewise-colimit infrastructure.
- The arbitrary target diagram is `N : I ⥤ Complex J R`; its colimit is the complex
  `colimit N`. No termwise bound, cohomological bound, continuity, finite generation,
  or K-injectivity condition on N or A is assumed.

Clauses of the conclusion, in order:

1. `strictColimit` is contravariant in the source complex and covariant in the entire
   target diagram. Its value at L,N is definitionally
   `DerivedCategory.Q.obj (colimit (N ⋙ homFixed J R L))`. It uses exactly the fixed
   `coefficientHomResolution` and existing Hom-complex bifunctor. Thus it is the
   image of a termwise sheaf colimit, without any derived-category colimit.
2. `target` at A,N is definitionally
   `(derivedInternalHomOfUniverses J R).obj (op A, Q.obj (colimit N))`.
   The existential G and the natural isomorphism
   `rho : Q.op ⋙ G ≅ strictColimit J R` express descent of the left endpoint in the
   source. Together with `alpha : G ⟶ target J R`, they express representative
   independence of the entire comparison, not only of its right endpoint.
   In detail, any specified `e : Q.obj L ≅ A` induces the identification
   `G.mapIso e.op` followed by `rho.app (op L)`. Naturality of rho identifies source
   chain maps with their canonical precomposition/colimit maps. Uniqueness up to the
   canonical identification follows from Q's localization universal property: two
   such factorizations and the specified rho's have a unique compatible natural
   isomorphism. This is the arrow-valued localization in the node's proof.
3. The first conjunct fixes alpha on every L,N as `rho.hom` followed by
   `Q.map (colimit.post N (homFixed J R L))` and the inverse of the existing
   `coefficientHomResolutionIso J R L (colimit N)`. Hence alpha is exactly the node's
   canonical comparison under its canonical endpoint identifications, not an arbitrary
   arrow or an extra assumption about a chosen map.
4. The second conjunct is the source-isomorphism square. `G.mapIso e.op` is the
   localized meaning of `colim H(e,N_i)`; `target.mapIso e.op` is H(e,N_infinity).
   The displayed order uses Lean's left-to-right composition, giving exactly
   H(e,N_infinity) alpha_A' = alpha_A colim H(e,N_i) in the node's notation.
   Both vertical maps are isomorphisms because they are functor images of e.op.
   No chain-map representative of an arbitrary derived isomorphism is assumed.
5. The existential `t A n` is a natural isomorphism from G(A[n]) to G(A)[-n].
   The third conjunct is exactly the signed-shift comparison square, with
   `(sourceShift J R A n).inv` rendering the node's s. The imported sourceShift has
   its sign fixed by the existing `LeftNormalization` and `LeftFormula`, including
   arbitrary complex representatives. In particular, its inverse is the node's
   Hom(A[n],N) -> Hom(A,N)[-n] convention.
6. The final conjunct specifies t, rather than merely asserting an unspecified
   isomorphism between its endpoints. For every L,n, `sigma` is a natural isomorphism
   `homFixed (L[n]) ≅ homFixed L ⋙ shiftFunctor _ (-n)` and `LeftFormula ... sigma.symm`
   is its product-projection formula. It multiplies Hom degree q by `(n*q).negOnePow`
   and reindexes source degree by n; the inverse has the same sign, so this is also
   exactly the forward normalization required by the node.
   The last equation tests t on every actual injection of `N ⋙ homFixed (L[n])`.
   The right side applies sigma at N_i, the canonical `Q.commShiftIso (-n)`, and
   the shifted injection for `N ⋙ homFixed L`. The left side transports Q(L[n])
   to (QL)[n] by `Q.commShiftIso n`. This determines the actual colimit-induced t
   and termwise colimit-shift identification, without choosing an arbitrary map.
7. Naturality in every target-diagram transformation is part of the types:
   G and target are functors into `(I ⥤ Complex) ⥤ D`; alpha and rho are natural
   transformations there, and t and sigma are natural isomorphisms. Thus each
   square is natural in N, including its two vertical maps. The two displayed
   squares with invertible vertical maps are exactly the asserted conjugacies.

Dependencies read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: the recorded site convention;
  its Grothendieck topology is used for the module category as in the dependency.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  general-site module category, through the existing Modules abbreviation.
- `def-weil-size-convention`: its convention record is implemented by the explicit
  c,v,r,w universes, small index universe and `HasDerivedCategory` binder.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and Q's existing shift comparison.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses`: the actual unbounded bifunctor.
- `Sheaf.Paper.DerivedInternalHomFilteredColimitData`,
  `WeilConjectures.SfbHomFilteredColimit.homFixed`: the unchanged strict models.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `colimit`, `colim`, `colimit.post`,
  `colimit.ι`, and `Mathlib.CategoryTheory.Filtered.Basic`, `IsFiltered`.
- `WeilConjectures.Algebra.Homology.HomComplex`, `homComplexFunctor` and `homComplex`:
  the existing product Hom construction; no new Hom model.
- Two already landed nodes are added to stmt_deps: the existing
  `lem-weil-pbc-ringed-internal-hom-exact-restriction` supplies
  `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`,
  `RingedHomUniverses.Modules`, `Complex`, `D`, `LeftFormula`, `sourceShift` and its
  full representative normalization; `def-coef-hom-representative-evaluation`
  supplies `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`,
  `WeilConjectures.coefficientHomResolution` and `coefficientHomResolutionIso`.
  Neither node is modified and no dependency interface is repaired.
- Existing proof dependencies imported non-publicly:
  `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
  (`SheafOfModules.grothendieckAbelian_with_localized_generator`),
  `WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits`
  (the homology/exact-colimit instance),
  `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`
  (`CategoryTheory.quasiIso_homComplex_map`), and
  `WeilConjectures.Algebra.Homology.HomComplexShiftLeft`
  (`CategoryTheory.homComplex_shift_left`). The independent-universe versions are
  already available through the generic recorded Hom/shift modules.

Edge cases checked before and after writing:

- Identity source isomorphisms give the identity naturality square. Arbitrary derived
  isomorphisms, including ones not represented by a chain isomorphism, remain allowed.
- n=0 gives identity reindexing; n=1 and n=-1 both have degree-q sign (-1)^q.
  All negative integers are included, and characteristic 2 simply makes the signs equal.
- Zero source, zero target diagrams, the one-object filtered index category and constant
  diagrams are allowed. Empty filtered index categories are excluded exactly by
  IsFiltered's nonemptiness, as in the mathematical statement.
- Unbounded source complexes and target complexes occur without any support hypothesis.
  Site object and morphism universes are independent and the module/index universe
  contains both. All introduced variables and universes are explicitly bound.

Searches (2026-10-21):

- msearch.py leanfinder: "Canonical derived internal Hom filtered colimit comparison
  commutes with source isomorphisms and signed source shifts". Eight hits, including
  derived exact-functor factorization/shift lemmas, Ind colimit comparisons and
  `colimitObjIsoColimitCompEvaluation_ι_inv`; none is this internal-sheaf-Hom statement.
- msearch.py leansearch: "Naturality of the canonical derived internal Hom filtered
  colimit comparison under source isomorphisms and source shifts". Eight hits, including
  `commShiftIso_hom_naturality`, `Cofork.IsColimit.homIso_natural`,
  `Functor.leftDerivedNatIso`, `Cotrident.IsColimit.homIso_natural`,
  projective-resolution naturality and `isoShift_hom_naturality`. None gives this result.
- msearch.py loogle: `"colimit", "shift"`: no hits. An initial comma-separated-name
  query reported unknown `CategoryTheory.Limits.colimitComparison`; reading the source
  identified the correct canonical-map name, `CategoryTheory.Limits.colimit.post`.
- msearch.py grep:
  `(colimit|colim).*(homFixed|internalHom|derivedHom)|(homFixed|internalHom|derivedHom).*(colimit|colim)`:
  no Mathlib hits. Direct rg of Mathlib HasLimits found colimit.post, its injection
  equation, and `colimit.map_post`, which supply generic cocone infrastructure.
- Direct rg of lean/WeilConjectures and lean/Sheaf with that expression and the item id:
  no upstream statement; project hits are strict homFixed continuity and its parent
  triangle-closure predicate. The parent does not state the source-transport equations.
  Searches of the planned namespace and declaration name found no duplicates.
- Reading the existing generic shift module found the exact signed `LeftFormula` /
  `sourceShift` interface, so it is imported rather than redefined.

No STATEMENT-DISPUTED flag, source fault, statement correction, new node, or dependency
module is needed. The source Stacks locations were read locally: sites-cohomology.tex
section-hom-complexes (0A8X), lemma-RHom-well-defined (0A95), and
lemma-RHom-triangulated (08JC). The transport/cocone calculation is explicitly the agent
extraction recorded in this node, not a claim that 08JC itself states colimit transport.

Validation: scompile.py compiled the module as both an isolated sandbox module and its
actual library module cleanly. A second compile checks the explicit filteredness binder.
The required delivery dry run and final delivery are run after preparing this record.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
