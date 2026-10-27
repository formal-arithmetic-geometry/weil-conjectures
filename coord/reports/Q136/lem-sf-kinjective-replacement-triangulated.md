## Worker report

The module `Sheaf.CategoryTheory.KInjectiveReplacementTriangulated` states
`HomotopyCategory.KInjectives.replacement_triangulated`, with its proof `sorry`.
It also supplies two real CommShift instance constructions for the existing upstream
inclusion and localization wrappers. They reuse ObjectProperty.ι's inherited comparison
and the comparison of its composite with DerivedCategory.Qh; no object is chosen from
a postponed existence theorem. No new mathematical definition or dependency repair is needed.

Hypothesis and clause correspondence:

- An arbitrary abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`.
  Its chosen unbounded derived category is `[HasDerivedCategory.{w} C]`, retaining
  independent object, morphism and localization universes.
- Every complex admits a quasi-isomorphism to a K-injective complex is exactly
  `h : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (i : K ⟶ I),
  I.IsKInjective ∧ QuasiIso i`. There is no `Mono i` hypothesis. In particular this
  does not replace the node's hypothesis by the stronger upstream resolution class.
- `CochainComplex.IsKInjective` is Mathlib's exact null-homotopy definition: every
  map from an acyclic complex admits a homotopy to zero. Its existing equivalence
  `isKInjective_iff_rightOrthogonal` identifies it with the full right orthogonal.
- `HomotopyCategory.KInjectives C` is the upstream full subcategory
  `(subcategoryAcyclic C).rightOrthogonal.FullSubcategory`. Thus the first conjunct,
  `(subcategoryAcyclic C).rightOrthogonal.IsTriangulated`, gives stability under every
  integer shift and under cones; the second conjunct gives its inherited triangulation.
  Mathlib obtains cone closure as IsTriangulatedClosed₃ by rotating triangles.
- `ι.IsTriangulated` is exactness of the actual upstream inclusion, with the inherited
  shifts supplied by `inclusionCommShift`. `Qh.IsEquivalence ∧ Qh.IsTriangulated`
  says localization restricts to a triangulated equivalence, with its canonical composite
  shift comparison supplied by `localizationCommShift`.
- Every chosen quasi-inverse is quantified as
  `G : DerivedCategory C ⥤ KInjectives C`, together with natural isomorphisms
  `η : 𝟭 _ ≅ Qh ⋙ G` and `ε : G ⋙ Qh ≅ 𝟭 _`. These are exactly quasi-inverse
  data; requiring the triangle identities is unnecessary for the underlying inverse
  functor, since equivalence data can always be adjusted to satisfy them.
- The existential `S : G.CommShift ℤ` supplies coherent comparisons for ALL integer
  shifts, including zero and addition coherence, rather than only a degree-one map.
  The explicit instance lambda uses this very S for `G.IsTriangulated` and for both
  composite assertions. Hence replacement `R = G ⋙ ι` is exact with its composite
  comparisons, and `R.op` is exact with the induced opposite comparisons.
- `open scoped CategoryTheory.Pretriangulated.Opposite` selects the Mathlib opposite
  shift by minus the integer and its reversed distinguished triangles. The assertion
  about `R.op` therefore uses exactly the node's opposite conventions.
- For the final upstream specialization take G to be `Qh.inv`, η and ε from
  `Qh.asEquivalence`. These are precisely the inverse and inclusion appearing at
  BifunctorHom.lean:94–98 before the Hom-complex factor and leftOp. The universal
  conclusion applies directly, so a duplicate specialized theorem is unnecessary.
  No claim concerning exactness of an internal-Hom bifunctor is included.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian` (def-sp-abelian).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Qh` (def-weil-abstract-derived-category).
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated` and `.Functor`:
  `Pretriangulated`, `IsTriangulated`, `Functor.IsTriangulated`, and `Functor.CommShift`
  (def-weil-triangulated-category). These are publicly exposed by the two public imports.
- `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives`:
  `HomotopyCategory.KInjectives`, its `ι`, and its `Qh`, with their full definitions read.
  The existing Qh equivalence instance assumes mono resolutions; the theorem above
  deliberately states equivalence under the node's weaker hypothesis.
- The proof imports retain the node's recorded Mathlib proof dependencies:
  HomotopyCategory.Triangulated (cone triangulation), Triangulated.Orthogonal
  (shift-stable right orthogonal), Triangulated.Subcategory (inherited triangulation),
  DerivedCategory.KInjective (`CochainComplex.IsKInjective.Qh_map_bijective`),
  Localization.Predicate (`Localization.essSurj`), Equivalence (`Functor.asEquivalence`),
  Triangulated.Adjunction (`Equivalence.IsTriangulated.mk'`), and the public
  Triangulated.Opposite.Functor (`functor_isTriangulated_op`).

Sources read: Stacks derived.tex, `lemma-K-injective-defined` and
`lemma-enough-K-injectives-implies` (Tags 070Y and 070K), the upstream KInjectives
construction, and `DerivedCategory.bifunctorRHomOfComplex`. Also read the Mathlib
right-orthogonal, subcategory, exact inverse, shift-adjunction and opposite-functor
interfaces cited by the proof. These agree with the node, so no statement correction
or STATEMENT-DISPUTED flag is needed.

Edge cases checked before writing: the zero category and zero complex are allowed;
acyclic K-injectives represent zero up to homotopy, not a prohibited strict-zero choice;
negative shifts and zero shifts are included by CommShift ℤ; unbounded complexes are
used throughout, with no enough-injectives, boundedness, Grothendieck, smallness,
monomorphism or equality-of-universes restriction. The universal inverse clause covers
an arbitrary choice of equivalence, including the upstream choice, rather than just
one fixed replacement construction.

Searches for an existing statement:

- msearch.py, leanfinder: `K injective replacement localization equivalence inverse
  triangulated opposite functor` returned eight generic opposite/triangulated-equivalence
  hits, including `Functor.op_isTriangulated_iff`; none states this K-injective assembly.
- msearch.py, loogle: `Functor.CommShift, Functor.IsTriangulated, KInjectives` returned
  zero hits (unknown unqualified identifier Functor.CommShift). The actual fully
  qualified class signatures were then inspected directly and with a module-mode
  server compiler probe.
- msearch.py, grep: `KInjectives|isKInjective_iff_rightOrthogonal` in Algebra/Homology
  returned three hits in HomotopyCategory/KInjective.lean, supplying the notion and
  right-orthogonal identification but not the replacement result.
- msearch.py, leansearch: `A K-injective replacement functor from the derived category
  to the homotopy category is triangulated` returned eight infrastructure hits, including
  Functor.IsTriangulated, DerivedCategory's triangulated instance, exact Qh and
  Equivalence.IsTriangulated's forward instance; no exact full statement.
- rg on lean/WeilConjectures and lean/Sheaf for
  `KInjectives|kinjectiveReplacement|kinjective_replacement` found the upstream
  definitions and consumers. In particular RightDerivedFunctor.KInjective computes
  derived functors and BifunctorHom constructs RHom, but neither states this result
  with the weak quasi-isomorphism-only hypothesis and all inverse/opposite clauses.
- grep for the node id in lean/WeilConjectures found no occurrence. Searches for
  `replacement_triangulated|inclusionCommShift|localizationCommShift` found no name
  collision in this namespace. The upstream name index also has no existing assembly.

Validation: the delivered module was checked through scompile.py in both sandbox and
library module modes. The initial probe diagnosed that the upstream wrappers do not
inherit shift instances by typeclass unfolding; the real instance constructions repair
that interface without copying any notion. Final compilation and delivery preflight
results are recorded by the delivery tool. Only the theorem's expected sorry is postponed.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
