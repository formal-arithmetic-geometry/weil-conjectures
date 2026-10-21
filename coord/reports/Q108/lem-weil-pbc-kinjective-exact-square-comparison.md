## Worker report

Item: lem-weil-pbc-kinjective-exact-square-comparison. The module
`Sheaf.CategoryTheory.KInjectiveExactSquareComparison` states
`CategoryTheory.KInjectiveExactSquare.existsUnique_normalized`, with its proof `sorry`.
The four helper definitions `sourceIso`, `leftUnit`, `rightUnit`, `delta` have real data.
No node statement, dependency, proof, or other pre-existing field was changed.
No new nodes, dependency repairs, or statement corrections are needed.

Source read: literature/stacks-project/derived.tex, lemma-K-injective (Tag 070I),
lemma-K-injective-defined (070Y), lemma-enough-K-injectives-implies (070K), and all
six proof steps in the item. In particular the source permits arbitrary
quasi-isomorphisms to K-injectives; no monomorphism is assumed here.

Hypothesis-by-hypothesis correspondence:

- The four abelian categories are `A'`, `A`, `B'`, `B`, each with its own `Category`
  and `Abelian` instances. Their object, morphism and localization morphism universes
  are independent: `uA' uA uB' uB`, `vA' vA vB' vB`, `wA' wA wB' wB`.
- The unbounded derived categories and localization functors are Mathlib's
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Qh`. A complex J appears
  as `(HomotopyCategory.quotient A' (.up ℤ)).obj J`; its Qh image is canonically
  isomorphic to `DerivedCategory.Q.obj J` by `DerivedCategory.quotientCompQhIso`.
  Thus the homotopy-category presentation does not change the node's QJ or omit
  complexes; it matches the recorded right-derived dependency's unit signature.
- Enough K-injectives for both A' and A are `enough'` and `enough`: every integer-indexed
  cochain complex has an actual map to a K-injective complex which is a `QuasiIso`.
  K-injectivity is the existing `CochainComplex.IsKInjective`, whose signature and
  docstring were read; it says every map from an acyclic complex is null-homotopic.
- H' and H are the functors `H'` and `H` with `Additive` instances. Neither is
  required to preserve limits, colimits or injective objects.
- r and s have `Additive`, `PreservesFiniteLimits`, `PreservesFiniteColimits` instances,
  exactly the existing exact-functor interface. The strict commuting square on
  objects and maps is functor equality `h : H' ⋙ s = r ⋙ H`.
- `preserves` says that termwise `r.mapHomologicalComplex (.up ℤ)` carries every
  K-injective complex to a K-injective complex.
- RH', RH and units η', η are arbitrary fixed pairs, not replacements by a selected
  resolution functor. `universal'` and `universal` express precisely the bijection on
  natural transformations in def-sfb-right-derived-functor (same formula as
  `rightDerivedFunctorOfQuasiIsoResolutions_universal`). No invertibility assumption
  on unit components is added; that invertibility is part of the conclusion.
- The functors named A and B in the node are respectively `RH' ⋙ s.mapDerivedCategory`
  and `r.mapDerivedCategory ⋙ RH`. Lean functor composition follows application order.

Clause-by-clause correspondence:

- `sourceIso` is the canonical identification Hr ≅ sH' on homotopy categories.
  It is the composite of `mapHomotopyCategoryCompIso (Iso.refl (r ⋙ H))` and the
  inverse of `mapHomotopyCategoryCompIso (eqToIso h)`, not an arbitrary square map.
- `leftUnit` is a_J: Qh of the strict-square identification, followed by
  `s.mapDerivedCategoryFactorsh.inv` at H'J, followed by D(s)(η'_J).
  Its source is Q(HrJ) and its target is A(QJ).
- `rightUnit` is b_J: η at rJ followed by RH of
  `r.mapDerivedCategoryFactorsh.inv` at J. Its source is the identical Q(HrJ)
  and its target is B(QJ). These are the fully typed arrows of proof step 1.
- The existential proof witnesses `ha` and `_hb` assert a_J and b_J are isomorphisms
  for every K-injective J. They add no hypothesis to the theorem.
- `delta` is literally `inv (leftUnit ...) ≫ rightUnit ...`, the node's b a⁻¹.
  Its explicit proof argument is supplied by the conclusion witness `ha`.
- The existential β is a natural isomorphism A ≅ B. The first conjunct is exactly
  `leftUnit ... J ≫ β.hom.app (Qh.obj (quotient.obj J)) = rightUnit ... J`, the
  normalized equation after the canonical localization identifications.
- The second conjunct quantifies over every other natural isomorphism γ and requires
  only the normalization at K-injectives to conclude γ = β. Uniqueness is not
  conditioned on its formula, naturality of delta, or normalization on all complexes.
- The third conjunct quantifies over J,J' K-injective and every homotopy-category
  morphism between them. It states `A(Qh f) ≫ delta J' = delta J ≫ B(Qh f)`.
  This includes all homotopy classes, not just chosen resolution maps or chain maps.
- The fourth conjunct quantifies over every derived M, every K-injective J, and every
  isomorphism u : M ≅ QJ. It gives `β_M = A(u.hom) ≫ delta J ≫ B(u.inv)`, exactly
  B(u)⁻¹ delta(J) A(u) in the node's composition convention.
- The last conjunct equates the formula for any two isomorphisms u and v into
  arbitrary K-injective J,J'. This explicitly states independence of both choices.
- There is no boundedness, adjunction, tower, monomorphic-resolution or Grothendieck
  hypothesis in the statement.

Dependency declarations used, with full source signatures/docstrings read:

- def-sp-abelian: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (via its mathlib_match).
- def-weil-abstract-derived-category: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`, `DerivedCategory.quotientCompQhIso`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- def-sfb-right-derived-functor:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit,
  `_universal`, `_unique`, `rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso`,
  and `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`, in
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
  The theorem quantifies over the universal pairs described by this interface;
  its two bijections are expanded so the result applies to any fixed such pairs.
- lem-weil-pbc-exact-functor-derived-factorization:
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  `mapDerivedCategoryFactorsh` in `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
  The last is the canonical homotopy-category form of the same factors.
- Proof dependency lem-weil-pbc-kinjective-hom-derived:
  `CochainComplex.IsKInjective.Qh_map_bijective` in
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`, imported non-publicly.
  The proof plan uses it at step 3; no proof import is omitted for a cycle.
- Existing auxiliary operations: `CochainComplex.IsKInjective` in
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` and
  `Functor.mapHomotopyCategoryCompIso` in `Mathlib.Algebra.Homology.HomotopyCategory`.

Edge cases checked before writing:

- Zero complexes and zero functors are included; the conclusion asserts invertibility
  of arrows between the zero derived objects, as expected.
- Identity vertical functors with identical fixed derived pairs recover the identity
  comparison by normalization and uniqueness. Distinct universal choices are still allowed.
- Arbitrary unbounded complexes and nonmonomorphic quasi-isomorphisms remain allowed.
- Arbitrary homotopy classes f and arbitrary isomorphisms u,v remain quantified;
  there is no restriction to the chosen replacements or their special morphisms.
- Four independent category sizes and four independent localization sizes were preserved;
  compiling did not force equalities between them.
- Strict equality h is used to build its canonical identification. It has not been
  replaced by an unconstrained map or by an additional comparison-isomorphism hypothesis.

Searches (prescribed msearch.py Q108 item wrapper unless a path is given):

- leanfinder, “An exact commuting square of additive functors preserving K-injective
  complexes induces a unique normalized natural isomorphism of total right derived
  functors”: 8 hits, including mapDerivedCategoryFactorsh_hom_app,
  mapDerivedCategoryFactorsh, mapDerivedCategoryFactors, localization factor variants
  and a derivability-structure Guitart exactness result. None is this normalized descent.
- loogle, `CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison`: 6 hits,
  comparison, isIso, and factor equations. The full source assumes the source composite
  is already a right-derived pair; it does not establish it from this node's hypotheses.
- grep, `rightDerivedFunctorComparison|rightDerivedUnique`, Mathlib/CategoryTheory:
  7 hits in Derived/RightDerived, Derived/PointwiseRightDerived and the localizer
  comparison file. `rightDerivedUnique` assumes both universal pairs for one source;
  deriving the square composite is the content to be stated, not an available match.
- leansearch, “Existence and uniqueness of a normalized derived comparison isomorphism
  for an exact commuting square preserving K-injective complexes”: 8 hits, concerning
  ordinary injective resolutions, Q inverting quasi-isomorphisms, and K-injectivity
  invariant under isomorphisms. No exact matching statement.
- rg in lean/WeilConjectures and lean/Sheaf for
  `kinjective-exact-square-comparison`, `KInjective.*[Ss]quare`,
  `kinjective.*[Ss]quare`, and right-derived square variants: no matching declaration.
  The private `rightDerivedSquare` of ExactEquivalenceDerivedSquares assumes vertical
  equivalences and gives a different interface; exact-square composition helpers also
  do not give this result. The selected namespace was absent from Mathlib, both project
  roots and dag/lean_names_upstream.json.

Validation: scompile.py compiled both the sandbox view and the actual module successfully,
26.8 s and 16.6 s respectively. No errors or warnings. The first attempt found a field
notation issue for the reducible CochainComplex abbreviation; this was repaired by the
fully qualified `CochainComplex.IsKInjective` in `preserves`, with unchanged mathematics.
Every universe and variable is explicitly bound; autoImplicit is disabled. All lines
are at most 100 characters. The only postponed theorem is existsUnique_normalized.
No STATEMENT-DISPUTED flag or unresolved node fault.

## Second reading by Q108

This is an in-session second pass; no separate agent was started, as required by the
worker brief. The maintainer performs the independent delivery review.

Reopened the node and final Lean together. Checked the strict-square orientation:
sourceIso runs Hr to sH', so leftUnit and rightUnit share Q(HrJ). Checked both
localization factors are inverses, and RH is applied to the r factor on the right.
Checked delta is a⁻¹ followed by b, naturality is A(f) followed by delta versus delta
followed by B(f), and the formula uses u.hom for A and u.inv for B. These agree with
all six proof steps after translating categorical composition order.

Checked that uniqueness quantifies over gamma with normalization alone. Checked ha
and hb are conclusions, not new assumptions; universal and universal' quantify over
all functors G and use exactly the dependency's natural-transformation bijection.
Checked that enough-injectives assumptions use arbitrary quasi-isomorphisms in the
correct direction and that preserves requires only r, not H or H'. Checked the final
independence equality allows both a different resolution object and a different
isomorphism. No missing hypothesis, weakened clause, or statement correction was found.
