## Worker report

The module `Sheaf.Algebra.Homology.FilteredUnboundedTruncation` states
`CochainComplex.FiniteFiltered.Unbounded.filteredUnboundedTruncation`.
Its conclusion is `Nonempty (Calculus A)`: the cone-normalized triangulation and
all functors, comparisons and properties exist together on the actual formal
localization. No construction is selected from this nonunique existence assertion.
Every theorem has proof `sorry`; definitions contain actual objects and maps.
The statement, proof and dependencies of the source node are unchanged.

### Hypotheses and objects

- An arbitrary abelian category is `(A : Type u) [Category.{v} A] [Abelian A]`.
  There is no enough-injectives assumption and no restriction relating `u` and `v`.
- Integer cochain complexes are `CochainComplex A ℤ`.
  `Complex A := FiniteFilteredObjects (CochainComplex A ℤ) none false` uses the
  existing full subcategory. The predicate `IsFinite` applies to the filtration
  of the entire complex: it gives a whole-complex top step and a whole-complex
  zero step. Thus bounds are uniform in cochain degree. `none` imposes no fixed
  interval common to objects, and `false` imposes no injectivity requirement.
  There is no cochain boundedness condition (unlike the imported sibling's
  separate bounded/bounded-below `Complex`).
- `evaluation A none` forgets filtration and `evaluation A (some p)` takes the
  existing graded quotient. `quasiIso A` is exactly the condition that every
  graded map is a `QuasiIso`.
- `Derived A := (quasiIso A).Localization` and `Q A := (quasiIso A).Q` are the
  actual formal localization and its canonical functor. Ordinary derived
  categories use `[HasDerivedCategory.{w} A]` and `DerivedCategory A`; both
  morphism sizes can be read in the common larger universe `max w u v`.
  `HasDerivedCategory.standard` supplies the unrestricted formal size, so the
  chosen-localization binder adds no mathematical smallness assumption.

### Every conclusion

- The induced triangulation is `TriangulatedLocalization A`, containing
  `Preadditive`, `HasZeroObject`, additive integer shifts, `Pretriangulated`
  and `IsTriangulated`. Its `shiftComparison` and `shift_naturality` identify
  those shifts with the actual cochain shifts. Its `cone_normalization` says
  precisely that distinguished triangles are triangles isomorphic to images
  of actual filtered mapping-cone triangles, including the signed third map.
  Thus the assertion is not merely the existence of some triangulation.
- In `TruncationCalculus`, `omega` and `gr p` are the forgetful and graded
  functors to `DerivedCategory A`. `omegaComparison` and `grComparison`
  identify their composites with `Q` with the corresponding actual functors
  on complexes followed by `DerivedCategory.Q`. The `*_shift` and `*_exact`
  fields express their exactness using `CommShift ℤ` and `IsTriangulated`.
- Before localization, `high K r` is the existing `highObject K.obj r`
  (subcomplex with induced filtration), and `low K r` is the existing
  `lowObject K.obj r` (cokernel with quotient/image filtration). The named
  theorem `construction_finite` supplies only their finite-filtration proofs,
  as well as the same proofs for the actual cone and cochain shift.
- The calculus fields `high r` and `low r` are endofunctors on `Derived A`.
  `highComparison` and `lowComparison` identify their values on localized
  complexes with those actual subcomplexes and quotients. `inclusion` and
  `quotient` are natural transformations, normalized by
  `inclusion_normalization` and `quotient_normalization` to the actual inclusion
  `highι` and cokernel projection `lowπ`. `high_naturality` also explicitly
  identifies the underlying localized subcomplex map with the existing
  `FilteredObject.restrictionSteps`. Exactness is recorded by `high_exact`,
  `low_exact` and their shift comparisons.
- `high_gr` identifies `high r ⋙ gr p` naturally with `gr p` when `r ≤ p`;
  `high_gr_zero` gives zero when `p < r`. `low_gr` gives the natural
  identification when `p < r`, and `low_gr_zero` gives zero when `r ≤ p`.
- Support is written directly with these recorded graded functors:
  `∀ p, p < r → IsZero ((gr p).obj L)` for high support, and
  `∀ p, r ≤ p → IsZero ((gr p).obj R)` for low support. This means vanishing
  in the derived category, not literal zero graded complexes.
- `connecting r : low r ⟶ high r ⋙ shiftFunctor _ 1` is natural for every
  localized morphism. With `inclusion` and `quotient`, `distinguished`
  states the required distinguished triangle for every integer and object.
- `unique_triangle` quantifies over every distinguished `Triangle` with
  middle object equal to `M` and the prescribed first/third supports. It gives
  `∃! e` of triangles whose middle component is the identity transported by
  `eqToHom h`. The triangle isomorphism includes the connecting square.
- `high_hom` states bijectivity of `f ↦ f ≫ inclusion.app M` for every
  high-supported `L`. `low_hom` states bijectivity of
  `f ↦ quotient.app M ≫ f` for every low-supported `R`. These are precisely
  the two canonical Hom maps in the node. Naturality follows from composition
  and the fact that inclusion and quotient are natural transformations; their
  inverses are natural because the maps are bijective. Since `high_gr_zero`
  and `low_gr_zero` put the output in the respective full support categories,
  these are the defining Hom universal properties for high being right
  adjoint and low being left adjoint to the respective inclusions.
- Lean composition `low (p+1) ⋙ high p` renders
  `T_p = t_{≥p} t_{<p+1}`. `pure_support` says that every other grade vanishes.
  `pureComparison` is the natural isomorphism `T_p ⋙ omega ≅ gr p`.
- `pureIdentity` is a natural isomorphism between `T_p` and identity after
  restriction along `ObjectProperty.ι` of the full pure-grade subcategory.
  `pureEquivalence` states that forgetting on this entire full subcategory
  is an `IsEquivalence` onto the entire ordinary unbounded derived category.

### Dependency declarations read and used

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`. Read its full class signature:
  preadditive, normal mono/epi, finite products, kernels and cokernels.
- `def-sp-filtration`: the recorded upstream
  `CategoryTheory.DecreasingFiltration` in
  `WeilConjectures.CategoryTheory.Abelian.Filtration`, read with
  `scompile.py --source` because this current module is absent from the older
  source checkout. Its fields are `F` and `F_succ_le`. The existing
  `Sheaf.CategoryTheory.Filtration` compatibility module supplies `step`,
  `gradedPiece`, induced and quotient filtrations, and the category of
  filtration-preserving maps. No filtration is redefined.
- `def-sp-filtered-complex-subquotients`:
  `Sheaf.Algebra.Homology.FilteredComplexSubquotients`, notably
  `CategoryTheory.DecreasingFiltration.complexQuotient`,
  `complexQuotientπ`, and the recorded `complexCycles` and `complexBoundaries`.
  Read the full signatures and docstrings. The present graded complexes use
  the same `gradedPiece`, the cokernel of the successive-step inclusion.
- `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-triangulated-category`: the recorded Mathlib interfaces
  `CategoryTheory.Pretriangulated`, `IsTriangulated`, `HasShift`,
  `Functor.CommShift` and `Functor.IsTriangulated`. These are used rather
  than a replacement set of triangle axioms.
- Existing helper constructions are reused from
  `Sheaf.Algebra.Homology.FiniteFilteredLocalization`:
  `CategoryTheory.FiniteFilteredObjects` and `filteredEvaluation`; and from
  `Sheaf.Algebra.Homology.FilteredDerivedHomCalculus`:
  `CochainComplex.FiniteFiltered.highObject`, `lowObject`, `coneObject`,
  `shiftObject`, `truncation_maps` and `restriction_square`.
  Their signatures and bodies were read. Only their unrestricted filtered
  object constructions are used, not the sibling's bounded theorem or its
  enough-injectives hypothesis. No missing independent notion or unusable
  dependency required a new node or dependency repair.
- Proof imports cover the recorded cone/fraction/localization/triangle route:
  `Localization.CalculusOfFractions`, `Localization.Predicate`,
  `Localization.Triangulated`, `Triangulated.Subcategory`,
  `Homology.HomologySequence`, `HomotopyCategory.Triangulated`,
  `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`, and
  `WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension`.

### Edge cases and source check

Read Varshavsky's PDF, printed pp.39–41, especially 5.1.1(a)–(d) and
5.1.2(a)–(c), and the current blueprint additivity proof of
`lem-trf-trace-triangle-compatibility`. The finite filtration in 5.1.1(a)
is a finite filtration of the entire complex, with no bound on cochain degrees.
For `r` below every grade, high is identity and low is zero; for `r` above
every grade, high is zero and low is identity. At the boundary, grade `r`
belongs to high and grade `r-1` belongs to low. The zero complex and pure
grade complexes are included. Acyclic exterior graded complexes satisfy the
support predicates even when those complexes are nonzero. Arbitrarily
cochain-unbounded complexes with a finite whole-complex filtration are included.
Neither injective objects nor bounded representatives are assumed.

The source's adjoint directions in 5.1.1(c) are reversed as already recorded
by stage 1. The node and Lean use the correct directions, determined by the
canonical inclusion and quotient. For example, a nonzero pure-grade object in
grade `r-1` maps by the underlying identity to the same object purely in
grade `r`; this is filtration preserving. This refutes a *left* adjoint high
cutoff: high of the source is zero, while maps from the source to a high
object need not vanish. The right-adjoint high cutoff has exactly the Hom
bijection stated here. No statement correction or dispute is needed.

`construction_finite`, `structure_maps`, and `filteredUnboundedTruncation`
are the three postponed named theorems belonging to this node. Their complete
natural-language proofs are in their docstrings. Choices in `coneι`, `coneπ`
and `shiftMap` come from `structure_maps`, which fixes the underlying chain
map; filtration-preserving maps are uniquely determined by that map and
proof irrelevance, so no arbitrary data is chosen from a mere existence claim.

### Searches

The sandbox `searches.jsonl` preserves the actual search service outputs:

- `msearch.py ... grep "FilteredDerived|FiniteFiltered|filtration.*truncation"`:
  9 hits, concerning preadditive finite constructions, Grothendieck axioms,
  and ordinary filtered colimit constructions; no matching theorem.
- `msearch.py ... loogle '"filtered", "truncation"'`: 0 hits.
- `msearch.py ... leanfinder "uniformly finite filtered unbounded cochain
  complexes localization filtration truncations exact distinguished triangle"`:
  8 hits, all ordinary derived cohomological bounds, ordinary fraction
  factorization or the ordinary derived t-structure; no matching theorem.
- `msearch.py ... leansearch "finite filtered derived category localization
  exact subcomplex quotient filtration truncation"`: 8 hits, including
  `HasDerivedCategory.standard`, ordinary `DerivedCategory.Q`, and ordinary
  homotopy localization interfaces; no finite-filtered cutoff theorem.
- `rg` on the source project's `WeilConjectures` for
  `FilteredUnbounded|Unbounded.Truncation|lem-trf-filtered-unbounded-truncation|FiniteFiltered`
  returned no hits. The same node/name search on published `lean/Sheaf`
  returned no hits. Broader searches found the bounded/bounded-below helper
  modules above, which were read and reused. They do not assert the present
  cochain-unbounded theorem.

Validation: single-file compilation through `scompile.py` succeeded for both
its sandbox probe and the actual module path, with no errors or warnings.
All variables and universes are explicit (`autoImplicit false`).

## Second reading by Q134

No second worker was started: the current dispatched brief requires direct
worker delivery and the maintainer's independent review. I reread the node
and final file for clause coverage. The compilation repairs grouped the full
subcategory predicate's conjunction correctly, disambiguated the unbounded
calculus from the bounded sibling, and parenthesized the functor-isomorphism
codomains of implication binders. These changed no mathematical statement.
The final module includes the graded formulas, full triangle uniqueness,
the canonical Hom bijections in the correct adjoint directions, and the
pure-grade equivalence; it contains no boundedness or injectivity assumption.
