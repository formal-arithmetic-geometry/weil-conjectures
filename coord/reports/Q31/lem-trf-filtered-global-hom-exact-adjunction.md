## Worker report

This repair addresses all points of return L on immutable head 2217bf1e97c3. The
saved packet first passed the prescribed dry run (798d3f7f97). A mathematical
self-check nevertheless confirmed both reported defects, so the packet is repaired
rather than re-pushed unchanged. The natural-language statement is unchanged.

The item module is `Sheaf.Algebra.Homology.FilteredGlobalHomExactAdjunction`.
`exactFilteredObject` applies `L.mapHomologicalComplex (.up ℤ)` to the underlying
complex and equips it with the image subobjects of the mapped step inclusions.
`exactFilteredComplex` has that object function and the mapped chain maps.
`exactFiltered_inverts` states preservation of graded quasi-isomorphisms and
inversion after target Q. `exactFilteredDerived` is `Localization.lift` of this
functor, and `exactFilteredDerivedQ` is `Localization.fac`, its Q comparison.
There is no LF parameter and hence no zero-functor substitution unrelated to L.
The helpers are parts of the termwise functor explicitly introduced in paragraph 2
of the item's statement, and carry its blueprint tag, source place and proof plan.
The selected `exactFilteredGrIso` comes from an exists-unique theorem fixing its
quotient-projection square; it is determined data, not a choice of an unspecified map.

Every hypothesis of the node has the following rendering:

* A and B have independently bound object universes u₁, u₂ and morphism universes
  v₁, v₂, with `[Abelian A]`, `[Abelian B]` and `[EnoughInjectives A/B]`.
* L is additive and exact: `[L.Additive]`, `[PreservesFiniteLimits L]` and
  `[PreservesFiniteColimits L]`. R is additive and `(adj : L ⊣ R)` is the original
  adjunction.
* The derived-unit hypothesis is `[IsIso adj.derivedPlus.unit]`. The published
  `Adjunction.derivedPlus` is the canonical bounded-below derived adjunction of
  this very adjunction (upstream module `RightDerivedFunctor.PlusAdjunction`).
  Reading the current server source shows that the return's suggested spelling
  `adj.derivedAdjunctionPlus` lives in a section requiring a monoidal category,
  functorial flat resolutions, K-injective resolutions and additional tensor
  hypotheses. Those are absent from this node. The same upstream file proves
  `derivedAdjunctionPlus_eq_derivedPlus` under those extra assumptions, so the
  direct construction states exactly the requested hypothesis without adding any.
  The arbitrary `derivedAdj` binder is removed; adj is now used by the hypothesis.
* `Complex A true`, `quasiIso true` and `Derived true` are the dependency's actual
  bounded complexes, uniformly finite filtrations and graded localization. They
  retain the exact `DegreeBound` and `filtration.IsFinite` predicates. The output
  calculus C uses the false flag, meaning bounded below.
* A common Ab universe is `max (max u₁ v₁) (max u₂ v₂)`. The dependency interface
  repair below permits the same coefficient target for GA and GB. No equality
  between either pair of object/morphism universes or between A and B is imposed.

Every conclusion clause has the following rendering:

* `c` is the filtered Hom isomorphism for every bounded filtered P,Q, using the
  constructed `exactFilteredDerived L true` on the target side.
  `natural_source` and `natural_target` give naturality in both variables.
* `omega` and `gr` compare the constructed L^F with L.mapDerivedCategory after
  forgetting or grading. Their normalization fields fix the components on Q of
  every filtered complex through `exactFilteredDerivedQ`, the calculus comparison
  isomorphisms, `L.mapDerivedCategoryFactors`, and (for grading) the canonical
  `exactFilteredGrIso`. These are not arbitrary comparison identifications.
* `ordinary` and `underlying` give the underlying derived Hom comparison and its
  square. The new `ordinary_cohomology` fixes this map on every H^n and every
  element: under `GA.cohomology` and `GB.cohomology` it is
  `L.mapDerivedCategory.map` on derived morphisms, transported through `omega`,
  `omegaBoundedComparison` and the canonical commShiftIso. This repairs F1.
* `gradedTerm_cohomology` imposes the identical characterization for every pair
  of grades a and a+r, using `gr` and `grBoundedComparison`. `gradedSum` fixes
  every projection of its map to be that component; `graded` identifies it with
  gr^r(c). Finite support and the bilimit bicone are supplied by the calculus.
  Thus q-p=r is rendered by p=a and q=a+r for all integers. This repairs F2.
* `morphism` identifies the induced H^0(omega high 0) map, through the two
  `homEquiv`s, with the map of the constructed L^F on filtered morphisms.
* `forgetful_and_grade_zero` is the pair of commuting squares with the canonical
  `C.inclusion 0` and `C.gradeProjection`. Applying H^0 gives the two maps in the
  node. No filtration or cochain degree is restricted to positive integers.

The theorem docstring now explicitly names Source: Varshavsky, §5.1.5 and
§§5.1.1–5.1.2. It includes the five proof steps: filtered-injective resolution,
preservation of injectives by R, the graded derived-unit argument, termwise
filtered Hom adjunction, descent and all ordinary/graded/H^0 projection checks.
Every new helper theorem has its own named statement and source/proof docstring;
all postponed proofs are `sorry`. Every definition has actual data.

Dependency declarations read and used:

* `def-sp-abelian`: Mathlib `CategoryTheory.Abelian`.
* `def-sp-injective-resolutions`: Mathlib `Injective`, `EnoughInjectives`,
  `InjectiveResolution` from the injective basic/resolution modules.
* `def-weil-abstract-derived-category`: Mathlib `HasDerivedCategory`,
  `DerivedCategory`, Q, homologyFunctor and the exact functor mapDerivedCategory.
* `def-sp-filtration`: upstream `DecreasingFiltration`, `FilteredObject`, with
  the existing `Sheaf.CategoryTheory.Filtration` step/category compatibility.
* `def-sp-filtered-complex-subquotients`: the existing complexQuotientπ and
  gradedPiece through `Sheaf.Algebra.Homology.FilteredComplexSubquotients`.
* `lem-trf-filtered-derived-hom-calculus`: original `Complex`, `DegreeBound`,
  `quasiIso`, `Derived`, `Q`, `TriangulatedLocalization`, `TruncationCalculus`
  and the universe-generalized `GlobalHomCalculusIn` in the dependency repair.

Edge cases checked: zero objects, zero categories, the zero functor when L itself
is zero, arbitrary negative n and filtration indices, empty graded support, and
one-step filtrations. In the identity-adjunction case L^F is constrained by
termwise identity plus the Q comparison; the unrelated zero-functor counterexample
from the return is no longer admitted. Distinct site object and morphism universes
and distinct A/B universes remain independent; the sole shared universe is the
common larger category of coefficient abelian groups. This covers the étale versus
pro-étale module-sheaf use in the citer `lem-trf-filtered-operations-hom`; its node
was reread and is unchanged.

Searches retained from the saved packet: leanfinder for filtered derived global Hom
exact adjunction (eight ordinary derived functor hits, no exact filtered statement),
loogle for adjunction/mapDerivedCategoryPlus (no such Loogle identifier), Mathlib
CategoryTheory grep for the item/helper names (zero hits), and rg over
WeilConjectures and project Sheaf for the filtered Hom comparison (only the recorded
calculus, no existing exact comparison). Further leanfinder query in this repair:
"Exact additive functor maps finite filtered complexes termwise to their filtered
derived localization and preserves graded pieces" returned eight ordinary
mapDerivedCategory/Ext declarations, none constructing the filtered functor.
Direct rg source searches found the localization lift/fac API, the ordinary
mapDerivedCategoryFactors API, and the canonical derivedPlus construction.
Varshavsky §§5.1.1, 5.1.2 and 5.1.5 were read from the supplied PDF; §5.1.5 supplies
the Hom/H^0 and graded-morphism projection interfaces.

## Dependency modules

`lem-trf-filtered-derived-hom-calculus` gains the module
`Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse` as a §1(B) repair.
Its old `GlobalHomCalculus` hard-codes Ab.{max u v} separately for each source
category, so the two inputs in the item cannot share C in different universes.
`GlobalHomCalculusIn` generalizes just the coefficient universe, to max s (max u v).
It uses the existing bounded/plus localizations and TruncationCalculus unchanged,
and all the original ordinary-model, cohomology, naturality, graded bicone,
finite-support, filtered-Hom and Hom/H^0 compatibility fields. The ordinary model
uses `uliftFunctor.{max s u, v}`. `DerivedHomCalculusIn` and
`filteredDerivedHomCalculusIn` state the same existence theorem in that larger
universe with the original seven-step source proof. The node copy changes only
lean and explains the unusable universe restriction in lean.note.

## Self-check by Q31

The return's F1/F2 were checked by tracing both cohomology equations from a source
H^n element through GA.cohomology to L.mapDerivedCategory.map and back to the
specified target via the representative-normalized omega or gr comparison. The
record still asserts a map of the actual derived Hom objects, not merely maps of
cohomology groups. The constructed LF is used throughout c, both naturality
conditions and the filtered-morphism clause. The extra universe parameter changes
only coefficient size, with no change to the source-defined finite filtrations,
boundedness predicates or localization classes. No independent second reader was
started; the maintainer performs independent review.

Validation: both delivered files compile cleanly through `scompile.py Q31
lem-trf-filtered-global-hom-exact-adjunction` with the dependency module first.
The final library checks report 17.8 s for FilteredDerivedHomCalculusUniverse and
27.8 s for FilteredGlobalHomExactAdjunction, with no errors or warnings. The
coefficient-universe repair, canonical derived-unit hypothesis, representative
normalizations, both cohomology characterizations, and all other comparison clauses
were included in this compile. JSON self-check confirms that each node differs
from the read-only repository only in lean, each lean.statement is verbatim,
and both Lean files have no line over 100 characters.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
