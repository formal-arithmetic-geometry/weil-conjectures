## Worker report

The delivery states `lem-trf-filtered-bifunctor-graded-comparison` in
`Sheaf.CategoryTheory.FilteredBifunctorGradedComparison`, in namespace
`CategoryTheory.FilteredBifunctor`. It also supplies a §1(B) repair of the canonical truncation interface of
`lem-trf-filtered-unbounded-truncation`, whose Q134 declaration landed during the
interrupted attempt. No node statement or proof is
changed. All postponed theorems have `sorry` proofs; definitions have real data.

Source read: Varshavsky, *Lefschetz–Verdier trace formula*, PDF pp.39–41,
§§5.1.1–5.1.3 and the complete statement and proof of Lemma 5.1.4. In particular,
5.1.3(c) gives the two different interval bounds, 5.1.3(d) the specified `phi`, and
5.1.3(e) requires a supplied lift of a transformation. Lemma 5.1.4(i) uses the cutoff
comparison (5.1); (ii) identifies its transformation square and (iii) detects isomorphisms.

Hypotheses and clauses, matched with Lean:

- Abelian categories A, B, C: explicitly bound `A`, `B`, `C`, `Category` and `Abelian`
  instances. Object, morphism and ordinary-localization universes are explicit and
  independent; none are forced equal. `HasDerivedCategory` supplies each ordinary
  derived category. The fixed filtered localization uses the standard larger path
  universe of `MorphismProperty.Localization`; it is not an abstract substitute.
- Uniformly finite decreasing subcomplex filtrations and graded quasi-isomorphism
  localization: `UniformFiltered.Complexes` and `.Derived` are abbreviations for the
  existing `UniformFilteredComplexes A none (fun _ ↦ True)` and
  `UniformFilteredDerived A none (fun _ ↦ True)`. The condition is finiteness in
  the abelian category of entire cochain complexes, hence bounds are independent
  of cochain degree. There is no cochain boundedness condition.
- The canonical forgetful and grade functors are `UniformFiltered.Model.omega` and
  `.gr`, with `omegaComparison`/`grComparison` identifying them on representatives
  with the actual forgetting and graded-complex functors followed by `DerivedCategory.Q`.
- Full triangulated domains: `Domain A E D` has full faithful exact embeddings
  `ordinaryIncl : E ⥤ DerivedCategory A` and
  `filteredIncl : D ⥤ UniformFiltered.Derived A`, with their own triangulated data.
  Its `omega`/`gr` come with natural identifications `omegaImage`/`grImage` under
  those embeddings. `high_closed` and `low_closed` are essential-image closure
  under the actual ambient truncations. Iterating them includes pure pieces.
  `pureNormalization` fixes the pure comparison by the ambient canonical one.
  The real definition `unrestrictedDomain` uses identity embeddings, so the full
  unbounded categories are expressly included rather than replaced by special domains.
- A triangulated bifunctor and filtered lift: `CovariantLift` has
  `ordinary : EA × EB ⥤ EC`, `filtered : DA × DB ⥤ DC`, shift compatibility and
  `IsTriangulated` for each partial functor. `ContravariantLift` uses `EAᵒᵖ` and
  `DAᵒᵖ` in the first slot, with Mathlib's opposite triangulation.
- The given forgetful isomorphism is the `phi` field, a natural isomorphism
  `filtered ⋙ PC.omega ≅ PA.omega.prod PB.omega ⋙ ordinary`, with `.op` in the
  first component contravariantly. This is data of the lift, not a new hypothesis
  that every ordinary bifunctor can be lifted.
- Filtration interval bounds are `interval`, quantified over every four integers
  and all input objects. Vanishing of the input grades outside `[a,b]`, `[c,d]`
  implies vanishing outside `[a+c,b+d]`, or `[-b+c,-a+d]` in the opposite case.
  Support is vanishing in the derived category, not vanishing of the literal
  graded complex. No strict cochain representative is imposed on the inputs.
- Both theorem statements first assert that every input has finite grade support.
  `SupportedOn`, `covariantSupport` and `contravariantSupport` express that support.
  The opposite-case support variable j indexes `gr (-j)`, as in the source.
- `Diagonal i s t` is the subtype of the finite product `s ×ˢ t` satisfying
  `j+k=i`. `covariantSummand` and `contravariantSummand` apply the ordinary
  bifunctor to the actual grades; the latter uses `(PA.gr (-j)).op`.
  `covariantSum`/`contravariantSum` take their finite biproduct in the functor
  category. Mathlib's pointwise finite products and preadditivity supply this
  biproduct; no arbitrary sum object is introduced.
- The existential `theta` is a family of natural isomorphisms on each full domain
  of supported pairs. This expresses naturality in both inputs. The first
  equation for each variance specifies every component by the actual cutoff
  maps, the inverse of the pure-to-cut isomorphism `e`, the canonical pure-output
  identification, `F.phi`, and the canonical pure-input grade identifications.
  `LowCut` normalizes its quotient/inclusion under the faithful embedding;
  `HighCut` normalizes the reversed first-variable inclusion/quotient. Their
  `pureToGrade` definitions are explicit composites, not arbitrary isomorphisms.
  The equation is quantified over all representatives of these canonical cuts
  and all `e` with the specified pure-to-cut hom. The exactness and interval
  hypotheses imply these homs are invertible, as the docstring explains.
- The next equation is the pure-pair normalization: its unique possibly nonzero
  component is precisely `pureComparison ≫ phi ≫ ordinary.map` of the two
  inverse pure identifications. Contravariantly the first factor is `hom.op`.
- The following component equation compares any two finite support choices,
  transporting only object/index equalities by `eqToHom`. Thus the finite sum
  presentation does not change the comparison when zero summands are added.
  Combined with the natural isomorphism on each supported domain, this gives
  the source's functorial finite sum on all pairs.
- The supplied ordinary transformation `H` and filtered transformation `HF` are
  both explicit binders. `covariantLiftsTransformation` and its opposite version
  are exactly the natural forgetful square from 5.1.3(e). The conclusion is the
  equality of natural transformations with `biproduct.map` of the gradewise H
  maps, followed by `IsIso H → IsIso HF`. There is no existence assertion for HF.
- Bounded and one-sided cochain categories are instances of the same full-domain
  assertion. The landed `uniformFiltered_bounded_localization_comparison`
  supplies their fully faithful embeddings and essential images. Their cochain
  bounds are preserved by filtration subcomplexes and quotients. Arbitrary full
  triangulated domains are covered under exactly the stated closure/range data;
  the proof induction is on filtration width, never on cochain degree.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian` (definition node
  `def-sp-abelian`, a Mathlib leaf).
- `WeilConjectures.CategoryTheory.Abelian.Filtration`:
  `CategoryTheory.DecreasingFiltration` with `F`, `F_succ_le`, and `gr`. Its
  current source was read through `scompile.py --source`, because the old local
  checkout lacks this newer module. `Sheaf.CategoryTheory.Filtration` supplies
  compatibility accessors for this same upstream filtration, not a second notion.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `DecreasingFiltration.complexStep`, `.complexQuotient`, `.complexQuotientπ`,
  `.complexCycleRepresentatives`, `.complexCycles`, `.complexBoundaries`; its
  grade is the same cokernel quotient used by the existing graded-map API.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, including its localization instance.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`, `.Functor`:
  `Pretriangulated`, `IsTriangulated`, `Functor.CommShift`, `Functor.IsTriangulated`.
- `Sheaf.Algebra.Homology.UniformFiniteFilteredLocalization`:
  `uniformFilteredProperty`, `UniformFilteredComplexes`, `uniformFilteredQuasiIso`,
  `UniformFilteredDerived`, and `uniformFilteredComparison`.
- `Sheaf.Algebra.Homology.FilteredDerivedHomCalculus`:
  `CochainComplex.FiniteFiltered.highObject`, `.lowObject`, `.truncation_maps`.
  These are actual subcomplex and quotient objects; the older derived calculus
  is bounded below and is not silently treated as the needed unbounded calculus.
- The delivery's `Sheaf.Algebra.Homology.UniformFilteredTruncation`:
  `UniformFiltered.Model`, `.unbounded_truncation`, and all its named helpers.
- `Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison`:
  `CategoryTheory.uniformFiltered_bounded_localization_comparison`, imported for
  the bounded/one-sided proof step. The zero-cone, two-of-three and finite-sum
  triangle proof dependencies are the Mathlib declarations recorded in their
  nodes, imported through the triangulated modules. The prerequisite additionally
  imports its recorded triangle-morphism-extension and cone-acyclic modules.

Edge cases checked: zero inputs; either finite support empty; empty diagonal even
with nonempty supports; a single pure grade; grade indices negative or zero;
intervals with endpoints reversed (which force zero objects); finite supports
containing extra zero grades; acyclic nonzero graded complexes outside an interval;
unbounded cochain complexes with uniformly finite filtration; both mixed one-sided
and bounded full domains; independent sizes of the three abelian categories and
full domains. In the pure contravariant case p=-j and the output grade is -p+k=i.
The formula uses `.inv.op` in the general pure-input identification and `.hom.op`
in the pure-pair normalization, with their directions checked separately.

Searches: the retained `searches.jsonl` records actual LeanFinder, Loogle, grep,
and LeanSearch searches from the earlier attempt. I repeated the three main
searches through msearch.py: LeanFinder query “An exact finite filtered derived
bifunctor has associated graded the finite convolution of its ordinary bifunctor,
compatibly with natural transformations” returned eight graded-object associator
and trifunctor hits; Loogle `CategoryTheory.GradedObject.mapBifunctor` returned
12 graded-object declarations; grep `filtered.*bifunctor|bifunctor.*filtered|UniformFiltered.Model`
returned one unrelated filtered-colimit presheaf hit. Read Mathlib
`GradedObject/Bifunctor.lean` lines 33–158: these construct a convolution of graded
objects, without comparing it with a lift on filtered derived categories. Direct
rg searches of upstream WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
for filtered bifunctors, `UniformFiltered.Model`, `CovariantLift`, and the item id
found no existing statement or interface. The filtered localization and complex
truncation helpers already exist and are reused rather than recreated.

The retained work needed repairs: qualify `Functor.whiskerRight` in the prerequisite;
replace a poorly inferred equality on nested products by the explicitly typed
`congrArg₂` in both support-independence clauses; add canonical cutoff component
formulas so the comparison is specified for general inputs; restore node records
and this report, which had not been written by the interrupted attempt.

## Dependency modules

`lem-trf-filtered-unbounded-truncation` now records Q134's
`Sheaf.Algebra.Homology.FilteredUnboundedTruncation`, declaration
`CochainComplex.FiniteFiltered.Unbounded.filteredUnboundedTruncation`. I read its
complete source on resumption, including `TriangulatedLocalization`,
`TruncationCalculus` and `Calculus`. Its `pureComparison` is an isomorphism
`T_p ⋙ omega ≅ gr p`, and `pureIdentity` independently identifies `T_p` with the
identity on the pure domain. Neither is normalized against the representative
forgetful/grade comparisons. For example, composing `pureIdentity` with minus the
identity on the pure domain changes the induced `gr p ≅ omega` while preserving
all fields of that interface. Thus importing that record alone does not specify
the canonical pure isomorphism required by the component formula (5.1).

The retained `Sheaf.Algebra.Homology.UniformFilteredTruncation` supplies the same
prerequisite under §1(B), now with that precise reason in `lean.note`. Its
`Model.pureNaturality` and `pureNormalization` fix the pure comparison on actual
strictly pure representatives. Its `high_grade_normalization` and
`low_grade_normalization` identify the grade maps with the actual inclusion and
quotient. These conditions provide the canonical identifications used in the
item, rather than additional hypotheses on its bifunctor. The category remains
the already landed `UniformFilteredDerived` localization used by the bounded
comparison; no replacement category or cochain bound is introduced. This is a
repair of the recorded prerequisite's interface, not a claim that its theorem is
false. No data is selected from either unproved `Nonempty` theorem.

The auxiliary theorem `truncation_bounds` renders preservation of uniform
filtration finiteness; `highRepresentative`, `lowRepresentative`, `highInclusion`
and `lowProjection` have actual subobject/cokernel data. `Model` supplies exact
forgetting/grading, representative-normalized truncations and their natural
triangle, uniqueness with identity middle component, the canonical Hom bijections,
and the normalized pure-grade equivalence. Every helper is listed in
`lean.declarations` and sourced to this prerequisite. The dependency node changes
only in `lean`. Its source already records the reversal of adjoint directions in
Varshavsky 5.1.1(c); the Hom bijections use the corrected directions.

All other recorded dependency declarations remain usable and are reused. There
are no new DAG nodes and no node statement correction.

## Second reading by Q133

This is the worker's second pass, not an independent reviewer signature; the
maintainer supplies the independent reading for this direct dispatcher delivery.
I reread the source pp.39–41, both node statements, and the complete two Lean files.
The two interval calculations and opposite signs agree with 5.1.3(c). The first
canonical component formula now matches (5.1) on all pairs, and the pure formula
reduces it to the given phi with the correct reversed first-variable arrow.
The support-independence equation compares the same pair and the same diagonal
index in two finite presentations. The transformation equation requires the given
forgetful square, and the isomorphism implication concerns that same HF. None of
these clauses asserts an arbitrary lift. Full-domain closure includes both cuts
used in the proof, so no extra cochain boundedness enters. The prerequisite uses
the real finite subcomplex filtration and the same localization as the existing
bounded-comparison node; its natural pure identity has no nonexistent direct
pure-to-original map. I found and repaired the missing canonical component
characterization and the equality elaboration defect described above. Final
validation is by scompile.py and deliver2.py, with every delivered file compiled
separately in dependency order.

Validation: scompile.py compiled both delivered modules separately in dependency
order, including their canonical library paths, with exit status 0 and no warnings
or errors. The delivery dry run repeats these checks before server preflight.

Resumption self-check: the first saved `lean.statement` stopped at the `:=` in
`(PA := PA)`. It now contains the entire covariant theorem signature, ending at
the actual proof boundary `:= by`; the extraction script uses that boundary too.
The newly landed Q134 prerequisite was read and the §1(B) reason above replaces
the stale claim that no declaration existed. Both Lean files are retained.
