## Worker report

Item: `def-sfb-right-derived-exact`. Reuse the existing upstream declaration
`CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`,
lines 97–101 of the read-only source. No module is added. Only the item's `lean`
record is changed. The existing attached declaration list was incomplete as a
stage-2 record; this delivery supplies the module, primary declaration, signature,
branch, author, date and `existing: true`, retaining both comparison declarations.

Source read: the current main-20261015 blueprint file
`blueprint/sec-proetale-coefficients/sk-def-sfb-derived-categories/def-sfb-right-derived-exact.md`,
the full item and its proof, and the full `def-sfb-right-derived-functor` dependency.
No statement correction, new node or dependency module is needed.

Hypotheses and clauses, individually:

- The categories C and D are the arbitrary abelian categories from the dependency:
  `{C : Type uC} {D : Type uD}`, `[Category.{vC} C]`, `[Category.{vD} D]`,
  `[Abelian C]`, `[Abelian D]` in the upstream section. Source and target category
  and morphism universes are independent.
- Their unbounded derived categories are the existing `DerivedCategory C` and
  `DerivedCategory D`, with `[HasDerivedCategory.{wC} C]` and
  `[HasDerivedCategory.{wD} D]`. There is no boundedness assumption.
- The functor is `(F : C ⥤ D)` with `[F.Additive]`, as in the dependency.
- Existence of K-injective resolutions is `[Abelian.HasKInjectiveResolutions C]`.
  Only the source category has this assumption; no such assumption is made on D.
  The upstream class includes a monic quasi-isomorphism to a K-injective complex.
  This is equivalent to the dependency's mere quasi-isomorphism formulation:
  replace any such resolution map by its mapping-cylinder inclusion. The latter
  is degreewise split monic, its target is homotopy equivalent to the original
  K-injective target and hence K-injective, and it remains a quasi-isomorphism.
  Thus this encoding does not impose an additional mathematical hypothesis.
- The added exactness assumption is `[PreservesFiniteLimits F]` and
  `[PreservesFiniteColimits F]`; for additive functors between abelian categories
  this is precisely preservation of short exact sequences.
- RF is the existing `F.rightDerivedFunctor`, defined in the upstream `Defs`
  module as the total right derived functor of
  `F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh`.
- D(F) is Mathlib's existing `F.mapDerivedCategory`, defined in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` by
  `F.mapHomologicalComplexUpToQuasiIso (ComplexShape.up ℤ)`. Its comparison
  `F.mapDerivedCategoryFactors` identifies it with termwise application to
  complexes followed by localization. `mapDerivedCategoryFactorsh` gives the
  corresponding comparison on the homotopy category.
- The conclusion RF ≅ D(F) is literally
  `F.rightDerivedFunctor ≅ F.mapDerivedCategory`.
- Canonicity is the actual definition by `rightDerivedUnique`, comparing the
  universal pair `(F.rightDerivedFunctor, F.rightDerivedFunctorUnit)` with
  `(F.mapDerivedCategory, F.mapDerivedCategoryFactorsh.inv)`.
  The recorded companion
  `CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory_hom_fac`
  asserts that the right-derived unit followed by the whiskered comparison hom
  equals `F.mapDerivedCategoryFactorsh.inv`. It therefore preserves the units,
  rather than selecting an arbitrary isomorphism.

Dependency declarations read in full with docstrings:

- The dependency node `def-sfb-right-derived-functor` has no completed `lean`
  record in the shared DAG snapshot. Its notion nevertheless already has the
  usable upstream declaration `CategoryTheory.Functor.rightDerivedFunctor`
  and its unit `CategoryTheory.Functor.rightDerivedFunctorUnit`, in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`.
  Those are exactly the declarations the existing comparison uses. Their
  definitions, the `IsRightDerivedFunctor` instance, and the isomorphism-on-
  K-injectives instance were read. This delivery does not restate or edit that
  dependency. The item's own existing upstream match needs no new consumer module.
- `CategoryTheory.Functor.mapDerivedCategory` and its two factorization
  isomorphisms are in Mathlib's `Algebra.Homology.DerivedCategory.ExactFunctor`.
- `CategoryTheory.Abelian.HasKInjectiveResolutions` is defined in upstream
  `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives`.

The node's proof is exactly the upstream construction: exactness makes the
termwise functor descend to derived categories; its factorization isomorphism
makes it a right derived functor by `isRightDerivedFunctor_of_inverts`; uniqueness
then gives `rightDerivedUnique`. No new proof or postponed theorem is introduced.

Edge cases checked by inspecting the full signature and construction: zero
complexes, zero functors, the zero abelian category, the identity functor, and
unbounded complexes are included. No nonzero, faithful, injective-target,
bounded-below, degree, characteristic, or equal-universe hypothesis is present.
The mapping-cylinder argument also applies to a zero resolution target.

Searches made with the required wrapper:

- `leanfinder`: "The total right derived functor of an exact additive functor
  between abelian categories is canonically isomorphic to its termwise functor
  on unbounded derived categories". Eight hits, including
  `mapDerivedCategoryFactorsh` and `mapDerivedCategoryFactors`; no Mathlib copy
  of the full upstream comparison.
- `loogle`: `CategoryTheory.Functor.mapDerivedCategory,
  CategoryTheory.Functor.totalRightDerived`. Zero hits.
- `leansearch`: "An exact additive functor induces a functor on derived
  categories canonically isomorphic to its total right derived functor".
  Eight hits including `totalRightDerived`, `mapDerivedCategory` and the
  different ordinary degree-zero `rightDerivedZeroIsoSelf`.
- `grep` in Mathlib `Algebra/Homology/DerivedCategory`:
  `rightDerivedFunctorIsoMapDerivedCategory|mapDerivedCategory.*Iso|totalRightDerived`.
  Five hits, including bounded-below total derivation and the exact-functor
  factorization; no exact unbounded comparison.
- Direct `rg` in upstream's `CategoryTheory/DerivedCategory/RightDerivedFunctor`
  finds the exact comparison and its unit-compatibility lemma in
  `MapDerivedCategory.lean`; the complete module and relevant imports were read.
- Direct `rg` for `def-sfb-right-derived-exact` in upstream finds no blueprint
  tag. The declaration-name search succeeds regardless of the absent tag.
- Direct `rg` for `rightDerivedFunctorIsoMapDerivedCategory` in `lean/Sheaf`
  finds many consumers of this same upstream declaration, including
  `CategoryTheory/DerivedExactMateCompatibility.lean` and
  `AlgebraicGeometry/SingleComplexOpenDirectImageUnit.lean`, and no reason to
  duplicate the notion. The upstream-name JSON has no matching entry.
- `scompile.py --source` confirms the current source of the comparison module
  agrees with the locally read upstream definition and section hypotheses.

Validation: the scratch-only import probe checks both full declaration types and
prints their axioms through the required `scompile.py` wrapper. The delivery
wrapper also checks both existing names, compiles the probe, and runs preflight.
The independent second reading is left for the second reader.

The compiled axiom probes show that each recorded declaration depends only on
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The diagnostic
universe-printing option was removed from the scratch probe after reading the
six independent universes; it is not part of the delivery.

## Second reading by Q20

Independent reading on 2026-10-16. I read the complete node, its current statement
dependency, both blueprint source files, Stacks `derived.tex`
`lemma-right-derived-exact-functor` (all five clauses and its proof), and Tags
070K/070Y (`lemma-enough-K-injectives-implies`, `lemma-K-injective-defined`).
The source assumes abelian categories; neither the unbounded exact-functor
comparison nor 070K imposes boundedness, enough injective objects, a coefficient
ring, or a monomorphic-resolution hypothesis. The node retains its stated
K-injective-resolution hypothesis inherited from its dependency.

Objects, hypotheses, and conclusions, matched individually against the final
module (the list used for the independent reading):

1. Arbitrary abelian categories C and D: `{C : Type uC} {D : Type uD}`,
   `[Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]`. PASS.
2. The unbounded derived categories of these same categories:
   `[HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]` and
   `DerivedCategory C`, `DerivedCategory D` in the recorded dependency.
   I read Mathlib `DerivedCategory.Basic`: HasDerivedCategory chooses the
   localization's morphism universe and always has a standard construction
   at `max u v`; these binders impose no extra mathematical existence
   assumption. PASS, with all six universes independent.
3. Additive functor F from C to D: `(F : C ⥤ D) [F.Additive]`. PASS.
4. Every source complex admits a quasi-isomorphism to a K-injective complex:
   `h : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ)
   (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s`. I read the Mathlib definition
   `CochainComplex.IsKInjective`: every map from an acyclic complex is homotopic
   to zero. There is no monomorphism requirement on s. No resolution assumption
   is made on D. PASS after repair.
5. F is moreover exact: `[PreservesFiniteLimits F] [PreservesFiniteColimits F]`.
   For additive functors between abelian categories these express preservation
   of kernels and cokernels, equivalently short exact sequences. PASS.
6. RF is precisely the dependency's chosen universal pair:
   `F.rightDerivedFunctorOfQuasiIsoResolutions h` and
   `F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h` from the now-landed
   `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`. I read all
   six declarations, including the universal bijection, unit-compatible
   uniqueness, invertibility on K-injectives, and comparison for every chosen
   resolution. PASS after repair; this is not upstream's different choice.
7. D(F) is the functor induced by applying F termwise:
   Mathlib's `F.mapDerivedCategory`, read in full together with
   `mapDerivedCategoryFactors` and `mapDerivedCategoryFactorsh`. Its definition
   is `F.mapHomologicalComplexUpToQuasiIso (ComplexShape.up ℤ)`; the
   factorization isomorphisms identify the action on complexes and their
   homotopy category. PASS; no duplicate termwise functor.
8. The conclusion is an isomorphism RF ≅ D(F):
   `rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory` has result
   `F.rightDerivedFunctorOfQuasiIsoResolutions h ≅ F.mapDerivedCategory`. PASS.
9. The isomorphism is canonical, compatible with the units: its definition
   applies the dependency's `rightDerivedFunctorOfQuasiIsoResolutions_unique`
   to `F.mapDerivedCategory` with unit `F.mapDerivedCategoryFactorsh.inv`.
   Mathlib's `isRightDerivedFunctor_of_inverts` supplies that pair's derived
   universal property; `homEquivOfIsLeftKanExtension` supplies the actual
   bijection. The definition chooses from an `∃!` characterization, not from
   arbitrary existence. The companion `_hom_fac` theorem states the exact
   equality of units. PASS.

Mismatch and repair: the first worker's existing match was read and compiled;
it compares upstream `F.rightDerivedFunctor`, whose signature requires
`HasKInjectiveResolutions C` and thus explicitly monomorphic resolution maps.
During this second reading, the dependency landed with the more general
`rightDerivedFunctorOfQuasiIsoResolutions h`. The original delivery therefore
no longer compared the object recorded by the dependency. A mathematical
mapping-cylinder equivalence of the hypotheses does not make the two chosen
functors definitionally identical or provide their Lean comparison. I replaced
the item's `lean` record and supplied its owning module
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact`, using the
current dependency directly under its exact h. The worker report above is
preserved as the history of the first delivery; its claim that no module is
needed is superseded by this reading. No natural-language statement correction,
new node, private copy, or dependency edit is necessary.

The node's proof is implemented as the construction plan in the definition's
docstring and, step by step, in the sole postponed theorem's docstring:
exactness preserves cohomology/quasi-isomorphisms; termwise F descends with its
factorization isomorphism; the inverse factorization is a right-derived unit;
uniqueness of the dependency's universal pair supplies the comparison preserving
units. The sole new sorry is
`CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory_hom_fac`,
the unit-characterization clause of this same DAG node. The definition contains
real data selected from a uniquely characterized comparison and no sorry.
All declarations have source and blueprint docstrings. All Lean lines have at
most 100 characters, imports are used, and `autoImplicit false` plus the six
explicit universes bind every variable.

Edge cases: zero complexes, zero exact functors, the zero abelian category,
the identity functor, and arbitrary unbounded complexes are included. The h
quantifier includes every complex, including zero, and no chosen resolution
is required to be monic. No degree n, characteristic, index set, or scheme is
introduced: n = 0, empty indices, and empty schemes cannot be excluded by any
additional condition here. Coefficient categories in every characteristic
remain admissible. Arbitrary source and target object, morphism, and derived
morphism universes remain independent; there is no forced equality.

Independent searches used different wording from the first worker:

- `leanfinder`: "An exact functor on abelian categories descends through
  quasi-isomorphisms and agrees with its universal right Kan extension along
  the localization". Eight hits: the termwise factorization isomorphisms,
  `mapDerivedCategory`, localization and Ext functor results; none compares
  the dependency's chosen universal pair.
- `leansearch`: "If a functor already inverts the morphisms of a localization
  then it is its own total right derived functor". Eight hits, including
  `isRightDerivedFunctor_of_inverts` and
  `isRightDerivedFunctor_iff_of_inverts`; I read the former's full signature
  and its use of a pointwise left Kan extension.
- Direct `rg` in Mathlib for `rightDerived.*[Ee]xact`, `[Ee]xact.*rightDerived`
  and `isRightDerivedFunctor_of_inverts` found the ordinary degree-zero
  comparison and generic localization lemmas, not this recorded RF.
- Direct `rg` in upstream and the project's Lean for the comparison,
  `def rightDerivedFunctor`, and `mapDerivedCategoryFactorsh` found the
  specialized upstream comparison and the newly landed dependency. Their
  modules and definitions were read, not inferred from similar names.
- A direct full-name search in Mathlib, upstream, and `lean/Sheaf` for
  `rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory` found no
  existing declaration before adding this owning-node comparison.
- `scompile.py --source` confirmed the upstream comparison's current signature.
  The scratch probe compiled and printed its two original declarations'
  standard axioms only; this does not validate their applicability to the
  changed dependency and is not used to claim the final module is sorry-free.

Validation of the repaired final module and delivery is recorded below.

The final module compiled cleanly through `scompile.py`, including its imported
side-project dependency overlay and the library-path compile. The dry run caught
a record-format mismatch: the preflight records signatures starting at `def`,
excluding the `noncomputable` modifier. I aligned `lean.statement` with that
verbatim signature; the module and mathematical statement are unchanged.

Final dry run: `deliver2.py Q20 def-sfb-right-derived-exact --no-push`
printed OK: the complete delivery passes preflight and compiles. The wrapper
preserved concurrent base additions of `chapter` and `unit`; neither field was
changed by this delivery. Only the item's Lean record, its owning module, and
this report are delivered. No target or natural-language statement was changed.
