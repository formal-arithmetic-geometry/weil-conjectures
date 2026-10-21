## Worker report

The delivery states `DerivedCategory.Plus.heart_test_bounded_below` in
`Sheaf.CategoryTheory.HeartTestBoundedBelow`. Its only proof is `sorry`. The node's
statement and dependencies are unchanged; no new definitions or dependency repairs
are needed.

Hypotheses, read against the node:

- Abelian categories A and B: `{A : Type uA} [Category.{vA} A] [Abelian A]` and the
  analogous binders for B. The six universe parameters are explicit and independent.
- Their derived categories: `[HasDerivedCategory.{wA} A]` and
  `[HasDerivedCategory.{wB} B]`, retaining each chosen morphism universe.
- Triangulated functors on the full bounded-below categories:
  `Φ Ψ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B`, with
  `[Φ.CommShift ℤ] [Ψ.CommShift ℤ] [Φ.IsTriangulated] [Ψ.IsTriangulated]`.
  The `commShiftIso 1` components are the specified natural shift comparisons.
- Natural transformation: `η : Φ ⟶ Ψ`. Its compatibility at [1] is the hypothesis
  `hη`; Lean's composition order writes the node's equation as
  `η.app (M⟦1⟧) ≫ (Ψ.commShiftIso 1).hom.app M =
  (Φ.commShiftIso 1).hom.app M ≫ (η.app M)⟦1⟧'`.
- Preservation of every lower cohomology bound: `hΦ` and `hΨ` quantify over every
  bounded-below object M, integer n, and a proof that every H^q(M) vanishes for q<n;
  each concludes the same vanishing for the corresponding image. Vanishing is
  `CategoryTheory.Limits.IsZero` in the abelian category, rather than equality of
  chosen representatives with a zero object.
- The given bounded-below E is `E : DerivedCategory.Plus A`. The hypothesis `hH`
  says, for every integer q, that `η.app ((singleFunctor A 0).obj
  ((homologyFunctor A q).obj E))` is invertible, exactly H^q(E) placed in degree zero.

Conclusions, clause by clause:

- `IsIso (η.app E)` is the node's main conclusion.
- `∀ (m : ℤ)` covers every cohomological degree, including negative degrees.
  The canonical c_m is `(DerivedCategory.TStructure.t.onPlus.truncLEι m).app E`;
  its source is `(DerivedCategory.TStructure.t.onPlus.truncLE m).obj E`.
- `∃ (hcΦ : IsIso ((homologyFunctor B m).map (Φ.map c_m))), ...` states
  invertibility of H^m(Φ c_m). This existential binds only a proof of invertibility
  so that the same proof can be passed explicitly to `CategoryTheory.inv`; it
  introduces no extra map or assumption.
- The next conjunct is `IsIso ((homologyFunctor B m).map (Ψ.map c_m))`, the second
  truncation-map assertion.
- The next conjunct is `IsIso (η.app ((...truncLE m).obj E))`, the assertion at the
  upper truncation.
- The final equality is H^m(η_E) = inv(H^m(Φ c_m)) ≫ H^m(η_tau) ≫ H^m(Ψ c_m).
  This is precisely the displayed formula with Lean's left-to-right composition.
  `@CategoryTheory.inv B _ _ _ ... hcΦ` uses the proof already supplied in the
  first clause. The inverse is the standard unique inverse, not an arbitrary map.
- No upper bound on E and no preservation of infinite limits is assumed.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; inherited through the public imports.
- `def-weil-abstract-derived-category`: `DerivedCategory` and `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated`,
  `CategoryTheory.IsTriangulated`, and `CategoryTheory.Functor.IsTriangulated`,
  in the recorded Mathlib triangulated modules. No structure is copied.
- `def-weil-pbc-bounded-derived-subcategories`: `DerivedCategory.Plus`,
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `def-sbc-standard-tstructure-derived-category`: `DerivedCategory.TStructure.t`,
  in the same module, with its canonical restriction `t.onPlus` from
  `Mathlib.CategoryTheory.Triangulated.TStructure.Induced`; `truncLE` and `truncLEι`
  are from `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`.
- Cohomology and degree-zero placement on D+: `DerivedCategory.Plus.homologyFunctor`
  and `DerivedCategory.Plus.singleFunctor`,
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`.
- Proof plan: `DerivedCategory.Plus.isIso_app_truncLE_of_isIso_app_homology`,
  `Sheaf.CategoryTheory.FinitePostnikovIsomorphism`; imported as a proof dependency.
  The remaining proof dependencies are the recorded Mathlib
  `HomologySequence.exact₁/exact₂/exact₃`, `TStructure.triangleLEGE_distinguished`,
  and `DerivedCategory.Plus.isIso_iff`. Their modules are imported and their full
  signatures were read. The declaration docstring reproduces the five proof steps.

Edge cases checked mathematically before writing:

- E=0: all cohomology and truncation objects are zero; additivity gives the
  asserted invertibility. The hypotheses still quantify over every integer.
- E=A[0], with m<0: tau_{<=m}E is zero and both output cohomologies vanish by
  lower-bound preservation. The inverse in the formula is a map between zero
  objects, which is legitimate.
- A negative lower bound a0 and m=a0-1 or m<a0: the proof chooses
  a=min(a0,m+1), so the finite Postnikov interval is empty when appropriate.
- E unbounded above: each conclusion uses only one finite upper truncation and
  its bounded-below tail. No boundedness-above instance is introduced.
- Non-split complexes: the proof uses the canonical distinguished triangles and
  their long exact sequences, not a splitting into cohomology objects.
- Independent object, hom, and derived-hom universes: no universe equality
  between A and B is imposed.

Searches run with msearch.py under this item (the raw log is searches.jsonl):

- LeanFinder: “A natural transformation between triangulated functors preserving
  lower cohomology bounds is invertible on a bounded below object if invertible on
  all its cohomology objects in degree zero”. Eight hits: homological-functor
  infrastructure and bounded/single-degree representatives, including
  `Functor.isHomological_of_localization` and
  `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`; no full match.
- Loogle: `CategoryTheory.NatTrans, "isIso", "trunc"`: zero hits.
- grep: `isIso_app|truncLE|homologyFunctor` in
  `Algebra/Homology/DerivedCategory`: 25 reported hits for cohomology, truncation,
  fractions, and single functors, no full heart test with all comparison clauses.
- LeanSearch: “Natural transformation of lower bound preserving triangulated
  functors isomorphism on all cohomology objects implies isomorphism on bounded
  below objects and upper truncations”: eight hits, including `NatTrans.app_homology`,
  `Functor.isTriangulated_of_iso`, and `TStructure.truncLTι`; no exact match for
  the conjunction and displayed naturality formula.
- Project rg: `isIso_app_of_forall_homology|lem-weil-pbc-heart-test-bounded-below|
  [Pp]ostnikov|[Hh]eart[Tt]est` in both lean/WeilConjectures and lean/Sheaf.
  The existing upstream `WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage`
  supplies partial results, including `Plus.isIso_app_of_forall_homology` and
  `Plus.isIso_homologyFunctor_map_map_truncLEι_app`. Read the entire module:
  the former uses an isomorphism-closed property P and gives only IsIso at E;
  neither states this node's entire conjunction and formula. The landed finite
  Postnikov module supplies only its bounded-truncation part. No duplicate found.
- `dag/lean_names_upstream.json` and the upstream source were searched for the
  item id: no declaration attached to this item. No repair note exists for it.

No statement dispute or source correction was found. The source paragraph and
Stacks derived.tex, `lemma-negative-vanishing` (Tag 05TC), were read locally.

## Second reading by NP

I reread the node, dependency signatures, and the final module as the same worker;
no independent worker was started, as the dispatcher brief prohibits sub-agents.
The maintainer performs the independent review of this delivery.

The category/derived-category binders match A and B without a size restriction;
the functors have exactly D+ as source and target. The [1] equation has the two
specified shift comparisons in the correct order. The hΦ/hΨ implications quantify
all objects and all integer bounds, and hH refers to the actual cohomology of E
in degree zero. The conclusion has all four requested degreewise assertions and
the main IsIso assertion. The inverse in the formula is composable first in
Lean order, followed by η at the truncation and Ψ(c_m); this matches the source's
right-to-left formula. No clauses or hypotheses were added or omitted.
The only correction during elaboration was removal of an extra closing parenthesis
at the end of the equality; no mathematical statement changed. No node fields
other than lean are changed. There are no additional declarations or hollow data.

Validation: scompile.py checked both the isolated sandbox and the library module
cleanly (2.5 s and 2.6 s respectively); all binders and universes are explicit.
