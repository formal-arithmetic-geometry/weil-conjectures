## Worker report

The module `Sheaf.CategoryTheory.RightFractionDenseSubcategory` states
`CategoryTheory.rightFractionDenseSubcategory`.  It uses Mathlib's
`MorphismProperty.HasRightCalculusOfFractions` for the ambient right-fraction
axioms, `ObjectProperty.FullSubcategory` and its inclusion `P.ι` for the full
subcategory, and `MorphismProperty.inverseImage W P.ι` for the restricted class
`W_B`.  The hypothesis
`hP : ∀ X : C, ∃ (B : P.FullSubcategory) (s : P.ι.obj B ⟶ X), W s`
renders the denominator-density condition object by object.  `Q` and `QB` are
localization functors with Mathlib's `Functor.IsLocalization` classes.  The
conclusion has two clauses: the restricted property has
`HasRightCalculusOfFractions`, and there is an equivalence functor
`F : E ⥤ D` together with `Nonempty (QB ⋙ F ≅ P.ι ⋙ Q)`, expressing the
inclusion-induced equivalence of localizations.  Universes `u₁,v₁,u₂,v₂,u₃,v₃`
allow the categories and localizations to lie in a common larger universe.

The statement dependency is the Mathlib declaration
`CategoryTheory.Localization.lift` from
`Mathlib.CategoryTheory.Localization.Predicate`; it supplies the universal
property notion represented by the `IsLocalization` typeclass.  The proof-only
fraction and equivalence ingredients are Mathlib declarations recorded by the
node: `CategoryTheory.Localization.exists_rightFraction`,
`CategoryTheory.MorphismProperty.RightFraction.map_eq_iff`,
`CategoryTheory.Localization.essSurj`, and
`CategoryTheory.Functor.asEquivalence`.

Edge cases checked: `P.FullSubcategory` permits an empty subcategory, but `hP`
then correctly forces a denominator source for every object of `C`; identities
and composition are included in `HasRightCalculusOfFractions`; no functorial
choice of the arrows in `hP` is introduced; no triangulated structure or
saturation assumption is present; empty and singleton categories and identity
localizations are covered; independent category universes are retained.

Searches for an existing declaration: `msearch.py leanfinder "right fraction
dense subcategory"` found only generic localization and triangulated
localization results; `msearch.py loogle "dense subcategory, right fraction"`
returned no exact hit; grep over Mathlib, `WeilConjectures/`, and `lean/Sheaf`
found only generic `RightFraction` APIs and no dense-subcategory theorem.
`rg` searches for `RightFraction`, `DenseSubcategory`, and localization
restriction likewise found no declaration with this statement.

## Second reading by Q135

I reread the node and module line by line.  The category `C`, morphism class
`W`, ambient right-calculus hypothesis, full subcategory `P`, and every-object
arrow `s : P.ι.obj B ⟶ X` are all explicit.  The restricted class is exactly
`W.inverseImage P.ι`, which is the intersection with arrows of the full
subcategory.  Both localization functors and their localization hypotheses are
present.  The first conclusion clause states the restricted right calculus;
the second supplies an equivalence functor and the comparison isomorphism from
`QB` followed by that functor to the ambient localization after inclusion.  No
hypothesis, object, universe, or conclusion clause was added or omitted.

Saved-packet repair, 2026-10-17: the required initial dry run reported only
the private-module warning. Added `@[expose] public section`, matching the
CompactObject example, so the theorem is exported. Expanded the theorem's
docstring to give all seven DAG proof steps, including the restricted Ore and
cancellation arguments, the universal-property comparison, roof surjectivity
and injectivity, and the two essential-surjectivity arguments. The theorem
signature and mathematical statement are unchanged.

For the ambient axioms, `hW` includes identities and closure under composition
through `HasRightCalculusOfFractions.toIsMultiplicative`; its
`exists_rightFraction` field is the Ore square with only the given denominator
in `W`, and its `ext` field is cancellation after postcomposition. The full
subcategory is precisely the one carried by `P`; `W.inverseImage P.ι` tests
membership on each underlying arrow. The natural isomorphism in the conclusion
identifies `F` as an inclusion-induced localization functor, rather than an
unrelated equivalence. Universal-property uniqueness makes any such induced
functor naturally isomorphic to it. All category object and morphism universes
are explicit and independent, and all variables are bound.

The current statement dependency is still the Mathlib leaf described above;
its `Localization.lift`, `fac`, `liftNatTrans`, `liftNatIso`, and `natTrans_ext`
signatures were read in `Mathlib.CategoryTheory.Localization.Predicate`.
The fraction proof leaves were checked in
`Mathlib.CategoryTheory.Localization.CalculusOfFractions`, and the equivalence
criterion in `Mathlib.CategoryTheory.Equivalence` (already publicly imported by
the localization modules). All proof dependencies are Mathlib leaves; no
additional project module imports are required. Stacks `derived.tex` at
`lemma-localization-subcategory` was reread: the node explicitly requests its
categorical refinement argument, without its triangulated specialization.
Current-source searches for the theorem name and node id in the upstream
`WeilConjectures`, the side `lean/Sheaf`, and `dag/lean_names_upstream.json`
found no duplicate. No repair note was present. No statement fault was found.

Mechanical self-check: the saved node agrees with the current repository in
every field except `lean`; the recorded signature matches the module verbatim,
and every Lean line has at most 100 characters. The only proof remains `sorry`.
