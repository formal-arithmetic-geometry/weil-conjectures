## Worker report

The new module `Sheaf.CategoryTheory.FinitePostnikovIsomorphism` states
`DerivedCategory.Plus.isIso_app_truncLE_of_isIso_app_homology`, with exactly one
postponed theorem and no new definitions. The item JSON changes only in `lean`.
Its statement, dependencies, proof and source remain unchanged.

I read the item, all five statement dependencies, all six proof dependencies,
and the recorded declarations with their surrounding parameters and docstrings.
I read Stacks `derived.tex`, Remark 08J5, including its successive upper-truncation
triangle, and the current blueprint's `sk-thm-properbasechange.proof.md`,
“Bounded below complexes” paragraph, especially the finite Postnikov sentence.

Clause-by-clause correspondence:

- The abelian category A is `{A : Type u} [Category.{v} A] [Abelian A]`.
  `[HasDerivedCategory.{w} A]` specifies the chosen localization and its morphism
  universe, as required by the recorded abstract-derived-category interface.
  The universes `u`, `v`, and `w` are independent.
- The arbitrary triangulated target T is `{T : Type uT} [Category.{vT} T]`,
  `[Preadditive T] [HasZeroObject T] [HasShift T ℤ]`, additive integer shifts,
  `[Pretriangulated T] [IsTriangulated T]`. These are exactly the recorded
  encoding of the triangulated-category definition; no abelian or derived
  target structure is assumed. Target object and morphism universes are
  independent of the source and localization universes.
- The full bounded-below domain is the existing `DerivedCategory.Plus A`.
  `(Φ Ψ : DerivedCategory.Plus A ⥤ T)` are functors on this domain.
- The specified coherent shift comparisons are `[Φ.CommShift ℤ]` and
  `[Ψ.CommShift ℤ]`. Their degree-one components are
  `(Φ.commShiftIso (1 : ℤ)).hom.app M` and
  `(Ψ.commShiftIso (1 : ℤ)).hom.app M`. Mathlib uses coherent integer shifts
  as the encoding of the given shift isomorphism of an exact functor.
- Exactness with respect to those comparisons is `[Φ.IsTriangulated]` and
  `[Ψ.IsTriangulated]`. Their additivity follows from Mathlib's existing
  instance for triangulated functors, rather than an extra hypothesis.
- The natural transformation is `(η : Φ ⟶ Ψ)`.
- The shift-compatibility hypothesis is the explicit degree-one equation `hη`:
  `η.app (M⟦(1 : ℤ)⟧) ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app M =
  (Φ.commShiftIso (1 : ℤ)).hom.app M ≫ (η.app M)⟦(1 : ℤ)⟧'` for every M.
  Composition `≫` runs from left to right, so this is exactly
  ζ_M ∘ η_{M[1]} = η_M[1] ∘ ξ_M. No all-integer compatibility assumption on η
  is imposed; it follows by iteration and inverse shift at the proof stage.
- The input is `(E : DerivedCategory.Plus A)` and `(a b : ℤ)` with
  `(hab : a - 1 ≤ b)`, exactly the stated endpoints and empty-interval option.
- The cohomological lower bound is the explicit hypothesis `hE`:
  `∀ (q : ℤ), q < a → IsZero ((homologyFunctor A q).obj E)`.
  This is cohomological boundedness, not a condition on a chosen representative.
- The finite set of invertible components is `hH`, quantified over all integers
  q with `a ≤ q` and `q ≤ b`. The cohomology object is
  `(DerivedCategory.Plus.homologyFunctor A q).obj E`; its degree-zero placement
  is `(DerivedCategory.Plus.singleFunctor A 0).obj` of that object. `IsIso`
  expresses invertibility of the component of η at precisely that placement.
- The conclusion is `IsIso (η.app
  ((DerivedCategory.TStructure.t.onPlus.truncLE b).obj E))`.
  This is the canonical upper truncation for the standard t-structure induced
  on the full bounded-below derived category, following the project's D+
  truncation convention. It does not substitute a chosen bounded model.

Dependency declarations used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (publicly supplied by the Plus import).
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; cohomology is the existing
  `DerivedCategory.homologyFunctor` from
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, restricted by
  `DerivedCategory.Plus.homologyFunctor` from
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated`,
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, and
  `CategoryTheory.IsTriangulated`,
  `Mathlib.CategoryTheory.Triangulated.Triangulated`.
  `Functor.CommShift` and `Functor.IsTriangulated` are used from
  `Mathlib.CategoryTheory.Shift.CommShift` and
  `Mathlib.CategoryTheory.Triangulated.Functor`.
- `def-weil-pbc-bounded-derived-subcategories`: `DerivedCategory.Plus`,
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `def-sbc-standard-tstructure-derived-category`:
  `DerivedCategory.TStructure.t`, same module; its `onPlus` is from
  `Mathlib.CategoryTheory.Triangulated.TStructure.Induced`, and `truncLE` is
  from `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`.
- Degree-zero objects use `DerivedCategory.Plus.singleFunctor` from
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`, not a private replacement.
- Proof dependency `lem-weil-pbc-derived-plus-iso-on-cohomology`:
  `DerivedCategory.Plus.isIso_iff`, same Plus module (public import).
- Proof dependency `lem-weil-pbc-truncation-cohomology`:
  `CochainComplex.quasiIsoAt_ιTruncLE` from
  `Mathlib.Algebra.Homology.Embedding.CochainComplex` (ordinary proof import).
- Proof dependency `lem-weil-pbc-truncation-triangle`:
  `DerivedCategory.truncation_triangle` from
  `WeilConjectures.CategoryTheory.TruncationTriangle` (ordinary proof import).
- Proof dependency `lem-sf-triangle-two-out-of-three`:
  `CategoryTheory.NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃` and the two sibling
  two-out-of-three lemmas from
  `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`
  (ordinary proof import). The theorem docstring retains the complete five-step
  DAG proof, including the zero base case and the shift conjugation argument.

Searches for an existing statement (2026-10-21):

- `msearch.py ... leanfinder`: “A shift compatible natural transformation between
  triangulated functors on a bounded below derived category is invertible on an
  upper truncation if invertible on the degree zero cohomology objects in its
  finite range”. Eight hits: derived-category shift compatibility,
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`,
  `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`, homological
  functor infrastructure, and factorization lemmas. None states this theorem.
- `msearch.py ... loogle`: `DerivedCategory.Plus, CategoryTheory.IsIso`.
  Three hits: `DerivedCategory.Plus.isIso_iff` and two derived-functor instance
  declarations. None gives finite Postnikov propagation.
- `msearch.py ... grep`: `isIso_app|Postnikov|postnikov|finite.*trunc`, restricted
  to `Algebra/Homology/DerivedCategory`. One hit, a use of
  `NatTrans.isIso_app_iff_of_iso` in `DerivabilityStructureInjectives.lean`.
- `msearch.py ... leansearch`: “Natural transformation of triangulated functors
  invertible on finite upper truncation if invertible on all cohomology objects
  placed in degree zero”. Eight hits, all general triangulated-functor,
  triangle-morphism or right-derived-zero infrastructure, with no exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Postnikov, finite-range,
  truncation and single-object invertibility found
  `WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage`.
  I read its signatures and docstrings: `isIso_app_of_isGE_of_isLE` and
  `isIso_app_of_bounded` have target `DerivedCategory.Plus D` for an abelian D,
  so do not state this arbitrary triangulated-target node. They also package
  the hypothesis using an isomorphism-closed heart property. The unrelated
  ModuleCat generation theorem concerns unbounded module derived categories
  with coproduct-preservation assumptions. Neither is an exact existing match.
- `rg` for the item id in `lean/WeilConjectures`: no hit.
- Name searches for `finitePostnikov`, `finite_postnikov` and
  `isIso_app_truncLE_of_isIso_app_homology` in Mathlib, both project source
  roots and `dag/lean_names_upstream.json`: no hit before this delivery.

Edge cases checked before writing:

- `b = a - 1`: there is no integer satisfying the two bounds in `hH`; all
  cohomology of the upper truncation vanishes by `hE`. Exact functors preserve
  zero objects, so the conclusion follows without any component assumption.
- `b = a`: the sole Postnikov quotient is H^a(E)[-a]; inverse and forward
  shifts of the explicit compatibility equation give the required component.
- Negative a, b and q are unrestricted integers, including inverse shifts.
- E may be unbounded above. Only its canonical upper truncation occurs in
  the conclusion; cohomology above b is unrestricted.
- E can be zero or acyclic. All components between its zero images are
  invertible. No nonzero-object assumption occurs.
- The target can be any triangulated category, including the zero category.
  No cohomology functor, t-structure, or abelian structure is required on it.
- No splitting of the Postnikov triangles is assumed; two-out-of-three applies
  to their actual distinguished triangles.
- All five universes are explicitly declared and every binder is explicit;
  no local notation, local instances, hidden helpers, or auto-bound implicits
  are introduced. There are no source corrections or disputed statements.

Validation: the prescribed `scompile.py Q12
lem-weil-pbc-finite-postnikov-isomorphism <module>` compiled the sandbox and
library forms cleanly (2.0 s and 1.9 s), with no errors or warnings.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
