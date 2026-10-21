## Worker report

Item: `lem-sf-localizing-hom-test`. The new module
`Sheaf.CategoryTheory.LocalizingHomTest` states
`CategoryTheory.ObjectProperty.isIso_of_bijective_postcomp_shift_generators`.
Its sole theorem has proof `sorry`; it introduces no new definition or axiom.
The natural-language statement, statement dependencies, proof, and proof dependencies are unchanged.

I read the item's statement and all five proof steps, the two statement-dependency nodes and
recorded Mathlib signatures, and the current blueprint proof
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/` +
`sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md`.
The source places are the closed-adjoint uniqueness and final restriction paragraphs.
The module docstring identifies that source, and the theorem docstring carries all five steps
of the node's cone/left-orthogonal proof with the corresponding DAG IDs and Stacks tags.
No repair note for this item was present in `coord/repair-notes`.

Hypotheses and clauses, matched individually:

- A locally small category is `{C : Type u} [Category.{v} C]`: each Hom is in `Type v`,
  with the object universe `u` independent of `v`.
- Its additive structure is `[Preadditive C] [HasZeroObject C]`, together with the
  additive integer shifts `[HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]`.
  `[Pretriangulated C]` supplies TR1--TR3 and `[IsTriangulated C]` supplies TR4,
  exactly as the recorded `def-weil-triangulated-category` Mathlib match specifies.
  Finite biproducts follow from the pretriangulated structure.
- All small coproducts are `[HasCoproducts.{v} C]`. The same `v` is used by Hom and
  by `ObjectProperty.IsLocalizing` for coproduct indices, as the node requires.
- An arbitrary class of generators is `(S : ObjectProperty C)`, a predicate on all
  objects. There is no small index type, compactness predicate, essential-smallness
  assumption, or shift-stability hypothesis on `S`.
- The defining intersection `Loc(S)` is the existing `S.localizingClosure` from
  `WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure`, lines 52--60 and 72--76.
  Its value at an object is `∀ Q : ObjectProperty C, S ≤ Q → Q.IsLocalizing → Q X`.
  `Q.IsLocalizing` extends `Q.IsTriangulated`, `Q.IsClosedUnderIsomorphisms`, and
  closure under colimits of every `Discrete J` with `J : Type v`. Thus these are precisely
  full replete triangulated subcategories closed under the indicated small coproducts.
  This uses the existing definition for the notion explicitly introduced within the item's
  own statement; it does not introduce a second localizing-closure definition.
- The objects and arrow are `{B G : C} (α : B ⟶ G)`; membership in the intersection
  is recorded separately by `(hB : S.localizingClosure B)` and
  `(hG : S.localizingClosure G)`.
- Every generator and every integer shift are quantified by
  `∀ (X : C), S X → ∀ (n : ℤ), ...` in `hα`.
- The required map is exactly postcomposition:
  `Function.Bijective (fun (f : X⟦n⟧ ⟶ B) ↦ f ≫ α)`.
  Its domain is `Hom(X[n],B)`, its inferred codomain is `Hom(X[n],G)`, and
  bijectivity includes both injectivity and surjectivity.
- The only conclusion is `IsIso α`, expressing that the specified arrow is invertible.

Dependency declarations read and used:

- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated` (lines 43--87),
  with `CategoryTheory.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Triangulated` (lines 301--315).
  The theorem imports `Mathlib.CategoryTheory.Triangulated.Triangulated` publicly.
- `def-weil-triangulated-subcategory`: `CategoryTheory.ObjectProperty.IsTriangulated`
  in `Mathlib.CategoryTheory.Triangulated.Subcategory` (lines 180--184);
  its full-subcategory pretriangulated structure and inclusion exactness are at
  lines 693--724. This module is imported publicly. This same class is a parent of
  the existing `ObjectProperty.IsLocalizing` used by the intersection definition.
- The closure definition is imported publicly from
  `WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure`.
- The proof-only import `Mathlib.CategoryTheory.Triangulated.Orthogonal` exposes
  `CategoryTheory.ObjectProperty.instIsTriangulatedLeftOrthogonalOfIsStableUnderShiftInt`
  (`lem-sf-shift-stable-left-orthogonal`, line 68), and its repleteness and zero-object
  instances in `Mathlib.CategoryTheory.ObjectProperty.Orthogonal` (lines 47--68).
- The remaining two proof dependencies are Mathlib leaves already available through
  the imports: `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂` and
  `coyoneda_exact₁`, together with `comp_distTriang_mor_zero₁₂`, for
  `lem-weil-pbc-hom-into-triangle-exact`; and
  `CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁` for
  `lem-kun-distinguished-cone-zero`. Their node records and signatures were read.

Edge cases checked before writing:

- `S = ⊥`: the Hom hypothesis is vacuous but both objects must lie in the localizing
  closure of the empty class, which consists of zero objects. Thus every such arrow
  is invertible; no nonempty-generator hypothesis is needed or present.
- The zero category and a class containing only zero objects are allowed.
- `S = ⊤`: taking the shift `n = 0` includes the ordinary Yoneda isomorphism test.
- Positive, zero, and negative shifts are all included by `n : ℤ`.
- Empty coproducts are included: localizing subcategories contain zero objects and the
  proof uses coproduct uniqueness for the empty family too.
- An object class larger than the fixed Hom universe remains expressible by
  `ObjectProperty C`; neither the signature nor the cone proof forms its coproduct.

Searches actually run (the wrapper log is `searches.jsonl` in this sandbox):

- `msearch.py`, LeanFinder: "A morphism between objects in the localizing closure of an
  arbitrary class is an isomorphism if postcomposition on Hom from every integer shift
  of each generator is bijective". Eight hits, led by
  `Localization.hasSmallLocalizedShiftedHom_iff`, `Localization.HasSmallLocalizedShiftedHom`,
  `Localization.isoOfHom`, and `Localization.LeftBousfield.W_iff_isIso`; none states this
  arbitrary-class localizing-closure test.
- `msearch.py`, Loogle: `CategoryTheory.ObjectProperty.localizingClosure`.
  No hits; unknown identifier in that Mathlib-only index. This does not establish
  absence from the project: direct source inspection found and reused its definition.
- `msearch.py`, grep: `localizing.*[Ii]so|[Ii]so.*localizing|bijective` in
  `CategoryTheory/Triangulated`. Seven hits: generic Yoneda isomorphism arguments,
  `rightOrthogonal.map_bijective_of_isTriangulated`, and
  `leftOrthogonal.map_bijective_of_isTriangulated`. The latter concern a localization
  functor's Hom maps, not postcomposition with an arrow in the localizing closure.
- `msearch.py`, LeanSearch: "A morphism in the localizing closure is invertible when Hom
  from all shifts of generators is bijective". Eight hits about localization inversion
  and local objects; no exact match.
- Direct `rg` searches in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` checked localizing closure, isomorphism tests,
  bijectivity, and the chosen declaration name. Searching the item's ID in
  `lean/WeilConjectures` returned no match. The chosen full name was absent.
  Existing `ObjectProperty.isZero_of_forall_eq_zero_localizingClosure` in
  `WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration` requires a
  shift-stable class and states a zero-object test, not the present morphism theorem.
  `Sheaf.Paper.LocalizingExceptionalAdjoint` has a private `generators_detect_iso` for
  a set-indexed generating family of the entire category; it neither exposes a usable
  public declaration nor states the arbitrary-class localizing-closure theorem.
  Mathlib's `LocalizingSubcategory` concerns Verdier left/right localizing conditions,
  a different notion. No duplicate theorem was found.

Validation: `scompile.py NY lem-sf-localizing-hom-test` compiled both the sandbox check
and the named library module cleanly on the server (1.5 s and 1.4 s). All variables and
universes are explicitly bound; the file also respects the 100-character line limit.
No statement correction, disputed statement, missing dependency, or new node was necessary.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
