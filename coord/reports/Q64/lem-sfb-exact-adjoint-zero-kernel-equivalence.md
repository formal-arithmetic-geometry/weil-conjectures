## Worker report

The module `Sheaf.CategoryTheory.Triangulated.ExactAdjointZeroKernel` states
`CategoryTheory.Adjunction.isIso_unit_and_counit_of_fully_faithful_of_zero_kernel`.
Its only proof is `by sorry`. There are no new definitions or dependency repairs,
and the node changes only in `lean`.

Source read: `literature/stacks-project/derived.tex`, lines 2372–2404,
Tag 09J1, `lemma-fully-faithful-adjoint-kernel-zero`, including the proof.
The node's explicit unit/counit conclusion is precisely the source proof's
construction of the equivalence. No statement correction or disputed statement.
No released repair note exists for this item in the read clone.

Hypotheses and clauses, in order:

1. The two triangulated categories are `{C : Type u₁} {D : Type u₂}` with
   `[Category.{v₁} C] [Category.{v₂} D]`, `[Preadditive C] [Preadditive D]`,
   `[HasZeroObject C] [HasZeroObject D]`, `[HasShift C ℤ] [HasShift D ℤ]`,
   the two additive-shift instance families, `[Pretriangulated C]`
   `[Pretriangulated D]`, and `[IsTriangulated C] [IsTriangulated D]`.
   These are exactly the interface recorded by `def-weil-triangulated-category`:
   TR1–TR3 are `Pretriangulated`, TR4 is `IsTriangulated`, and finite
   biproducts follow from these assumptions. All four universes are independent.
2. The given functors are `(F : C ⥤ D) (G : D ⥤ C)`.
   Their exactness is `[F.CommShift ℤ] [G.CommShift ℤ]`
   `[F.IsTriangulated] [G.IsTriangulated]`. The commutation data encode the
   shift comparison; `Functor.IsTriangulated` preserves distinguished triangles
   and has a derived `Additive` instance, so no separate additivity hypothesis
   is necessary. No compatibility of the adjunction with these chosen shift
   comparisons is assumed or needed.
3. Full faithfulness is `[F.Full] [F.Faithful]`: surjectivity and injectivity
   of every morphism map, respectively, hence exactly the stated bijections.
4. The specified adjunction is `(adj : F ⊣ G)`. Mathlib's `Adjunction` stores
   its actual natural unit and counit and both triangle identities and provides
   the associated natural Hom-set bijections. It does not replace this data by
   an existentially chosen adjunction.
5. The zero-kernel hypothesis is
   `(hG : ∀ Y : D, IsZero (G.obj Y) → IsZero Y)`.
   `IsZero` is the categorical zero-object predicate, equivalent to being
   isomorphic to the chosen zero object in these categories (`IsZero.isoZero`
   and invariance under isomorphism). This is exactly the node's implication
   for every Y, with no conservativity assumption added.
6. Both asserted natural isomorphisms are
   `IsIso adj.unit ∧ IsIso adj.counit`. These are isomorphisms in the functor
   categories, for the original unit and counit. They exhibit F and G as the
   claimed inverse equivalences, rather than merely asserting that an
   unrelated equivalence exists.

Dependency declarations read and used:

- `def-weil-triangulated-category` is a Mathlib leaf, not a missing Lean
  attachment. Its recorded `mathlib_match` gives
  `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  `CategoryTheory.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Triangulated`, and
  `CategoryTheory.Functor.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Functor`. Their source signatures and
  docstrings were read. The public `Functor` import exposes these notions.
- `Mathlib.CategoryTheory.Adjunction.Basic`, public import:
  `CategoryTheory.Adjunction`, with its stored unit, counit and triangle
  identities; its source definition and docstring were read.
- `lem-sp-adjunction-unit-fully-faithful-left`, proof dependency, is the
  Mathlib leaf `CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful`
  in `Mathlib.CategoryTheory.Adjunction.FullyFaithful` (plain import).
  Read its full signature with `[L.Full] [L.Faithful]` and `h : L ⊣ R`.
- `lem-kun-distinguished-cone-zero`, proof dependency, is the Mathlib leaf
  `CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated` (plain import).
  Read its distinguished-triangle context and the equivalence
  `IsZero T.obj₃ ↔ IsIso T.mor₁`.

The declaration docstring carries all four DAG proof steps: invert the unit
using full faithfulness; use the right triangle identity and complete the
counit to a distinguished triangle; apply G, the zero-cone criterion and
the zero-kernel hypothesis; obtain componentwise inverse counits and their
naturality. It names the DAG proof dependencies and their Stacks sources.

Edge cases checked mathematically before drafting: the zero category and
identity adjunction satisfy the conclusion. For the inclusion
C → C × E and right-adjoint projection, the omitted zero-kernel condition
would fail on (0,Z) for any nonzero Z of E, as required; thus the condition
is substantive. A zero right adjoint satisfying the condition forces every
object of D to be zero, and full faithfulness then forces C to be zero too.
No boundedness, size relation, nonzero object, compact-generation, or
adjunction-shift-compatibility restriction is introduced. Empty categories
are already excluded by the source's zero-object requirement, not by an
extra binder.

Searches made with the prescribed `msearch.py` for Q64 and this item:

- LeanFinder: "An exact fully faithful left adjoint between triangulated
  categories whose right adjoint detects zero objects is an equivalence".
  Eight hits, including adjoint triangulated-functor preservation,
  `Equivalence.IsTriangulated.mk'`/`mk''`, and
  `IsTriangulated.of_fully_faithful_triangulated_functor`. None is the
  zero-kernel equivalence criterion.
- LeanSearch: "A fully faithful triangulated left adjoint is an equivalence
  when the right adjoint detects zero objects". Eight hits, primarily the
  triangulated adjunction API, plus
  `Limits.IsZero.of_full_of_faithful_of_isZero`. The latter detects zero
  for an already fully faithful functor; it does not prove this criterion.
- Loogle: `"IsTriangulated", "IsEquivalence"`: zero hits.
- Mathlib grep via msearch: `isEquivalence|IsEquivalence|reflectsIsomorphisms`
  in `CategoryTheory/Triangulated`: four hits, all rotation equivalences.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `zero_kernel|zeroKernel|detects.*zero|exact-adjoint-zero-kernel|isEquivalence.*[Zz]ero|isIso.*[Zz]ero`
  found applications and unrelated zero-detection results, not this statement.
  Searching the exact node id upstream found no occurrence; the project
  occurrences are comments in consumers, not a declaration of this criterion.
  Further searches of both CategoryTheory trees for fully faithful/zero-kernel
  equivalence phrases and of `dag/lean_names_upstream.json` for the proposed
  declaration name found no duplicate. Mathlib's triangulated adjunction
  source contains no zero-kernel criterion.

Validation: the prescribed `scompile.py` successfully compiled the delivered
file as both a sandbox module and its intended library module, with no errors
or unexpected warnings. `autoImplicit` is explicitly false. Every variable
and universe is bound. No live source was modified and no global build was run.

## Second reading by Q64

I reread the node and the final Lean file in this worker session; this is a
self-check, not an assertion of independent agent review. The dispatch brief
prohibits starting other agents and assigns independent review to the maintainer.
The two category structures match the recorded triangulated-category interface;
both exact functors, the full/faithful hypothesis, the actual adjunction, and
the implication for every object Y are present. The conclusion explicitly
contains both `adj.unit` and `adj.counit`. The source proof uses no omitted
compatibility condition. No mismatch or change was found on this rereading.
