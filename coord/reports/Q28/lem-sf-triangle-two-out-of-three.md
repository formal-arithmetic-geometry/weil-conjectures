## Worker report

Existing declaration delivery: no Lean library module is written. The complete statement is
already present as these three lemmas in
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor` (slopmaster2), lines 61, 69, 77:

- `CategoryTheory.NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂`;
- `CategoryTheory.NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃`;
- `CategoryTheory.NatTrans.isIso_app_obj₁_of_isIso_app_obj₂₃`.

Read the module's full signatures, section variables, docstrings and proof bodies. The same
source was confirmed using `scompile.py --source` against the current published library. Each
docstring explicitly identifies blueprint `lem-sf-triangle-two-out-of-three`. The node's `lean`
record names all three declarations; its `statement` is the first lemma's signature verbatim,
with the inherited context described below. Only the node's `lean` field changes.

Hypothesis and clause correspondence:

- Categories C and D have independent object and morphism universes (`{C D : Type*}` and
  `[Category* C] [Category* D]`). The node's triangulated categories supply `[Preadditive C]`,
  `[HasZeroObject C]`, `[HasShift C ℤ]`, `[∀ n : ℤ, (shiftFunctor C n).Additive]`,
  `[Pretriangulated C]`, and the same structures on D. Their octahedral axioms are not needed:
  these existing lemmas are valid already for pretriangulated categories. Specializing to
  triangulated categories gives exactly the categorical setting in the node.
- Φ and Ψ are `{F₁ F₂ : C ⥤ D}`. Their natural shift isomorphisms are `[F₁.CommShift ℤ]` and
  `[F₂.CommShift ℤ]`, with φ and ψ equal to `(Fᵢ.commShiftIso (1 : ℤ)).app X`.
  Exactness is `[F₁.IsTriangulated] [F₂.IsTriangulated]`. These classes say that the image
  of every distinguished triangle is distinguished; functor additivity follows from them.
- α is `(τ : F₁ ⟶ F₂)`, so naturality for all three arrows is built in.
  `[NatTrans.CommShift τ ℤ]` is the shift-compatibility premise. Its degree-one equation is
  `(F₁.commShiftIso 1).hom.app X ≫ (τ.app X)⟦1⟧' =
   τ.app (X⟦1⟧) ≫ (F₂.commShiftIso 1).hom.app X`.
  Reversing equality and reading `≫` as forward composition gives exactly
  ψ_X ∘ α_{X[1]} = α_X[1] ∘ φ_X. This is not an assumption that α is invertible.
  The integer-shift encoding is the coherent extension of the chosen degree-one shift:
  compatibility propagates to positive integers by composition, to zero by the unit, and
  to negative integers using the inverse shift equivalence. Thus this does not impose
  extra compatibility beyond the node's equation for every X.
- The arbitrary distinguished triangle is `{T : Triangle C}` and `(hT : T ∈ distTriang C)`.
  `T.obj₁`, `T.obj₂`, `T.obj₃` are X, Y, Z; its arrows have precisely the node's types,
  including `T.mor₃ : T.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧`.
- Pair (X,Y): `(h₁ : IsIso (τ.app T.obj₁)) (h₂ : IsIso (τ.app T.obj₂))` yields
  `IsIso (τ.app T.obj₃)` in the first lemma.
- Pair (X,Z): the first/third `IsIso` hypotheses yield `IsIso (τ.app T.obj₂)` in the
  second lemma.
- Pair (Y,Z): the second/third `IsIso` hypotheses yield `IsIso (τ.app T.obj₁)` in the
  third lemma. These are all three possible pairs, so no clause is omitted.

Dependency declarations read and used by the existing implementation:

- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `CategoryTheory.IsTriangulated`
  in `Mathlib.CategoryTheory.Triangulated.Triangulated`, and
  `CategoryTheory.Functor.IsTriangulated` in `Mathlib.CategoryTheory.Triangulated.Functor`.
  Read the full signatures, class fields and docstrings.
- `def-weil-pbc-triangles-with-shift`: `CategoryTheory.Pretriangulated.Triangle`,
  `TriangleMorphism`, `triangleCategory`, `Triangle.isoMk`, `Triangle.isIso_of_isIsos`
  in `Mathlib.CategoryTheory.Triangulated.Basic`. The first two are the objects and
  commuting-square data used here; no private replacement is made.
- Proof step 1 is exactly `F₁.map_distinguished T hT`, `F₂.map_distinguished T hT`.
- Proof step 2 uses `CategoryTheory.NatTrans.mapTriangle` in the same upstream module,
  already recorded for `lem-weil-pbc-commshift-nattrans-triangle-morphism`. Its three
  components are the three components of τ, and its last square follows from the
  stated compatibility and naturality for `T.mor₃`; its naturality in triangles is proved.
- Proof step 3 uses `CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂`,
  `isIso₂_of_isIso₁₃`, `isIso₁_of_isIso₂₃` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, the three matches of
  `lem-sf-triangle-morphism-iso`. Read their full signatures/docstrings and the upstream
  applications: both image triangles are supplied with their distinguishedness proofs.

Edge cases checked: zero triangles, contractible triangles, and rotations remain covered;
`IsIso` on a zero object is meaningful and no nonzero-object assumption is present.
There is no restriction on characteristic, coefficient objects, boundedness or universes.
The identity transformation satisfies compatibility and every pairwise conclusion. A merely
natural transformation need not commute with shift, so the explicit compatibility premise
must remain; it is present in all three upstream declarations. None assumes global `IsIso τ`.

Searches made (2026-10-16):

- `msearch.py ... leanfinder` with query “natural transformation of exact triangulated
  functors compatible with shifts is an isomorphism on two terms of a distinguished
  triangle hence the third”: 8 hits including `Functor.mapTriangleCommShiftIso` and
  `Functor.mapTriangleIso`; no exact Mathlib transformation theorem.
- `msearch.py ... loogle` with query
  `CategoryTheory.NatTrans.CommShift, CategoryTheory.Functor.IsTriangulated`: 8 hits
  about transporting functor triangulatedness; none is the componentwise assertion.
- `msearch.py ... grep` with query `isIso.*of_isIso|mapTriangleIso`, subdirectory
  `CategoryTheory/Triangulated`: 11 hits, including all three generic triangle-morphism
  lemmas. These require the triangle morphism as input; `mapTriangleIso` assumes a
  natural isomorphism and does not express the present assertion.
- `msearch.py ... leansearch` with query “natural transformation commuting with shifts
  isomorphism on two objects of distinguished triangle”: unavailable, Internal Server Error.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf`, searching `CommShift`,
  `mapTriangle`, `isIso_app_obj₃_of_isIso_app_obj₁₂` and the item id: upstream
  `Mathlib/CategoryTheory/Triangulated/Functor.lean` contains the exact three declarations
  and the item-id docstrings, in both local source trees; no duplicate Sheaf declaration.
- Read Mathlib `Shift.CommShift` to check `NatTrans.CommShift.shift_comm` and
  `NatTrans.shift_app_comm` in full. Read the full upstream module, not just its names.

Validation: `scratchpad/ExistingChecks.lean` imports the existing module, checks all three
fully elaborated signatures and prints their axioms via `scompile.py`. It is a scratch probe,
not a delivered library module. The required `deliver2.py --no-push` also compiles its own
existing-declaration probes. No new nodes, dependency repairs, statement correction or
statement dispute is necessary. The second reader supplies their own independent report.

The scratch probe completed without errors or warnings in both compilation phases.
All three `#print axioms` outputs list exactly `propext`, `Classical.choice`, `Quot.sound`;
there is no `sorryAx`.

## Second reading by Q28

Independent review on 2026-10-16. I opened the item and all four distinct statement/proof
 dependencies, read the entire existing upstream module (including its section context),
and independently confirmed that module using `scompile.py --source`. There is no delivered
Lean module, new node, dependency module, or stage-2 statement correction to review.
The blueprint document and Stacks checkout are absent from this machine's literature tree.
I therefore retrieved the official Stacks `derived.tex` into scratchpad and read the actual
source at `definition-triangle`, `definition-triangulated-category`,
`definition-exact-functor-triangulated-categories` (including its following paragraph about
2-morphisms), and `lemma-third-isomorphism-triangle`. These are the places the node's proof
cites. They assume additive categories with an additive shift autoequivalence and the stated
pretriangulated axioms; no scheme, coefficient, finiteness or characteristic condition occurs.
The corresponding official pages are [0144](https://stacks.math.columbia.edu/tag/0144),
[014V](https://stacks.math.columbia.edu/tag/014V), and
[014A](https://stacks.math.columbia.edu/tag/014A).

My list of the node's objects, hypotheses and conclusions, matched individually:

1. Two triangulated categories C and D. Lean has `{C D : Type*}`, independent
   `[Category* C] [Category* D]`, and on each category `[HasZeroObject]`, `[Preadditive]`,
   `[HasShift _ ℤ]`, additive integer shifts and `[Pretriangulated]`. I read the recorded
   Mathlib classes: `Pretriangulated` has exactly TR1--TR3; `IsTriangulated` adds TR4.
   Verdict: every triangulated category of the node is covered. The reusable existing
   theorem requires only the pretriangulated structures and specializes to the node;
   its unused octahedral axiom need not be supplied as a theorem argument.
2. Exact functors Φ and Ψ with specified natural shift isomorphisms. Lean has
   `{F₁ F₂ : C ⥤ D}`, `[F₁.CommShift ℤ] [F₂.CommShift ℤ]`, and
   `[F₁.IsTriangulated] [F₂.IsTriangulated]`. Their degree-one isomorphisms are
   `(F₁.commShiftIso (1 : ℤ)).app X` and `(F₂.commShiftIso (1 : ℤ)).app X`.
   I read `Functor.IsTriangulated.map_distinguished` and its additivity instance.
   Verdict: exact match; additivity is derived, not an extra premise.
3. A natural transformation α:Φ→Ψ. Lean has `(τ : F₁ ⟶ F₂)`.
   Verdict: same object, including naturality for all arrows; no global `IsIso τ` premise.
4. For every X, compatibility with the given shift isomorphisms. Lean has
   `[CategoryTheory.NatTrans.CommShift τ ℤ]`. I read `CommShift.shift_comm`,
   `shift_app_comm`, `Functor.commShiftIso_zero` and `Functor.commShiftIso_add`.
   At degree one the equation is
   `(F₁.commShiftIso 1).hom.app X ≫ (τ.app X)⟦1⟧' =
    τ.app (X⟦1⟧) ≫ (F₂.commShiftIso 1).hom.app X`.
   Verdict: reversing equality and translating forward composition gives exactly the
   node's ψ_X∘α_{X[1]} = α_X[1]∘φ_X. Integer compatibility adds no mathematical
   condition: positive powers follow inductively from the addition coherence,
   degree zero from naturality and the unit coherence, and negative powers from the
   inverse shift. More explicitly, evaluate compatibility for n>0 on X[-n], identify
   X[-n][n] with X, and cancel the invertible shift comparisons; this is compatibility
   for -n. This reasoning does not assume that τ is invertible.
5. Every distinguished triangle T=(X→Y→Z→X[1]). Lean has `{T : Triangle C}` and
   `(hT : T ∈ distTriang C)` before the pairwise hypotheses. I read the recorded
   `Triangle` and `TriangleMorphism` signatures in Mathlib Basic: the third arrow lands
   in `T.obj₁⟦(1 : ℤ)⟧`, and the third square involves the shifted first component.
   Verdict: all objects, arrows, distinguishedness and quantifier order agree.
6. Pair (X,Y) invertible implies Z invertible. The recorded main lemma has
   `(h₁ : IsIso (τ.app T.obj₁)) (h₂ : IsIso (τ.app T.obj₂)) :
    IsIso (τ.app T.obj₃)`.
   Verdict: exact; the JSON `lean.statement` is verbatim the source signature.
7. Pair (X,Z) invertible implies Y invertible. The second entry of `lean.declarations`,
   `isIso_app_obj₂_of_isIso_app_obj₁₃`, takes the first/third `IsIso` hypotheses and
   concludes `IsIso (τ.app T.obj₂)`. Verdict: exact.
8. Pair (Y,Z) invertible implies X invertible. The third entry,
   `isIso_app_obj₁_of_isIso_app_obj₂₃`, takes the second/third `IsIso` hypotheses and
   concludes `IsIso (τ.app T.obj₁)`. Verdict: exact. These exhaust the node's three pairs.

I independently read the dependency `NatTrans.mapTriangle` and the three Mathlib
triangle-morphism two-out-of-three lemmas, not just their names. Proof step 1 is implemented
by `F₁.map_distinguished T hT` and `F₂.map_distinguished T hT`; step 2 by
`(NatTrans.mapTriangle τ).app T`, whose first two squares use naturality and whose third
uses degree-one shift compatibility followed by naturality of `T.mor₃`; step 3 by
`isIso₃_of_isIso₁₂`, `isIso₂_of_isIso₁₃`, or `isIso₁_of_isIso₂₃` with both distinguishedness
proofs. Thus the existing proofs follow the node step by step. No private notion, hollow
definition, new theorem proof, or postponed theorem is introduced. The existing docstrings
identify this blueprint item; the read-only upstream source is reused without rewriting it.

Edge cases: the zero category, zero triangle and contractible triangles are included;
there is no nonzero-object assumption. Rotation and inverse rotation give the other pairs,
including negative shifts. Degree zero is normalized by the shift unit. The elaborated
checks show four independent category object/morphism universes, with no size equality.
An actually empty category cannot satisfy `HasZeroObject`, just as it cannot be additive
in the source; this is intrinsic to the setting. There is no index set, scheme, integer
bound, characteristic or coefficient ring whose edge case could be silently excluded.

Independent searches, using queries different from the first reader's:

- LeanFinder via msearch: `componentwise isomorphism natural transformation exact functors
  distinguished triangle`; eight hits, including `Functor.mapTriangleIso` and
  `Triangle.functorIsoMk`, but no exact componentwise transformation theorem.
- Loogle via msearch: `CategoryTheory.Pretriangulated.Triangle, IsIso`; zero hits because
  the service reports unknown identifier `IsIso`. This is not evidence of absence.
- LeanSearch via msearch: `natural transformation of triangulated functors invertible on
  two vertices of distinguished triangle`; unavailable, Internal Server Error.
- msearch grep: `isIso.*app.*obj|shift.*compatib|mapTriangleIso`; hits concern shift
  compatibility and triangle isomorphisms. Direct `rg` of Mathlib Triangulated with
  `isIso.*of_isIso|mapTriangleIso` finds the generic triangle-morphism lemmas and
  `mapTriangleIso`, which assumes an already invertible natural transformation.
- Direct `rg` of upstream WeilConjectures and project Sheaf with `NatTrans.*isIso`,
  `isIso_app_obj`, `two.out.of.three`, and the item id finds the exact three upstream
  lemmas in the recorded module. The upstream Generators module uses the second one;
  no project module supplies a duplicate statement requiring replacement.

Mismatches found: none in the node's Lean record or the three existing declarations.
Changes: appended this independent reading only; retained the existing-declaration record
and all mathematical fields verbatim. No statement dispute remains.

Validation: reran `scompile.py Q28 lem-sf-triangle-two-out-of-three` on the absolute path
of `scratchpad/ExistingChecks.lean`. Both compilation phases passed without errors or
warnings; all three elaborated signatures have every variable and universe bound.
All three axiom checks list only `propext`, `Classical.choice`, and `Quot.sound`.
