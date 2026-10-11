## Worker report

The module defines the statement
`CategoryTheory.brownCohomologicalRepresentability` for a triangulated category
`C` with set-indexed coproducts. Its hypotheses and their Lean renderings are:

- `C` is a category with zero object, integer shift, preadditive and
  pretriangulated structures, a triangulated structure, and coproducts indexed by
  `Type w`, rendered by the explicit typeclass binders on `C`.
- Compact generation is the dependency declaration
  `CategoryTheory.IsCompactlyGeneratedTriangulated C`, rendered by `hC`.
- The contravariant cohomological functor is
  `H : Cᵒᵖ ⥤ AddCommGrpCat.{v}` with the instance `[H.IsHomological]`; this is
  Mathlib's homological formulation of the node's cohomological functor on
  `Cᵒᵖ`.
- Sending set-indexed coproducts to products is rendered by
  `hH : ∀ (I : Type w), PreservesLimitsOfShape (Discrete I) H`; products in
  `Cᵒᵖ` are coproducts in `C`.

The conclusion, `∃ G : C, Nonempty (H ≅ preadditiveYoneda.obj G)`, gives an
object `G` and a natural isomorphism whose component at `op c` is the additive
group of morphisms `c ⟶ G`, exactly the node's `H(c) ≅ Hom_C(c,G)` clause.
The proof is intentionally `sorry` for stage 2.

Dependencies used: `CategoryTheory.IsCompactlyGeneratedTriangulated` from
`Sheaf.CategoryTheory.CompactlyGenerated`; `CategoryTheory.Pretriangulated`
from Mathlib's `CategoryTheory.Triangulated.Pretriangulated` (via the recorded
Mathlib match); `CategoryTheory.Abelian` from
`Mathlib.CategoryTheory.Abelian.Basic`; and
`CategoryTheory.Functor.IsHomological` from
`Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`. The additive Yoneda
notion is Mathlib's `CategoryTheory.preadditiveYoneda` from
`Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`.

Edge cases checked: `I` is an arbitrary `Type w`, including the empty index type;
the coproduct family can therefore be empty. No nonzero, nonempty, or
characteristic hypothesis is added, and all universes are explicit. The zero
category and zero functor are not excluded by the statement. The opposite shift
and pretriangulated instances are enabled with
`open CategoryTheory.Pretriangulated.Opposite`.

Searches made: `msearch.py leanfinder` for “Every cohomological functor from a
compactly generated triangulated category that sends coproducts to products is
representable” found only Mathlib homological and additive-Yoneda declarations;
`msearch.py loogle` for `Triangulated.HasCoproducts, PreservesCoproducts,
IsRepresentable` found no result (and reported unknown `Triangulated.HasCoproducts`);
`msearch.py grep` for `cohomological.*functor|representable.*coproduct` in
`Mathlib/CategoryTheory` found no Brown theorem; `msearch.py leansearch` for
Brown representability reported the service unavailable; `rg` over
`WeilConjectures` and `lean/Sheaf`, plus a node-id grep, found no existing
Brown declaration. The node's recorded searches have the same results.

The first remote compile was blocked because the server had not built the
landed dependency `Sheaf.CategoryTheory.CompactlyGenerated`. A temporary
stand-in for that dependency compiled the theorem signature cleanly; the final
file restores the recorded dependency import.

## Earlier second reading (a previous round; superseded)

I reread the node statement, Tag 0A8F, and the module. The explicit category
typeclasses render the triangulated category with set-indexed coproducts; `hC`
renders compact generation; `H` and `[H.IsHomological]` render the contravariant
cohomological functor to abelian groups; and `hH` renders preservation of the
products corresponding to every `Type w`-indexed coproduct. The existential `G`
and natural additive Yoneda isomorphism render representability objectwise as
`H(c) ≅ Hom_C(c,G)`. No hypothesis or conclusion clause was added or dropped,
and empty index sets, zero objects, and arbitrary characteristics remain
allowed. The temporary compile check found no elaboration errors; no statement
change was needed.

## Second reading by E1

I opened the node `lem-pc-brown-cohomological-representability`, its source
reference (Stacks Project, Derived Categories, Tag 0A8F, Lemma `lemma-brown`),
the dependency records, and
`lean/Sheaf/CategoryTheory/BrownCohomologicalRepresentability.lean`.

The node statement, item by item, is rendered as follows:

- The object `C` is a triangulated category with set-indexed coproducts. The
  module binds `C : Type u`, `[Category.{v} C]`, `[HasZeroObject C]`,
  `[HasShift C ℤ]`, `[Preadditive C]`, shift additivity, `[Pretriangulated C]`,
  `[IsTriangulated C]`, and `[HasCoproducts.{w} C]`. Verdict: exact; the
  compact-generation dependency uses this same ambient structure.
- Compact generation is `hC : IsCompactlyGeneratedTriangulated C`, using the
  recorded project declaration. Verdict: exact, with no extra finiteness or
  nonemptiness assumption.
- The contravariant cohomological functor is `H : Cᵒᵖ ⥤ AddCommGrpCat.{v}`
  with `[H.IsHomological]`. Verdict: exact Mathlib formulation.
- Preservation of coproducts as products is `hH : ∀ (I : Type w),
  PreservesLimitsOfShape (Discrete I) H`. Limits in `Cᵒᵖ` are opposites of
  coproducts in `C`, so this is the stated product condition for every index.
- The conclusion is `∃ G : C, Nonempty (H ≅ preadditiveYoneda.obj G)`, the
  natural isomorphism with components `H(c) ≅ Hom_C(c,G)`. Verdict: exact.

Edge cases were checked: `Type w` includes the empty index type; no zero,
nonzero, empty-category, characteristic, or `n = 0` restriction is present;
the zero category and zero functor remain allowed; and all universes are
explicit and unconstrained beyond the node's levels.

The existing-declaration searches were checked against Mathlib's additive
Yoneda and `Functor.IsHomological`, the project source and `lean/Sheaf`, and
the DAG node-name index. They provide ingredients only; no Brown
representability declaration exists. The recorded LeanSearch, Loogle/
LeanFinder, and grep results in the worker report are consistent with this.

No mismatch was found and no code or node statement required repair. The
module compiles with `scompile.py`; its only proof is the permitted `sorry`.
