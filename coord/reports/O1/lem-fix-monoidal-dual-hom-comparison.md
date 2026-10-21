## Worker report

Attached the existing declaration
`CategoryTheory.Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing`
in `WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison`
(`lean/WeilConjectures/SixFunctors/Etale/Derived/GenericFibre/Comparison.lean:72–81`).
No new module, definition, theorem, or proof is introduced. Only the item's `lean`
record changes. There is no repair note for this item.

The existing source signature, copied verbatim into `lean.statement`, is:

```lean
lemma isIso_ihomComparison_app_of_exactPairing (Y X : C) [ExactPairing Y X] (Z : C) :
    IsIso ((ihomComparison G X).natTrans.app Z)
```

Its enclosing namespace is `CategoryTheory.Functor.Monoidal`. The section context
at lines 46–47 binds arbitrary categories `C`, `D`, their monoidal structures,
`[MonoidalClosed C] [MonoidalClosed D]`, `(G : C ⥤ D) [G.Monoidal]`.
The theorem's `Y`, `X`, `Z` correspond respectively to the node's dual object
`D`, source object `P`, and arbitrary object `N`. The category named `D` in the
source context is the node's target category, not its dual object.

Hypothesis and clause correspondence:

| Node | Existing Lean rendering |
| --- | --- |
| Arbitrary monoidal categories C and D | `[Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]` in the section context. |
| Specified natural bijections Hom(A tensor T,B) = Hom(T,H(A,B)) | `[MonoidalClosed C] [MonoidalClosed D]`; `Closed.rightAdj` and `Closed.adj` specify the functor and adjunction, not mere existence. `ihom A` is that chosen right adjoint to `tensorLeft A`. |
| Strong monoidal G, tensorator GA tensor GB to G(A tensor B) | `(G : C ⥤ D) [G.Monoidal]`; `Functor.Monoidal.μIso G A B` has exactly this orientation. The recorded `CoreMonoidal` dependency gives the same data via `CoreMonoidal.toMonoidal`. |
| Objects D and P | `(Y X : C)` with `Y = D`, `X = P`. |
| e : P tensor D to the unit | `ExactPairing.evaluation'` in `[ExactPairing Y X]`, with type `X ⊗ Y ⟶ 𝟙_ C`. |
| c : unit to D tensor P | `ExactPairing.coevaluation'`, with type `𝟙_ C ⟶ Y ⊗ X`. |
| Triangle for P | `ExactPairing.coevaluation_evaluation'`: `X ◁ c ≫ (α_ X Y X).inv ≫ e ▷ X = (ρ_ X).hom ≫ (λ_ X).inv`. Insert `(ρ_ X).inv` before and `(λ_ X).hom` after to obtain the node's identity endomorphism of P. |
| Triangle for D | `ExactPairing.evaluation_coevaluation'`: `c ▷ Y ≫ (α_ Y X Y).hom ≫ Y ◁ e = (λ_ Y).hom ≫ (ρ_ Y).inv`. Insert `(λ_ Y).inv` before and `(ρ_ Y).hom` after to obtain the identity of D. |
| Every N in C | Unrestricted `(Z : C)`; no boundedness or finiteness condition. |
| Specified comparison, with the displayed domain and codomain | `(Functor.LaxMonoidal.ihomComparison G X).natTrans.app Z : G.obj ((ihom X).obj Z) ⟶ (ihom (G.obj X)).obj (G.obj Z)`. |
| Comparison is the transpose of tensorator followed by G(ev) | `Functor.LaxMonoidal.ihomComparison_app_eq_curry` in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic:253–255` identifies the component with `curry (μ G X _ ≫ G.map ((ihom.ev X).app Z))`. Evaluation is the counit of the specified adjunction. |
| Comparison is an isomorphism | The conclusion `IsIso ((ihomComparison G X).natTrans.app Z)`. |
| No equivalence or exactness assumption | Neither appears in the complete section context or theorem binders. No additive, abelian, triangulated, braided, symmetric or rigid-category assumption is used; only this particular exact pair is required. |

Dependency declarations read:

- `def-sfb-monoidal-category`: Mathlib match
  `CategoryTheory.MonoidalCategory` in
  `Mathlib.CategoryTheory.Monoidal.Category:162–210`, extending the structural
  data at lines 87–110. Its pentagon, triangle, unitors and associator are the
  ones in the node. No dependency module is needed.
- `def-sfb-strong-monoidal-functor`: Mathlib match
  `CategoryTheory.Functor.CoreMonoidal` in
  `Mathlib.CategoryTheory.Monoidal.Functor:620–651`.
  Read also `Functor.Monoidal:389–393`, `εIso:404`, `μIso:411` and
  `CoreMonoidal.toMonoidal`. These are equivalent presentations of the specified
  strong monoidal structure, including its unit isomorphism and coherence.
- The proof dependency `lem-pod-closed-uncurry-laws` records
  `CategoryTheory.MonoidalClosed.uncurry_curry`, `uncurry_natural_left`,
  `uncurry_eq` in `Mathlib.CategoryTheory.Monoidal.Closed.Basic:175–194`.
  All three signatures and their surrounding chosen-adjunction context were read.

Additional interfaces checked: `ExactPairing` in
`Mathlib.CategoryTheory.Monoidal.Rigid.Basic:77–90`;
`Closed`, `MonoidalClosed`, `ihom`, `ihom.adjunction`, `ihom.ev` in
`Mathlib.CategoryTheory.Monoidal.Closed.Basic:39–93`;
and the definition and transpose formula for `ihomComparison` in
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic:105–106,253–255`.

Source check: read Stacks `cohomology.tex`, Tag 0GM7,
`lemma-pullback-internal-hom`, case (1), and `categories.tex`, Tags 0FFP/0FFQ,
`definition-dual` and `lemma-left-dual`. The latter supplies the insertion and
contraction bijections, including Hom(P tensor T,N) = Hom(T,D tensor N) in
this tensor order. The item's source explicitly cites the general upstream
comparison theorem attached here. There is no source-based correction needed.

Edge cases checked by inspecting the full interfaces: the internal Hom is an
arbitrary chosen adjoint; its evaluation and transpose use that same choice.
The dual maps are arbitrary specified maps satisfying precisely two triangles,
not an assumption that either map is invertible. No duals for other objects
are required. The unit and any zero object, when present, are not excluded;
`Z` is arbitrary, including the tensor unit. No nonemptiness assumption is
added (a monoidal category already has its unit). Source and target object and
morphism universes are independent. No commutation of tensor factors was used,
so a nonbraided category is included. General strong monoidal functors are
included without equivalence, exactness, or full-faithfulness restrictions.

Searches actually run, using `batch2/msearch.py O1` for this item:

- LeanFinder: `A strong monoidal functor between closed monoidal categories
  preserves the internal Hom comparison out of an object with an exact dual
  pairing`. Eight results, including `MonoidalClosedFunctor.comparison_iso`,
  Cartesian exponential comparisons, and `tensorRightHomEquiv`; none is the
  exact general theorem in Mathlib.
- Loogle: `"ExactPairing", "ihom"`. Zero hits.
- Mathlib grep in `CategoryTheory`:
  `isIso_ihomComparison|ihomComparison.*exactPairing|ExactPairing.*[Mm]ap`.
  Zero hits.
- LeanSearch: `A strong monoidal functor preserves the internal Hom comparison
  from an object admitting a dual`. Eight hits: `MonoidalClosedFunctor.mk`,
  `Functor.Monoidal.ofBifunctor`, `ihom`, functor-category closed structures,
  `expComparison`, `MonoidalClosed.internalHom`, and `internalHom`. These give
  related notions, not the general comparison theorem.
- `rg -n 'isIso_ihomComparison_app_of_exactPairing'` over `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: the exact theorem is present
  in upstream `GenericFibre/Comparison.lean:72`, with consumers in upstream
  `GenericFibre/InternalHom.lean` and two Sheaf modules. The upstream-name index
  does not list it. The source declaration, not an index entry, establishes it.
- `rg -n 'lem-fix-monoidal-dual-hom-comparison' lean/WeilConjectures`: zero hits.
  Thus there is no node-id annotation upstream, but the exact named statement
  was found and read directly.
- Project `lean/Sheaf` comparison searches found uses of the same upstream
  theorem, including `SixFunctors/EtaleFiniteProjectivePullbackHom.lean:112`
  and `Paper/FiniteFreeHomComparison.lean:91`; no duplicate definition is needed.

No statement dispute, new node, dependency repair or changed statement.

Validation: a sandbox-only scratch file imports the upstream module, checks the
fully explicit theorem type with universe printing, and prints its axioms,
using `scompile.py`: clean compile in both server modes (8.7 s and 9.0 s),
with four independent universe parameters and exactly `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`. The delivery wrapper additionally
checks the existing attachment on the server and runs the maintainer's stage-2
preflight.

## Second reading by O1

No independent second worker was started: this dispatcher brief forbids other
agents and assigns independent review to the maintainer. A final self-check
reopened the node, the upstream theorem, its section variables, `ExactPairing`,
and the curry formula. The table above records each hypothesis and clause.
The potentially confusing argument order was checked explicitly: upstream
`Y = D`, `X = P` gives evaluation `P ⊗ D` and coevaluation `D ⊗ P`.
The comparison is the specified map, not an arbitrary isomorphism between its
endpoints. No mismatch was found and no statement was changed.
