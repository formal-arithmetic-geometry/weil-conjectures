## Worker report

The delivery states `DerivedCategory.preaisle_transfinite_monomorphism_closure` in
`Sheaf.CategoryTheory.PreaisleTransfiniteMonomorphismClosure`, with proof `sorry`.
There are no new definitions, extra nodes, dependency repairs, or statement changes.
The theorem docstring records all six steps of the DAG's bar-skeleton proof.

The source is the current blueprint's `lem-per-artin-gabber-affine-curve.proof.md`,
Step 2 (middle t-structure existence input). I read that step: it motivates this
auxiliary assertion but does not prove it. The statement and the supplied proof are
agent-formulated, as recorded by the node, and the module says so explicitly.

Hypothesis-by-hypothesis and clause-by-clause comparison:

| Node clause | Lean rendering |
| --- | --- |
| Fixed smallness universe V, arbitrary object universe | `universe t v u`; V is `v`, objects `A : Type u`. |
| V-small Hom sets | `[Category.{v} A]`. |
| A Grothendieck abelian category, with V-small colimits | `[Abelian A] [IsGrothendieckAbelian.{v} A]`; the latter supplies `HasColimitsOfSize.{v,v}`, exact filtered colimits, and a separator. |
| Unbounded derived localization Q | `[HasDerivedCategory.{t} A]`, `DerivedCategory A`, and `Q : CochainComplex A ℤ ⥤ DerivedCategory A`. The derived morphism universe `t` is independent. |
| Strictly full subcategory V₀ | `U : ObjectProperty (DerivedCategory A)` with `[U.IsClosedUnderIsomorphisms]`; its associated full subcategory has every ambient morphism between its objects. |
| Contains zero | `[U.ContainsZero]`; with isomorphism closure this means every zero object belongs. |
| V-small coproduct closure | `hcoproducts : ∀ I : Type v, U.IsClosedUnderColimitsOfShape (Discrete I)`. This includes an empty I and does not restrict the index size to Type 0. |
| Closure under [1] | `hshift : ∀ K, U K → U (K⟦(1 : ℤ)⟧)`. It does not assume closure under [-1]. |
| Extension closure, middle object from both ends | `[U.IsTriangulatedClosed₂]`. Its definition gives membership up to isomorphism; `[U.IsClosedUnderIsomorphisms]` makes this exactly middle-object membership. |
| V-small ordinal interval β ≤ θ | `{J : Type v} [LinearOrder J] [OrderBot J] [OrderTop J] [SuccOrder J] [WellFoundedLT J]`. See the equivalence of encodings below. |
| Ordinal-indexed diagram of complexes | `E : J ⥤ CochainComplex A ℤ`. |
| Initial complex zero | `hzero : IsZero (E.obj ⊥)`. Categorical zero is the invariant meaning of E₀ = 0; it does not depend on the chosen zero object's representation. |
| All transition maps degreewise monic | `hmono : ∀ (i j : J) (hij : i ≤ j) (n : ℤ), Mono ((E.map (homOfLE hij)).f n)`. |
| At every nonzero limit, the specified transition cocone is a degreewise colimit | `[hcontinuous : ∀ n : ℤ, (E ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) n).IsWellOrderContinuous]`. Mathlib's definition quantifies over `Order.IsSuccLimit`, excluding the least element. The cocone is `Set.principalSegIio` applied to the given diagram, not an unrelated isomorphic object or arbitrary map. |
| Each successor quotient in U, for β < θ | `hquotients : ∀ i : J, i < ⊤ → U (Q.obj (cokernel (E.map (homOfLE (Order.le_succ i))))))`. Cokernels of complex morphisms in this abelian category are computed degreewise, so this is precisely E_{β+1}/E_β. |
| Terminal derived complex belongs to U | `U (Q.obj (E.obj ⊤))`. |
| No boundedness, compactness, or direct-summand closure imposed | No such binder appears; all complexes are ℤ-indexed and unrestricted. In particular the module uses only `IsTriangulatedClosed₂`, not `IsTriangulated` or `IsStableUnderRetracts`. |

Ordinal encoding: a small well-ordered set with a greatest element has successor
order type θ+1, hence is order-isomorphic to the interval [0,θ] for a V-small
ordinal θ. Conversely every such interval has the five displayed order structures
and a representative type in `Type v`. `SuccOrder` supplies the usual next element
below top, and fixes top; the quotient hypothesis is restricted to `i < ⊤`, so
there is no spurious final quotient. Bottom and top may coincide. This encoding
introduces no mathematical restriction and no assumption about θ's cofinality.
It avoids placing an interval directly in `Ordinal.{v}`, whose carrier is in the
larger universe. The order structures are data for the original ordinal indexing,
not extra hypotheses on the filtration.

Dependency declarations used, with signatures and docstrings read:

- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`; its defining fields,
  the `hasColimits` instance, and the specialization w=v match the node's notion.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone`, `IsColimit`,
  `colimit`, `colimit.desc` in Mathlib's `Limits.Cones`, `Limits.IsLimit`, and
  `Limits.HasLimits` modules. Continuity uses exactly `IsColimit` of the
  transition cocone; it does not assume literal equality to Mathlib's choice.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q`, their shift and triangulated instances, in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- Closure interfaces: `ObjectProperty.IsClosedUnderIsomorphisms`,
  `ObjectProperty.ContainsZero`, `ObjectProperty.IsClosedUnderColimitsOfShape`,
  and `ObjectProperty.IsTriangulatedClosed₂`, in Mathlib's corresponding
  ObjectProperty modules and `Mathlib.CategoryTheory.Triangulated.Subcategory`.
- Filtration continuity: `CategoryTheory.Functor.IsWellOrderContinuous` in
  `Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous`; degree
  evaluation is `HomologicalComplex.eval`, and quotients are `Limits.cokernel`.
- Proof import `def-sc-preorder-bar-total`: `CategoryTheory.PreorderBar.total`
  in `Sheaf.AlgebraicGeometry.PreorderBarTotal`.
- Proof import `lem-kun-grothendieck-derived-coproducts`:
  `DerivedCategory.isColimit_mapCocone_grothendieckSum` in
  `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`. This module is
  absent from the older local copy; `scompile.py --source` supplied its current
  published source and full general signature.
- Proof import `lem-kun-sequential-telescope-mono`:
  `CategoryTheory.sequentialTelescope_mono` in
  `Sheaf.CategoryTheory.SequentialTelescopeMono`, also read with
  `scompile.py --source`; its AB5 and colimit-size assumptions are Type 0.
- Proof import `lem-sc-preorder-bar-filtered-augmentation`:
  `CategoryTheory.PreorderBar.augmentation_quasiIso` in
  `Sheaf.AlgebraicGeometry.PreorderBarFilteredAugmentation`.
- Proof import `lem-weil-pbc-complex-ses-triangle`:
  `DerivedCategory.triangleOfSESδ`, `triangleOfSES`, and
  `triangleOfSES_distinguished` in `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.
- `def-weil-triangulated-category`: Mathlib's `Pretriangulated` and
  `IsTriangulated` structures; their module is already publicly imported via
  the derived-category module. Their rotation axiom is the one in proof Step 5.

All recorded proof-dependency modules are imported. Public imports supply the
statement interfaces; the bar, derived-coproduct, telescope, bar-augmentation,
and short-exact-triangle imports are ordinary proof imports. No proof import
has been omitted for an import cycle.

Edge cases checked:

- θ=0 is represented by a singleton J: bottom=top, successor hypotheses are
  empty, and the conclusion is membership of a derived zero object.
- A single successor yields exactly one quotient condition and the usual
  extension-closure conclusion. No extra condition at top is imposed.
- At θ=ω and at uncountable limit ordinals, degreewise continuity uses the
  entire strict initial segment; there is no replacement by a countable
  cofinal subsequence and no countability assumption on J.
- The zero category, zero complexes, and the subcategory of zero objects are
  permitted. Empty coproducts are included in the closure quantifier.
- Complexes may be unbounded in both directions. Only the positive shift [1]
  is required. Neither compactness nor summand closure appears.
- Arbitrary object universe u and derived morphism universe t are retained;
  the universe v is shared by the originally specified Hom and indexing sizes.

Searches made with the required tools:

- `msearch.py leanfinder`: “A cocomplete preaisle in the derived category of a
  Grothendieck abelian category contains continuous transfinite extensions of
  complexes by monomorphisms”. Eight hits concern generating monomorphisms,
  monomorphism stability, and small-object arguments in A; none states closure
  of an arbitrary preaisle in D(A).
- `msearch.py leansearch`: “A subcategory of a derived category closed under
  coproducts positive shifts and extensions is closed under transfinite
  filtrations by subcomplexes”. Eight hits supply triangulated subcategories,
  derived-category structures, and closure classes; none is this theorem.
  `ObjectProperty.IsTriangulated` would impose negative shifts, so it is not used.
- `msearch.py loogle`: “Functor.IsWellOrderContinuous,
  ObjectProperty.IsClosedUnderExtensions, IsGrothendieckAbelian”. Zero hits;
  this search service did not recognize the shortened first identifier.
  Direct source inspection found its fully qualified declaration and also
  distinguished abelian extension closure from the required triangle closure.
- `msearch.py grep` on Mathlib/CategoryTheory:
  `preaisle|transfinite.*extension|IsWellOrderContinuous|IsClosedUnderExtensions`.
  Twenty-five hits include the continuity definition and transfinite composition
  APIs; no theorem matching the item.
- `rg` in upstream WeilConjectures and the project's lean/Sheaf for
  `preaisle|transfinite.*[Cc]los|[Cc]los.*transfinite` and the item id found the
  existing parent `SetGeneratedSheafAisle`, not this general auxiliary theorem.
  The parent has stronger closure assumptions and is specific to module sheaves,
  so it cannot serve as an exact existing statement.
- `rg` for the chosen declaration name and triangle-closure interface in
  `dag/lean_names_upstream.json`, upstream, and the project found no existing
  `preaisle_transfinite_monomorphism_closure`; existing consumers confirm the
  names of the Mathlib closure interfaces.

No statement fault or mathematical dispute was found. Compilation and delivery
validation use only the prescribed `scompile.py` and `deliver2.py` wrappers.

## Second reading by Q96

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
