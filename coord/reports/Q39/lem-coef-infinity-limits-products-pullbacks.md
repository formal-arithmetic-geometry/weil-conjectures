## Worker report

The module `Sheaf.CategoryTheory.InfinityLimitsProductsPullbacks` states
`SSet.Enhanced.infinity_limits_products_pullbacks`, with its sole proof `sorry`.
Its docstring reproduces all eight proof steps of the node, including the cited
prerequisites and the finite-cardinal case. Definitions contain real data only.
No node statement is changed and no dispute remains.

The correspondence with every hypothesis and clause is as follows.

| Node text | Lean rendering |
| --- | --- |
| Small universe U, larger universe U' | `universe u v`; the small shapes are `SSet.{u}` and the targets are `SSet.{max (u + 1) v}`. The canonical degreewise `SSet.uliftFunctor` embeds small shapes in that containing universe. No equality of universes is assumed. |
| Infinite regular small cardinal κ | `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`. Mathlib's `Cardinal.IsRegular` includes infinitude. |
| κ-small simplicial sets | The published dependency `SSet.Presentability.IsKappaSmall κ K`: `HasCardinalLT (Σ n : ℕ, K.nonDegenerate n) κ`. It counts nondegenerate simplices in all dimensions, rather than all degenerate simplices. |
| C and D quasicategories | `(C D : SSet.{max (u + 1) v}) [Quasicategory C] [Quasicategory D]`. |
| Both admit every specified limit | `hC : HasKappaLimits κ C` and `hD : HasKappaLimits κ D`. Each predicate quantifies over every small κ-small shape, every coherent diagram, and the existence of a cone satisfying the dependency's `IsLimiting`. |
| Coherent functor F | `(H : C ⟶ D)`, a simplicial natural transformation, exactly the recorded enhanced-functor convention. |
| Preserves all such limits | `PreservesKappaLimits κ H`, the left side of the equivalence. It quantifies over all the same shapes and every specified limiting cone. |
| If and only if | The theorem's `↔`; neither direction is omitted. |
| Homotopy pullbacks | `PreservesLimitsOfShape H infinityCospan`, where `infinityCospan` is the canonical lift of `nerve WalkingCospan`. Thus it is a coherent cospan diagram, and its limiting cones use the original comma-cone definition. |
| Products on every small set of size less than κ | `∀ I : Type u, Cardinal.mk I < κ → PreservesLimitsOfShape H (...)`. The shape `infinityDiscrete I` is the existing `SimplicialObject.const (Type u)` on I, canonically lifted. |
| Empty product, terminal object | The product quantifier has no `Nonempty I` assumption. For empty I its constant simplicial set is empty; a limiting cone is precisely a terminal object of C. |
| Image of each specified cone, canonical comparison respecting its legs | `PreservesLimitsOfShape` quantifies over every `t` with `IsLimiting F t` and requires a limiting `s` with `IsImageCone H F t s`. Both data coordinates are fixed: `s.1.1 = H.app _ t.1.1` and `s.1.2 = ((ihom Δ[1]).map ((ihom K).map H)).app _ t.1.2`. Thus the existential is the uniquely specified image cone, with its full transformation, not an arbitrary cone with the same apex. Its limitingness is exactly the node's preservation convention. Its comparison to any other limit is the equivalence respecting cone legs, by the terminal-object universal property; no arbitrary comparison morphism is an input. |
| κ = ℵ₀ included | There is no strict inequality `ℵ₀ < κ`. The published smallness predicate at ℵ₀ says that the total set of nondegenerate simplices is finite. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsKappaSmall`, with the entire published module read.
  This dependency had no record initially, but group NU's complete module landed
  during this work. The worker's provisional sandbox dependency module was removed;
  the delivery uses NU's published declaration and changes no dependency node.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.coneCategory`, `IsLimiting`, `IsTerminal`, and the existing
  internal-hom and coherent-transformation convention. Its full source was read.
- Mathlib's `SSet.uliftFunctor`, `SSet.nerve`, `SimplicialObject.const`,
  `CategoryTheory.Limits.WalkingCospan`, `Cardinal.mk`, and `Cardinal.IsRegular`.
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan` is imported explicitly.

Proof-only imports cover every recorded proof dependency: `RightPinchComparison`,
`EnhancedFunctorConeCalculus`, `FinalIndexColimit`, Mathlib's simplicial `Skeleton`
(`SSet.relativeCellComplexOfMono`), `InfinityColimitGluing`,
`InfinitySequentialSpine`, and `InfinityDirectedUnionLocalColimits`.
The enhanced-diagram definition is a public import as well as a proof prerequisite.

Edge cases checked mathematically before stating the result:

- The empty shape and empty product are included; no nonempty indexing condition
  or chosen terminal object is imposed.
- The one-point discrete shape is included, as are arbitrary disconnected discrete
  families below κ. Degenerate simplices do not affect their cardinal bound.
- The cospan nerve has three nondegenerate vertices and two nondegenerate edges,
  so it is κ-small for every infinite κ, including ℵ₀.
- At κ = ℵ₀ all finite simplicial shapes are tested, including shapes with
  nontrivial higher simplices; this is not a restriction to finite ordinary categories.
- Empty C or D are not silently assumed inhabited. Their stated existence-of-limits
  hypotheses themselves test the empty shape and thus imply a terminal object.
- The containing target universe can be arbitrarily larger than the small universe;
  all comparison morphisms live after canonical ULift, with no extra equality.

Searches performed (also logged by the prescribed search wrapper):

- LeanFinder: "A functor between quasicategories preserves small limits if and only
  if it preserves products and homotopy pullbacks". Eight hits were ordinary-category
  preservation results or `hoFunctor` preservation; none is this coherent statement.
- Loogle: `CategoryTheory.Limits.preservesLimits_of_preservesEqualizers_and_products,
  SSet.Quasicategory`. Zero hits.
- Mathlib grep through msearch: `preservesLimits_of_preserves|Preserves.*Pullback`
  in `CategoryTheory/Limits/Constructions`. Seventeen hits concern ordinary
  categories. Read `preservesLimits_of_preservesEqualizers_and_products` and the
  finite-limits variant: they use ordinary Category instances and strict cones.
- LeanSearch: "A coherent functor of quasicategories preserves kappa small limits
  exactly when it preserves products and homotopy pullbacks". Eight hits were
  ordinary `PreservesLimitsOfSize`, strict mapCone, and hoFunctor results; no match.
- LeanFinder: "Accessible presentable quasicategory and kappa small simplicial set
  defined by number of nondegenerate simplices". Eight hits included `SSet.Finite`,
  dimension predicates and horn filling; none was the required general definition.
- Direct rg on upstream `WeilConjectures` for this node ID returned no declaration.
  Direct rg on upstream and `lean/Sheaf` for the new names, κ-smallness,
  accessibility and quasicategories found NU's module after its concurrent landing.
  The final version uses that module. No existing preservation-of-infinity-limits
  theorem or cone-image predicate was found.

Source checked online: Lurie's `highertopoi.pdf`, Proposition the project server, printed
p. 297 (PDF p. 314), together with Corollary the project server and the skeletal argument of
the project server. The theorem is the stipulated opposite-category form, retaining the
node's existence hypotheses for both C and D. No source-based correction is needed.

Validation: the prescribed `scompile.py` wrapper successfully compiled the final
module against the landed dependency without warnings. Initial import and line-width
faults were repaired. The required `deliver2.py --no-push` dry run repeats compilation
and runs the maintainer's preflight; delivery is reserved for the second reader.

## Second reading by Q39

I reread the live node, both dependency declarations, the source passage, and the
module independently. The item-by-item correspondence is:

- The two universe levels are `universe u v`; `C` and `D` have type
  `SSet.{max (u + 1) v}`, while every test shape is `SSet.{u}` and is lifted by
  `SSet.uliftFunctor`. No universe equality or extra size hypothesis is assumed.
- The infinite regular cardinal is `(κ : Cardinal.{u})` with `hκ : κ.IsRegular`;
  Mathlib's `Cardinal.IsRegular` includes the infinite-cardinal condition.
- A κ-small shape is rendered by `SSet.Presentability.IsKappaSmall κ K`, which
  counts `Σ n : ℕ, K.nonDegenerate n` below κ, exactly the node's count.
- The quasicategories are `(C D : SSet.{max (u + 1) v})` with the two
  `[Quasicategory]` instances. The coherent functor is `H : C ⟶ D`.
- Limit existence for both categories is `hC : HasKappaLimits κ C` and
  `hD : HasKappaLimits κ D`; this quantifies over every κ-small U-shape and
  every coherent diagram and supplies a cone satisfying `IsLimiting`.
- Preservation of all such limits is `PreservesKappaLimits κ H`, whose quantifiers
  range over the same lifted shapes and every specified limiting cone.
- The conclusion is the node's `↔`: the right side tests
  `PreservesLimitsOfShape H infinityCospan` and every
  `PreservesLimitsOfShape H (ulift (infinityDiscrete I))` with
  `I : Type u` and `Cardinal.mk I < κ`.
- `infinityCospan` is the lifted nerve of `WalkingCospan`, so its limiting cones
  are precisely the coherent homotopy-pullback cones from the dependency.
  `infinityDiscrete I` is `SimplicialObject.const (Type u)).obj I`, so it is the
  required discrete product shape.
- The empty index type is included because there is no `Nonempty I` binder. Its
  empty discrete shape gives the terminal-object case. `IsImageCone` fixes both
  the image apex and the complete postcomposed coherent transformation, and
  `PreservesLimitsOfShape` requires that cone to be limiting; this is the
  canonical comparison convention in the node.
- The `κ = ℵ₀` case is included: `HasCardinalLT ... ℵ₀` means finitely many
  nondegenerate simplices, while the cospan and every finite product shape remain
  available. Zero and singleton index types are also covered.

No mismatch was found, so no Lean or node repair was needed. The module's helper
 declarations (`IsImageCone`, `PreservesLimitsOfShape`, `HasKappaLimits`,
 `PreservesKappaLimits`, `infinityCospan`, and `infinityDiscrete`) all belong to
 this statement's notion and are listed in its `lean.declarations`; none is a
 private duplicate of a dependency declaration. The dependency modules were read
 at their recorded declarations: `SSet.Presentability.IsKappaSmall` in
 `Sheaf.CategoryTheory.PresentableInfinityCategory` and
 `SSet.Enhanced.coneCategory`/`IsLimiting` in
 `Sheaf.CategoryTheory.EnhancedDiagramsCones`.

I repeated the prescribed searches with `msearch.py`: LeanFinder returned only
ordinary-category and `hoFunctor` preservation results; Loogle had no coherent
quasicategory result; and grep found no declaration of this node or its helper
notions in the source checkout or project `lean/Sheaf`. Direct searches of Mathlib
likewise found only ordinary `PreservesLimitsOfShape` APIs. I checked Lurie's
Higher Topos Theory Proposition the project server (printed p. 297, PDF p. 314), its finite
case Corollary the project server, and the construction in Proposition the project server; the source
supports the node's products-plus-pullbacks criterion and its finite-cardinal edge
case. The module compiles cleanly with the required `scompile.py` wrapper.
