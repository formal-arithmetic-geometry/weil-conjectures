## Worker report

Item: lem-sfb-curve-limit-preservation. Module:
`Sheaf.AlgebraicGeometry.CurveLimitPreservation`. Main declaration:
`AlgebraicGeometry.properCurve_limit_preservation`.

Source read: `literature/stacks-project/quot.tex`, `lemma-curves-limits`
(Tag 0D55), its invocation of `lemma-spaces-limits` (0D1I), and the curve
moduli definition `situation-curves`. The module states the three explicit
clauses of the node, which are precisely essential surjectivity, fullness,
and faithfulness of the natural filtered 2-colimit functor. It does not
replace the groupoid by its set of isomorphism classes: arrows are actual
isomorphisms of presheaves over the represented base, and equality is
isomorphism equality. Only the main theorem is postponed, with `sorry`.
Its docstring contains all six proof steps of the node.

Hypothesis and clause correspondence:

- Schemes over Spec Z: `Over (Spec (.of (ULift.{u} ℤ)))`. ULift places the
  integer ring in the universe of the schemes without changing that ring
  up to its canonical ring isomorphism. `u` is explicit and arbitrary.
- Algebraic-space families: every `ProperCurveFamily T` has `space :
  AlgebraicSpace S`, the actual projection `space.obj.obj ⟶ yoneda.obj T`,
  and the existing `AlgebraicSpace.IsProperCurveFamily` proof. No source is
  restricted to be a scheme or chosen presentation.
- Flatness: the first conjunction of `IsProperCurveFamily` is
  `MapToSchemeIsLocally (@Flat) X T f`, testing all representable etale
  scheme charts with the recorded Mathlib flatness predicate.
- Properness: that predicate includes `MapToSchemeIsSeparated`, whose
  relative diagonal is representable by closed immersions;
  `MapIsQuasiCompact`; `MapToSchemeIsLocally (@LocallyOfFiniteType)`;
  and `MapToSchemeIsUniversallyClosed`. The latter tests the closedness of
  the point map after every scheme base change. For algebraic spaces this
  is equivalent to testing all algebraic-space base changes: etale scheme
  atlases are surjective quotient maps, so closedness descends from them.
  Thus the inherited interface supplies exactly the node's convention.
- Finite presentation: `MapIsQuasiCompact f`,
  `MapIsQuasiCompact (pullback.diagonal f)`, and
  `MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f`.
- Geometric fibre dimension at most one: the last conjunction of
  `IsProperCurveFamily` quantifies over every `Ω : Type u` with `Field Ω`
  and `IsAlgClosed Ω`, and every map `Spec Ω ⟶ T.left`. It requires
  `topologicalKrullDim (AlgebraicSpace.Point (pullback ...)) ≤ 1` for
  the actual geometric fibre. The existing point topology is used.
- Arrows over a fixed base are isomorphisms in `Over (yoneda.obj T)`;
  these are natural isomorphisms commuting with the projection. The helper
  `ProperCurveFamily.presheafOver` is exactly `Over.mk X.projection`.
  Cartesian base change is the existing `Over.pullback (yoneda.map f)`.
  Hence these are precisely T-isomorphisms of the underlying spaces.
- Small directed inverse system: `I : Type u`, `[Preorder I]`,
  `[IsDirected I (· ≤ ·)]`, `[Nonempty I]`, and `D : Iᵒᵖ ⥤ Over ...`.
  `D.map (homOfLE hij).op` is the transition from stage j to stage i.
  Nonempty is part of a directed inverse system; it excludes no permitted
  case. The index universe is the scheme universe, as required by the
  project size convention for inverse limits.
- Affine stages: `[∀ i : I, IsAffine (D.obj (op i)).left]`.
  Every map between two affine schemes is affine, so this already gives
  the stated affine-transition condition; no additional assumption on
  transitions is omitted. `c : Cone D`, `hc : IsLimit c` give the specified
  limit. For the connected, nonempty directed indexing category, a limit
  in Over is exactly a scheme limit with its compatible map to Spec Z.
- Object descent: first conjunct, `∀ X`, `∃ i Y`, and the nonempty type
  of isomorphisms from the canonical pullback of `Y` to `X`, over `c.pt`.
- Isomorphism descent: second conjunct allows distinct stages `i j`,
  arbitrary families `X Y`, and any limiting isomorphism `a`. It supplies
  a common `k`, proofs `hik : i ≤ k`, `hjk : j ≤ k`, and an isomorphism
  `b` of the canonical pullbacks there. The final equation identifies its
  further pullback with exactly `a`, using the specified canonical
  composition comparisons, not a freely supplied comparison.
- Eventual equality: third conjunct quantifies over every same-stage
  pair of families and every pair of isomorphisms `a b`. Equality of their
  pullbacks to the limit implies equality after pullback to some `j ≥ i`.
  Pairs represented at different stages are first moved to a common stage,
  as in the node's proof. An isomorphism's inverse is determined by its
  forward map, so isomorphism equality is exactly the asserted equality.
- Equivalence of the natural 2-colimit functor: its objects are stage
  families and its arrows are eventual stage isomorphisms modulo eventual
  equality. The first conjunct gives essential surjectivity; the second
  and third give the bijection on arrows. This is the node's explicit
  formulation of that equivalence, retaining automorphisms as arrows.

Dependencies used, with signatures/docstrings read in the source:

- `Sheaf.AlgebraicGeometry.ProperCurveModuli`:
  `AlgebraicGeometry.ProperCurveFamily` and
  `AlgebraicGeometry.AlgebraicSpace.IsProperCurveFamily`, with its
  `MapToSchemeIsLocally`, `MapToSchemeIsSeparated`,
  `MapToSchemeIsUniversallyClosed`, `MapIsQuasiCompact`, and `mapPoint`.
  This landed definition node is added to `stmt_deps`, under the explicit
  rule permitting citation of a newly landed definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace` and its etale-chart predicate.
  Imported transitively through ProperCurveModuli.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `.Separated`, `.FiniteType`,
  `.UniversallyClosed`: the recorded scheme properties used by the
  algebraic-space chart/diagonal/point definitions above.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the general categorical notion recorded
  for both fibre-product dependencies also applies to presheaves.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`,
  `Over.pullbackComp`. `ProperCurveModuli.limitBaseChangeIso` instantiates
  the latter and `eqToIso` of the cone equation mapped by Yoneda. Its data
  are fully constructed; its only proof term is simplification of that
  cone equation. Neither helper introduces an independent new notion.
- `def-weil-size-convention` is the existing metatheoretic convention,
  expressed by explicit universes, not a Lean object.

The four proof dependency nodes currently have no Lean record:
`lem-sfb-fp-space-limit-category`, `lem-sfb-space-eventually-flat`,
`lem-sfb-space-eventually-proper`, `lem-sfb-space-eventually-fibre-dimension`.
Their statements are not needed to type this statement. Their proof route
is preserved in the six-step docstring; there is no recorded module to
import yet. No missing statement dependency remains.

Edge cases checked: empty total spaces and empty geometric fibres are
allowed (`topologicalKrullDim` has bottom dimension); zero-dimensional
families are allowed (bound ≤ 1, not equality); no connectedness,
reducedness, stability or nonemptiness is imposed on curves. Arbitrary
characteristic and non-Noetherian affine bases remain allowed. Distinct
starting stages, identity isomorphisms, nontrivial automorphisms and
singleton index systems are all included. Both inverse identities are
part of the type of each descended isomorphism. No equality of unrelated
universe levels, arbitrary comparison map, or existence-selected data is
introduced.

Searches made:

1. `msearch.py ... leanfinder "Proper flat finitely presented algebraic
   space curves descend along inverse limits of affine schemes"`:
   eight scheme-level descent/approximation hits, no algebraic-space
   curve limit-preservation statement.
2. `msearch.py ... leansearch "Flat proper finitely presented algebraic
   space curves commute with directed inverse limits of affine bases"`:
   eight scheme-level affine-limit/flatness hits, no exact statement.
3. `msearch.py ... loogle "AlgebraicGeometry, IsProper, limit"`:
   no exact match. `msearch.py ... grep
   "curveStack|CurveFamily|IsProperCurve|limitPreserv" AlgebraicGeometry`
   and `... grep "IsProperCurveFamily" AlgebraicGeometry`: no Mathlib hit.
4. `rg` in `lean/WeilConjectures` for curve/limit-preservation names and
   the item id: scheme curve interfaces and other unrelated results;
   no declaration of this algebraic-space statement.
5. `rg` in `lean/Sheaf/AlgebraicGeometry` and `lean/Sheaf/CategoryTheory`
   for limit-preservation names, and the curve/space modules: located
   `ProperCurveModuli.lean`, which is reused, not copied. Searches for
   the newly introduced fully qualified declaration names found no clash.
6. `tools/blueprint_refs.py search curve` and DAG searches: the current
   theorem is the corresponding limit-preservation node; the newly
   landed `def-sfb-proper-curve-moduli` is the reusable family definition.
   No new definition node or dependency repair is needed.

Validation: scompile.py compiled both the sandbox source and its actual
module name on the live server with no errors or warnings (6.3 s and
5.0 s, respectively). All variables and the universe are explicitly bound.
There is no statement correction or STATEMENT-DISPUTED finding.

## Second reading by Q134

Worker's final rereading of the node and completed source; the dispatched
brief assigns independent review to the maintainer and forbids subagents.
The reuse of `IsProperCurveFamily` was checked conjunct by conjunct
against flatness, properness, finite presentation and geometric dimension.
The source remains an algebraic space. Object descent retains its
identification over the limit; arrow descent handles two different
starting stages and fixes the given limiting isomorphism through the
canonical composition isomorphisms. Eventual equality is conditional on
actual equality after canonical pullback and concludes actual equality
at a later stage. The same-stage expression of this last clause gives
all representatives after passing to a common stage. The comparison uses
`Over.pullbackComp` in the correct order (cone projection first, then
stage transition). The initial elaboration issue in its equation was
repaired without changing any mathematical hypothesis or conclusion.
No further mismatch was found. No independent review is claimed here.
