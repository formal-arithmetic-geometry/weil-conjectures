## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveCurveIsomGraphs` states
`AlgebraicGeometry.exists_projective_curve_isom_graphs`. Its only postponed proof
is this named theorem, with the nine-step DAG proof included in the docstring.
There are no new definitions, dependency repairs, or statement corrections.
Only the item's `lean` field is changed.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X, Y and locally Noetherian S | `{S X Y : Scheme.{u}} [IsLocallyNoetherian S]` |
| Structure morphisms X to S, Y to S | `(f : X ⟶ S) (g : Y ⟶ S)` |
| Projective, with the blueprint's finite-projective-space convention | `[IsHProjective f] [IsHProjective g]`, the exact recorded upstream class |
| Both flat | `[Flat f] [Flat g]`; Mathlib `Flat.iff_flat_stalkMap` identifies these with the stalkwise definition |
| Both finitely presented | For each of f and g: `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`, exactly the dependency's finite-presentation comparison convention |
| Every geometric fibre has dimension at most one | `hX` and `hY` quantify over every `s : S`, use the recorded pullback along `Spec (AlgebraicClosure (S.residueField s))` to S, and bound `topologicalKrullDim` by 1 |
| Representative J over S | `∃ J : Over S` |
| J separated and finitely presented over S | `IsSeparated J.hom ∧ LocallyOfFinitePresentation J.hom ∧ QuasiCompact J.hom ∧ QuasiSeparated J.hom` |
| All T-points correspond bijectively to T-isomorphisms of the base changes | `∃ e : ∀ T : Over S, (T ⟶ J) ≃ (Over.mk (pullback.fst T.hom f) ≅ Over.mk (pullback.fst T.hom g))` |
| Pullback along morphisms of S-schemes | First conjunct: for every `h : T' ⟶ T` and `a : T ⟶ J`, the square of underlying isomorphisms commutes with `((Over.pullback f).map h).left` and `((Over.pullback g).map h).left`; the point pulls back to `h ≫ a` |
| A point gives a closed subscheme of X_T times_T Y_T | Second conjunct: a scheme D and closed immersion `i : D ⟶ pullback (pullback.fst T.hom f) (pullback.fst T.hom g)` with `IsClosedImmersion i` |
| Both restricted projections are isomorphisms | Isomorphisms `p : D ≅ pullback T.hom f` and `q : D ≅ pullback T.hom g`, together with `i ≫ pullback.fst _ _ = p.hom` and `i ≫ pullback.snd _ _ = q.hom` |
| Recover the associated isomorphism by inverse first projection and second projection | `p.inv ≫ q.hom = (e T a).hom.left`; composition in Lean is left to right |
| Conversely these closed subschemes give exactly the points | Third conjunct: every such `i`, `p`, `q` determines `∃! a : T ⟶ J` satisfying the same inverse-projection formula |
| The bijections commute with arbitrary base change | The naturality conjunct quantifies over every S-scheme morphism h, without any condition on T or T'. For any new base S' to S and T over S', compose T to S' to S and use the same e. The pullback universal property identifies its domain with Hom over S' from T to J times_S S', and identifies T times_S X with T times_S' (S' times_S X), likewise Y. Naturality for all h gives compatibility of these bijections, with the same graph and recovery formula, for every S', including non-Noetherian S'. |
| No stability, smoothness, connectedness, marking assumptions | None appears in the binders |

The base-change factors are written `T ×_S X`, as in Mathlib's `Over.pullback`,
rather than `X ×_S T`. This is the same base change with its two projections
exchanged by the canonical pullback symmetry. The projection to T is consequently
`pullback.fst T.hom f`. Isomorphisms in `Over T.left` include the required structure
map compatibility and inverse, so these are exactly T-isomorphisms, not arbitrary
isomorphisms of schemes. The graph data represent a closed subscheme by an actual
closed immersion rather than a choice of a set of points. The two projection
equalities and `p.inv ≫ q.hom = e` imply `i = (id,e) ∘ p`, by the pullback universal
property. Thus the subscheme is precisely the graph, uniquely up to isomorphism
of its source; the existential presentation does not permit a different graph.
The converse quantifies over all such subschemes, not merely the chosen graphs.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (all affine section rings Noetherian).
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective` (finite coordinate type and a closed immersion).
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`, with the recorded stalkwise equivalence.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`; finite presentation also uses
  the recorded quasi-compact and quasi-separated convention.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-geometric-fibre`: the recorded specialization of
  `CategoryTheory.Limits.pullback` using `AlgebraicClosure`,
  `Scheme.residueField` and `Scheme.fromSpecResidueField`, exactly as its lean.note.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, valued in `WithBot ℕ∞`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  `pullback.fst`, `pullback.snd`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  its recorded separatedness notion `AlgebraicGeometry.IsSeparated`, publicly
  imported by the upstream projectivity module. Its `IsProper` clause is used in
  the proof plan, not imposed on the representing scheme.
- Naturality additionally uses Mathlib's canonical
  `CategoryTheory.Over.pullback` from
  `Mathlib.CategoryTheory.Comma.Over.Pullback`, whose full definition was read.

All currently recorded proof-dependency modules are imported, as plain imports
where used only in the proof: ProjectiveBaseChange, ProjectiveSpace.Product,
Modules.Invertible, CurveDegreeTensorAdditive, Cohomology.Defs, and the relative
scheme representability criterion. Mathlib Noetherian, finite-presentation,
proper/separated and pullback APIs provide the recorded Mathlib leaves;
Mathlib.AlgebraicGeometry.Gluing supplies the morphism-gluing leaf. The following
proof nodes have no recorded module in the read clone and therefore have no
import yet: lem-sfb-proper-flat-sheaf-euler-local-constancy,
lem-sfb-projective-hilbert-polynomial-representability,
lem-sfb-graphs-open-in-hilbert,
lem-sfb-projective-coordinate-ring-euler-polynomial. They are proof dependencies,
not missing notions needed to type this statement. Their uses remain documented
in the theorem's proof docstring, for the maintainer to add imports when stated.

Sources read: `literature/stacks-project/moduli-curves.tex`, the complete 0DSQ
proof, in particular its numerical boundedness calculation; `quot.tex`, 0D01 and
0D1B and the preceding graph recovery paragraph; `moduli.tex`, 0DPN and 0DPP.
These support the unchanged nine-step scheme-realization proof recorded in the
DAG. The example's old Sheaf CompactObject module is withdrawn, so I also read
its node's current upstream module, WeilConjectures.CategoryTheory.CompactObject.

Edge cases checked before writing:

- Empty S: geometric-point binders are empty; the representative is empty.
- X and Y empty over S: their isomorphism functor is terminal, represented by S.
- Empty or zero-dimensional geometric fibres are included: dimension of the
  empty space is bottom, so the bound is an inequality rather than equality 1.
- Only one empty fibre: there is no isomorphism there; the statement does not
  assert that J has a point on every fibre.
- Nonreduced, disconnected, singular fibres and nonreduced test schemes: no
  reducedness, connectedness, smoothness or stability assumption appears.
- Identity test morphisms and arbitrary composite test morphisms are included
  in naturality; the canonical maps come from the actual pullback functor.
- All schemes and all tests use the same scheme universe u, with geometric
  closures of residue fields also in u. There is no independent smaller test
  universe or bounded test-field quantifier.
- The graph equations use the full scheme morphisms and their inverses, so
  nilpotent structure is retained.

Searches for an existing statement:

- `msearch.py ... leanfinder "The isomorphism functor of projective flat finitely
  presented curves is represented by a separated scheme of finite presentation"`:
  8 hits, including Proj.isSeparated, IsSeparated.respectsIso and
  UniversallyOpen.of_flat. None represents this functor or states this theorem.
- `msearch.py ... loogle '\"AlgebraicGeometry\", \"Isom\"'`: 12 hits, including
  SheafedSpace.isoMk, isomorphisms_eq_stalkwise and IsClosedImmersion instances;
  no isomorphism scheme theorem.
- `msearch.py ... grep 'isomFunctor|IsomScheme|isomScheme|HilbertScheme'
  AlgebraicGeometry`: 0 hits.
- `rg` of the project and upstream AlgebraicGeometry directories for isomorphism
  functors/schemes, projective isomorphism theorems, and graph definitions found
  no existing statement. Existing partial-section graph constructions are a
  different operation and are not duplicated here: this module defines nothing.
- Exact node-id search in WeilConjectures had no hits. Exact declaration-name
  search in Mathlib, WeilConjectures and Sheaf had no hits.

Validation: prescribed `scompile.py O4 lem-sfb-projective-curve-isom-graphs` on the
single delivered module passed both sandbox (4.6 s) and library-mode (2.5 s)
checks with no errors or warnings. No local compilation or global build was run.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
