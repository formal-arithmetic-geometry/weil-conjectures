## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceLftDiagonalLfp` states
`AlgebraicGeometry.AlgebraicSpace.diagonal_locallyOfFinitePresentation_of_locallyOfFiniteType`.
Its only proof is `sorry`; it introduces no definitions. The statement is Stacks Tag 084P,
first assertion, read in `literature/stacks-project/spaces-morphisms.tex`, at
`lemma-diagonal-morphism-finite-type`. The node's statement and accepted proof split are
unchanged. The existing definition node `def-sfb-space-morphism-properties` is added to
`stmt_deps` so that the shared chart predicates are recorded explicitly.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`, with explicitly declared `universe u`.
- The arbitrary algebraic spaces over that base are `{X Y : AlgebraicSpace S}`.
  This is the recorded full subcategory of fppf sheaves on `Over S` with representable
  diagonal and a surjective etale scheme atlas. Its existing universes are retained.
- The morphism is `(f : X ⟶ Y)`, a natural transformation of their underlying sheaves.
- Local finite type on compatible etale charts is exactly
  `(hf : MapIsLocally (@LocallyOfFiniteType) f)`. Expanding `MapIsLocally` quantifies over
  every pair of schemes `U V : Over S`, every representable etale chart map into `X`
  and `Y`, and every commuting scheme morphism `h : U ⟶ V`, requiring
  `LocallyOfFiniteType h.left`. No global quasi-compactness condition is included.
- The target `X ×_Y X` is `Limits.pullback f.hom f.hom` in the sheaf category. The
  algebraic-space structure is supplied by
  `(fibreProduct_isAlgebraicSpace X X Y f f).1`, not by an additional hypothesis or a
  choice of an unrelated object. The closure theorem determines exactly the property
  of this already constructed sheaf.
- The map is `ObjectProperty.homMk (Limits.pullback.diagonal f.hom)`, the canonical
  diagonal sheaf map sending a section to its repeated pair.
- The conclusion is `MapIsLocallyOfFinitePresentation` of that map. This expands to
  the same all-compatible-etale-chart test with `LocallyOfFinitePresentation` on the
  chart morphism. It is precisely local finite presentation, with no quasi-compactness
  or quasi-separatedness conjunct.
- No quasi-compactness, quasi-separatedness, separatedness or Noetherian hypothesis
  appears. The assertion concerns only the first part of Tag 084P, as does the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsEtale`, `IsRepresentableWith`; the other recorded
  site/module declarations do not enter this statement.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace` supplies the property
  of the exact sheaf pullback used in the conclusion.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (and the proof-plan base-change instance
  `locallyOfFiniteType_isStableUnderBaseChange`).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally` and
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocallyOfFinitePresentation`; this existing
  definition node is added to the item's dependency list rather than duplicated.
- `def-weil-size-convention` is explicitly a convention with no declaration: the
  existing universe-polymorphic scheme and sheaf interfaces implement it here.
- The recorded proof dependency
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests` is imported
  privately. Its declaration `representable_etale_scheme_tests` was read with its
  source/proof docstring. The chart-test and relative-lfp-permanence proof nodes
  currently have no Lean records, so there are no modules for them to import. The
  scheme base-change node is already a Mathlib leaf, whose module is imported.

The docstring reproduces all four accepted proof steps: compatible atlases for `f`,
the atlas `U ×_V U` for the second projection, the identity's zero-generator and
zero-relation presentation, and relative-lfp cancellation applied to the diagonal
followed by the second projection. No extra theorem is silently postponed.

Edge cases checked before writing: empty source (no nonemptiness binder), identity
morphisms (canonical diagonal into the identity pullback), the scheme case (the chart
predicates restrict to the scheme properties), arbitrary non-Noetherian base, and
non-quasi-compact sources such as an infinite disjoint union of points over a field.
In the last case the projection need only be locally finite type. The source proof's
phrase "of finite type over X" must be read locally in this first assertion, as already
explained in the accepted split; neither the Lean nor the node asserts global finite type.
No statement dispute or correction is needed.

Searches for existing declarations:

- `msearch.py ... leanfinder "The diagonal of a locally finite type morphism of algebraic
  spaces is locally of finite presentation"`: eight hits, including
  `FormallyUnramified.isOpenImmersion_diagonal`, scheme pullback instances and the scheme
  local-finite-presentation definition; none is this algebraic-space assertion.
- `msearch.py ... loogle "LocallyOfFiniteType, LocallyOfFinitePresentation"`: zero hits;
  the service reported unknown unqualified identifier `LocallyOfFiniteType`.
- `msearch.py ... grep "[Dd]iagonal.*[Ff]inite[Pp]resentation|[Ff]inite[Pp]resentation.*[Dd]iagonal"
  AlgebraicGeometry`: zero hits.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for diagonal/local-finite-
  presentation names and for the exact item id: no existing declaration of this item.
  Upstream `locallyOfFinitePresentation_diagonal` is scheme-only and even assumes local
  finite presentation of `f`, so it is not the desired statement. Searches of the
  algebraic-space modules found the shared `MapIsLocally` predicate and its local-finite-
  presentation specialization, which are reused.

Validation: `scompile.py NP lem-sfb-space-lft-diagonal-lfp` compiled both the sandbox and
the named library module cleanly, each in 1.5 seconds, with no warnings. An initial
namespace collision with the module-pullback definition `AlgebraicSpace.pullback` was
fixed by spelling the categorical construction `Limits.pullback` explicitly.

The earlier worker's stage-1 unchanged-item refusal does not apply to this stage-2
assignment: the current node has no Lean record, and `coord/queue.tsv` queues it at
stage 2. This follows the explicit stage-handoff rule in `coord/brief-stage2.md` §0.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
