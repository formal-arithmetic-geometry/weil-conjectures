## Worker report

The item is stated as `AlgebraicGeometry.picard_stack_curve_geometry` in
`lean/Sheaf/AlgebraicGeometry/PicardStackCurveGeometry.lean`. Its proof is `sorry`.
The node's mathematical statement and accepted proof split are unchanged. Its
`stmt_deps` gains only the new definition node `def-sfb-line-bundle-moduli`.

Sources read: Stacks `quot.tex`, Proposition 0D04 (`proposition-pic`) and its
preceding open-invertible-locus argument; `moduli.tex`, Lemmas 0DMB
(`lemma-pic-qs-lfp`) and 0DPJ (`lemma-pic-curves-smooth`), with the assumptions of
the Picard-stack section; `examples-stacks.tex`, Tag 0372
(`section-picard-stack`), the explicit category construction. The current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` 
`sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), was read for the
inherited supporting-input placement. The blueprint ancestor command prints no
ancestor; the new node preserves the item's null ancestor and inherited via chain.

Clause-by-clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`. The scheme morphism is `(f : X ⟶ S)`.
- Flatness: `[Flat f]`; properness: `[IsProper f]`.
- Finite presentation: `[LocallyOfFinitePresentation f]` together with properness.
  Properness already implies quasi-compactness and separatedness, hence
  quasi-separatedness. Thus the three finite-presentation conditions are present
  without an extra assumption or a lost case.
- The actual category over S-schemes is `LineBundleModuli.category f`, whose
  projection is `LineBundleModuli.forget f`. Its object field `base : Over S`
  retains the test scheme and its structure map.
- Its object field `module : (pullback f base.hom).Modules` is an actual module
  on X_T. The field `invertible : module.IsInvertible` uses precisely
  `Scheme.Modules.IsInvertible`, including the empty-scheme case.
- An arrow from A over T' to B over T has `base : A.base ⟶ B.base` and
  `iso : (Scheme.Modules.moduleBaseChange f base).obj B.module ≅ A.module`.
  This is the node's isomorphism u_X^*L ≅ L', with the same orientation.
- `identity` uses `baseChangeMap_id` and `tensorPullbackSectionId`.
  `composition` uses `baseChangeMap_comp`, `tensorPullbackSectionComp`, pullback
  of the second isomorphism, and composition with the first isomorphism.
  The data are fully written; only their category-law proof is postponed in the
  named theorem `LineBundleModuli.category_laws`, the category-law clause of the
  new definition node. No object is selected from an undetermined existence claim.
- Algebraicity is the first conjunct
  `IsAlgebraicModuliStack (LineBundleModuli.category f)`. This is the recorded
  predicate including etale descent, algebraic-space diagonal and smooth
  surjective scheme atlas. It has no fibre-dimension assumption.
- The additional fibre hypothesis is exactly
  `∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1`. These are the actual
  scheme-theoretic fibres; no geometric nonemptiness or purity is inserted.
- The resulting smoothness is
  `IsSmoothModuliStack (LineBundleModuli.category f)`. Unfolding the recorded
  definition gives a smooth surjective scheme atlas U and smooth U.hom : U → S,
  exactly the stated meaning of smoothness.
- There is no condition on f_*O_X, no chosen section, no smoothness assumption
  on f, no reducedness assumption on any fibre, and no Noetherian assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with its
  stalkwise interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (locally rank one).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`, the tensor-pullback
  functor along the canonical map between base changes. X_T itself uses
  `CategoryTheory.Limits.pullback`, with the specified projections.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionId`, and
  `tensorPullbackSectionComp`; the normalized adjunction uniquely determines
  these comparisons. This is the recorded module-pullback interface.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack` and `IsSmoothModuliStack`, whose full
  definitions and atlas projections were read.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, valued in
  `WithBot ℕ∞`, the supremum of chain lengths of irreducible closed subsets.
- The new node supplies `AlgebraicGeometry.LineBundleModuli.category`.

Plain proof imports retain the recorded plan: `coherent_stack_algebraic_lfp`,
`openStackAlgebraicLfp`, `AlgebraicSpace.flat_proper_fp_locality`,
`AlgebraicSpace.schemeSpace`, `fibre_dimension_after_base_change`,
`IsFirstOrderThickening.baseChange`, `Scheme.Hom.ker`,
`Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`,
`Scheme.exact_picard_squareZeroPicardObstruction`,
`CategoryTheory.isSmoothModuliStack_of_affine_firstOrder_lifting`, and
`topologicalKrullDimAt`, in their recorded modules. The item docstring carries
all five proof steps, including the arbitrary-base cohomology argument and the
passage from equality of Picard classes to an actual restriction isomorphism.
At the time of reading, `lem-sfb-invertible-open-in-coherent-stack` and
`lem-sfb-proper-quasicoherent-fibre-dimension-vanishing` have no Lean records.
They are proof-only dependencies, not notions needed to type this statement;
their imports are consequently absent, as permitted by the stage-2 import rule.

Edge cases checked before writing: S or X empty; empty fibres and nonsurjective
f; relative dimension zero; disconnected and nonreduced fibres; arbitrary
characteristic; arbitrary base schemes. Empty fibres have dimension minus
infinity and meet the bound. On an empty X_T the local-rank-one condition is
vacuous, which correctly includes its unique module. On a nonempty X_T a zero
module is not invertible, so the definition does not replace line bundles by
arbitrary modules. No choice of rank or dimension forces a fibre to be nonempty.
The universe u is arbitrary; test schemes and module sheaves use the project's
existing same-u scheme/module conventions, with all binders explicit.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder` with “The stack of invertible sheaves of a proper
  flat finitely presented family is algebraic and smooth for fibres of dimension
  at most one”: eight hits about smooth scheme morphisms, no Picard-stack result.
- `msearch.py ... leansearch` with “category of invertible sheaves over test
  schemes with tensor pullback isomorphisms as morphisms”: eight hits for module
  sheaves, pullbacks and sheaf categories; no such based category.
- `msearch.py ... loogle` with `"Picard", "Stack"`: zero hits.
- `msearch.py ... grep` with
  `PicardStack|picardStack|LineBundleModuli|InvertibleModuli`: zero Mathlib hits.
- `rg -n` with the same regex in the read-only project's `lean/WeilConjectures`
  and `lean/Sheaf`: no hits. Searching the item id in those source trees also
  found no existing statement. Broader line-bundle searches found ordinary
  invertible-module geometry, not a line-bundle total category.
- DAG regex search followed by JSON statement-only filtering found the current
  item/open-in-coherent theorem and unrelated line-section statements, but no
  definition node for the category. `tools/blueprint_refs.py search 'Picard stack'`
  found zero blueprint nodes; `search 'line bundles'` found eleven ordinary
  geometry nodes, none defining the category. `FlatCoherentModuli` was read:
  its objects carry finite-presentation, relative-flatness and proper-support
  constraints and it does not define the unrestricted invertible-module category.

Validation: both delivered modules compiled cleanly using the prescribed
`scompile.py NK lem-sfb-picard-stack-curve-geometry <LineBundleModuli.lean>
<PicardStackCurveGeometry.lean>`, separately in dependency order. No local/global
build was run. No statement dispute or source correction was needed.

## New nodes

`def-sfb-line-bundle-moduli` supplies the actual category needed in the item,
with module data, invertibility, pullback-isomorphism arrows, canonical identity
and composition, their laws, and projection to `Over S`. Its source is Stacks
Tag 0372, `examples-stacks.tex`, `section-picard-stack`, specialized from algebraic
spaces to schemes. It imposes no hypotheses on f. The actual Mathlib, upstream,
project and DAG searches above found no owner for this notion. The new node
records the actual LeanSearch, Loogle, Mathlib grep and project grep results.
Its four statement dependencies own the scheme, invertibility, base-change and
tensor-pullback notions; those declarations are imported and reused. Its only
postponement is the named proof that the explicitly given operations satisfy
the category laws, with a full proof docstring. This is a definition construction,
not a replacement of the item by an arbitrary fibred category.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
