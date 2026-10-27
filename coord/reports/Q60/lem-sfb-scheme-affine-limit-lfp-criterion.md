## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyFinitePresentationAffineLimitCriterion`
states `AlgebraicGeometry.locallyOfFinitePresentation_iff_affine_limit_hom_bijective`,
with proof `sorry`. It introduces no definitions or additional nodes. The node's
statement, dependencies, six-step proof and independent stage-1 review are preserved;
only its `lean` field changes. The earlier BLOCKED ending confused an accepted
stage-1 split with completion of stage 2. The live node has no Lean record, and the
stage-handoff paragraph of `coord/brief-stage2.md` expressly authorizes this work.
`coord/queue.tsv` also lists this item at stage 2. No repair note was present.

Source read: `literature/stacks-project/limits.tex`, proposition
`proposition-characterize-locally-finite-presentation`, Tag 01ZC, statement and proof
of equivalence (1) and (2). In particular this source imposes no global finiteness
condition on the morphism's source or base. The Lean declaration's docstring gives
the accepted node's complete six-step proof plan and names the dependencies used
by each step. Nothing is proved in this delivery.

The correspondence of every hypothesis and clause is as follows:

| Node text | Lean rendering |
| --- | --- |
| Schemes B and U | `{B U : Scheme.{u}}` |
| Morphism g : U -> B | `(g : U ⟶ B)` |
| Size convention | Explicit `universe u`; stages, base and target use `Scheme.{u}`, and the small index type is `I : Type u`. Hom sets and their colimit use Mathlib's inferred type universe. |
| g locally of finite presentation | `LocallyOfFinitePresentation g`, the recorded Mathlib notion |
| If and only if | The outer `↔`, with the entire test property on its right |
| Every small nonempty directed set | `∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`; the project's directed-set convention uses a preorder. |
| Inverse system of B-schemes | `(D : Iᵒᵖ ⥤ Over B)`; the structure maps and commuting triangles are part of Mathlib's over category. |
| All stage schemes affine | `(∀ i : Iᵒᵖ, IsAffine (D.obj i).left) →` |
| Limit T of that system, over B | `∀ c : Cone D, IsLimit c →`; its vertex is `c.pt : Over B` and the projections are `c.π.app i`. |
| Set Mor_B(T_i,U) | The value at `i : I` of `D.rightOp ⋙ yoneda.obj (Over.mk g)` is `D.obj (op i) ⟶ Over.mk g`. This is the type of morphisms commuting with the structure maps to B, not all scheme maps. |
| Forward transition maps on Hom sets | `D.rightOp` reverses the inverse system and `yoneda.obj (Over.mk g)` precomposes with its transition morphisms. |
| Filtered colimit of sets | `colimit (D.rightOp ⋙ yoneda.obj (Over.mk g))`; nonempty directedness makes I filtered (`isFiltered_of_directed_le_nonempty`). Type-valued colimits exist without an added hypothesis. |
| Canonical map to Mor_B(T,U) | `colimit.desc (D.rightOp ⋙ yoneda.obj (Over.mk g)) ((yoneda.obj (Over.mk g)).mapCocone (coconeRightOpOfCone c))` |
| Bijective | `Function.Bijective` of precisely that canonical map |
| No qc or qs assumptions on B or U | There are no such binders; affineness is assumed only for the stages. |

For the canonical-map clause, `coconeRightOpOfCone c` has vertex `op c.pt`
and leg `(c.π.app (op i)).op`. Yoneda sends that leg to precomposition with
the projection. Consequently the canonical map sends the colimit class of a
stage map `a_i` to `c.π.app (op i) ≫ a_i`, exactly as in the node. No arbitrary
map, equivalence or existential bijection replaces the canonical map.

Limits in `Over B` are the intended relative limits: for the nonempty directed
index the diagram is connected, and the forgetful functor creates these limits.
Equivalently the underlying scheme limit gets its unique compatible B-structure.
Quantifying over every limiting cone avoids choosing a new limit construction.
The recorded `exists_limit_affine_transition` provides the underlying scheme
limit, since transitions between affine stages are affine; hence the limiting-cone
binder does not make the criterion vacuous or impose a new existence condition.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`, including their full declarations/docstrings.
  Available publicly through the finite-presentation and limit dependencies.
- `def-weil-size-convention`: the recorded convention has no declaration; the
  explicit universe and index binders implement it.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, public import.
- `lem-weil-pbc-limit-affine-transition`:
  `AlgebraicGeometry.exists_limit_affine_transition`,
  `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`, public import;
  the full theorem and its affine-stage clause were read. No private copy is made.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`, `Cocone`,
  `IsColimit`, `colimit.desc`, in `Mathlib.CategoryTheory.Limits.HasLimits`,
  and filteredness in `Mathlib.CategoryTheory.Filtered.Basic`. The latter is
  exposed by the affine-transition limit dependency. `colimit.desc` is used directly.
- Standard construction API: `CategoryTheory.Over.mk`,
  `CategoryTheory.yoneda`, `Functor.rightOp`, `Functor.mapCocone`,
  `CategoryTheory.Limits.coconeRightOpOfCone`. Their definitions were read;
  these existing constructions supply all the required data.

Imports for stated proof dependencies are plain imports of
`Mathlib.AlgebraicGeometry.AffineScheme`, `GammaSpecAdjunction`,
`Morphisms.FiniteType`, `Morphisms.QuasiSeparated`, `AffineTransitionLimit`,
and `OpenImmersion`. These cover the recorded affine qcqs, spectrum/colimit,
forward factorization, eventual equality and eventual open-containment leaves.
The newly split proof prerequisite
`lem-sfb-algebra-directed-hom-finite-presentation` has no Lean declaration yet,
so no nonexistent import was added. It occurs only in the proof plan, not in the
signature, and is not needed to state the item.

Edge cases checked before writing:

- Empty I is excluded explicitly, as the node requires; no chosen initial stage
  or distinguished element is demanded. Directedness need not be linearity.
- The singleton system reduces the map to its single-stage Hom identification.
- Empty affine stages (spectra of the zero ring) and an empty limit are allowed;
  there is no nonemptiness hypothesis on schemes or their underlying spaces.
- Empty U is allowed: there are no maps from a nonempty test scheme, while
  the empty scheme has its unique morphism. Eventual emptiness of an affine
  limit system is compatible with the forward theorem, not excluded by a binder.
- Empty B forces its over-schemes, including U, to be empty, and the same
  canonical construction still applies.
- Arbitrary non-quasi-compact and non-quasi-separated U and B are included.
- I has the schemes' universe as required by the size convention; it is not
  an unrelated smaller universe that might make the converse vacuous.

Searches for existing statements (all before finalizing the module):

- `msearch.py`, LeanFinder: "A scheme morphism is locally of finite presentation
  if and only if relative Hom commutes with directed limits of affine schemes".
  Eight hits: the finite-presentation class, its affine-chart characterization,
  appLE, composition, and related instances. None states the affine-limit iff.
- `msearch.py`, Loogle: `"LocallyOfFinitePresentation", "IsLimit"`.
  No hits.
- `msearch.py`, grep in Mathlib/AlgebraicGeometry:
  `locallyOfFinitePresentation_iff|coyoneda.*[Cc]olimit|affine.*limit.*criterion`.
  Two hits: the affine-chart characterization and its use in Etale; neither matches.
- `msearch.py`, LeanSearch: "A scheme morphism is locally finitely presented
  precisely when its relative Hom functor commutes with directed inverse limits
  of affine schemes". Eight hits: the class, constructor, affine-local ring property,
  smoothness, and a general categorical finitely-presentable property; no criterion
  for scheme morphisms as in this node.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `locallyOfFinitePresentation`, `FinitePresentation`, `AffineLimit`, and the full
  new declaration name. Found related descent and forward factorization results,
  but no full equivalence. `grep -rn` for the item's blueprint id in
  `lean/WeilConjectures` found no matches.
- Read `Mathlib.AlgebraicGeometry.AffineTransitionLimit`'s
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` in full signature:
  it is the forward factorization clause only, and cannot replace the iff.

There is no statement dispute, statement correction, new node, or dependency
interface repair. Auto-bound implicits are disabled in the delivered file.

Validation: the initial server compile passed in both sandbox and library modes.
The final file, including `set_option autoImplicit false`, is validated by the
required server dry run and delivery wrapper.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
