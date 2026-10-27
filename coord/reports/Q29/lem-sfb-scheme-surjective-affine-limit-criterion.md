## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyFinitePresentationOfAffineLimitSurjective`
states `AlgebraicGeometry.locallyOfFinitePresentation_of_affine_limit_hom_surjective`.
Its sole theorem has proof `by sorry`; there are no definitions or auxiliary theorems.
I read the complete node, its five statement dependencies, their recorded interfaces,
and Stacks `literature/stacks-project/limits.tex`, Tag 0CM0,
`lemma-surjection-is-enough` (statement and complete proof, lines 1463–1522).
The statement agrees with that source. Only the item's `lean` field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes `B` and `U` and the morphism `g : U → B` are exactly
  `{B U : Scheme.{u}} (g : U ⟶ B)`.
- The size convention is the explicit universe `u`, shared by the scheme carriers
  and `I : Type u`. Scheme hom sets and their set colimits live in `Type u`.
  No independent smaller test universe or equality of unrelated universes is imposed.
- Every small nonempty directed set is quantified by `∀ (I : Type u) [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. This follows the project's directed-set
  convention, including preorders rather than imposing antisymmetry.
- An inverse system of schemes over `B` is `D : Iᵒᵖ ⥤ Over B`.
  The condition `∀ i : Iᵒᵖ, IsAffine (D.obj i).left` requires each stage to be an
  affine scheme, not just an affine morphism to a possibly nonaffine base.
  There is no assumption that the stage structure maps to `B` are affine.
- Its limit is any `c : Cone D` with `IsLimit c`. This quantifies over all limit
  representatives, rather than requiring equality to a chosen object. The connected
  limit creation/preservation result for `Over.forget B` in
  `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected` identifies these with
  limits of the underlying schemes. Nonempty directed indexing is connected.
  Transitions between affine schemes are affine automatically, so the recorded
  affine-transition limit theorem supplies existence without an extra assumption.
- The set `Mor_B(T_i,U)` is exactly
  `(yoneda.obj (Over.mk g)).obj (op (D.obj (op i)))`. An `Over B` morphism consists
  of a scheme morphism with its equality of composites to `B`, as seen in
  `Over.homMk`. The full diagram of these sets is
  `D.rightOp ⋙ yoneda.obj (Over.mk g)`, indexed by `I`.
- `coconeRightOpOfCone c` reverses the cone projections. Mapping this cocone by
  `yoneda.obj (Over.mk g)` gives the cocone with vertex `Mor_B(c.pt,U)` and legs
  `h_i ↦ c.π.app (op i) ≫ h_i`. Thus
  `colimit.desc (D.rightOp ⋙ yoneda.obj (Over.mk g))
  ((yoneda.obj (Over.mk g)).mapCocone (coconeRightOpOfCone c))`
  is the stated canonical comparison, built from the existing universal construction.
  It is not an arbitrary map. The colimit exists by `Limits.Types.Colimits` and
  is filtered because the index is nonempty and directed.
- The required hypothesis is `Function.Surjective` of precisely that comparison,
  universally quantified inside `hsurj`. There is no injectivity requirement.
- The conclusion is exactly `LocallyOfFinitePresentation g`.
  There are no quasi-compactness, quasi-separatedness, separatedness, or affineness
  hypotheses on `B` or `U`.

Dependency declarations used and read:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`, full signatures and docstrings at lines 35–77.
- `def-weil-size-convention`: its record is explicitly metatheoretic, with no
  declaration or module. It is rendered by the explicit universe binders above.
- `lem-weil-pbc-limit-affine-transition`:
  `AlgebraicGeometry.exists_limit_affine_transition` in
  `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`; read the full theorem
  and docstring. Its module is publicly imported. The affine-stage test diagrams
  satisfy its transition hypotheses automatically.
- `def-weil-pbc-category-colimit`: `colimit`, `Cocone`, `IsColimit`,
  `colimit.desc` in `Mathlib.CategoryTheory.Limits.HasLimits`, and `IsFiltered`
  in `Mathlib.CategoryTheory.Filtered.Basic`. Read the actual structures and the
  `to_dual` source that generates `colimit` and `colimit.desc`.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`
  in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, lines 40–54.
  This is the affine-local finite-presentation condition of the node.

The module docstring and theorem docstring cite Tag 0CM0 and the blueprint id.
The theorem docstring carries all five accepted proof steps, including affine
chart reduction, use of a stage representative, eventual containment in an arbitrary
open, restriction and base compatibility, and the directed algebra criterion.
All already stated proof dependencies are imported: `Spec`/`Spec.map` and
`Spec.reflective` from `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` (and its
public imports); `Types.jointly_surjective` and the filtered elementwise equality
lemmas from `Mathlib.CategoryTheory.Limits.Types.Filtered`; affine scheme compactness
and quasi-separatedness from `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
(and its public imports); `exists_map_eq_top` from
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`; `IsOpenImmersion` from
`Mathlib.AlgebraicGeometry.OpenImmersion`; and
`CommAlgCat.finitePresentation_of_directed_colimit_factorization` from
`Sheaf.RingTheory.FinitePresentationOfDirectedColimitFactorization`.
I read these source declarations and the complete algebra-criterion module.
No dependency module or new node is needed.

Edge cases checked before writing:

- Empty indexing is excluded exactly by the node's nonempty hypothesis. Singleton
  and arbitrary nonempty directed preorders are allowed, with no finite-stage bound.
- Empty affine schemes (`Spec` of the zero ring) and limits that are empty remain
  allowed. There is no nonempty-stage or nonempty-limit hypothesis.
- Empty `U` and empty `B` are allowed; in the latter case a morphism `U → B`
  forces `U` empty. Local finite presentation is vacuous for the empty source.
- Non-quasi-compact and non-quasi-separated source and base remain allowed.
  The proof's open inverse image need not be quasi-compact; Tag 0CM0 and
  `exists_map_eq_top` require only compact affine stages and affine transitions.
- The base need not be affine. The theorem uses the slice category, and its affine
  condition concerns underlying stage schemes only.
- The canonical comparison need only be surjective. Distinct stage representatives
  are not required to become equal by the hypothesis.
- There are no restrictions on rings, residue characteristics, or domains.

Searches actually run:

- `msearch.py ... leanfinder` with query "Surjectivity of the comparison from the
  filtered colimit of Hom into a scheme to Hom from an inverse limit of affine
  schemes implies local finite presentation": eight hits, including
  `LocallyOfFinitePresentation`, its affine-local characterization, and forward
  implications. No exact surjectivity-only converse.
- `msearch.py ... loogle` with query `"LocallyOfFinitePresentation", "Surjective"`:
  four hits about flat descent, pullback faithfulness, and effective epimorphisms;
  none states this affine-limit criterion.
- `msearch.py ... grep` with query
  `surjection_is_enough|locallyOfFinitePresentation.*[Ll]imit|[Ff]initePresentation.*[Ss]urject`
  in `AlgebraicGeometry`: four hits in Fpqc, LocalFlatDescent and
  FinitePresentation, none an exact match. Read FinitePresentation lines 40–105.
- `msearch.py ... leansearch` with query "A scheme morphism is locally of finite
  presentation if the colimit to limit comparison map on relative affine test
  schemes is surjective": eight hits, consisting of the lfp definition, its
  constructor/characterization, finite type and smoothness consequences. No match.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `surjection_is_enough|locallyOfFinitePresentation_of_affine_limit_hom_surjective|surjective-affine-limit-criterion|affine.*limit.*surjectiv`
  found only unrelated formal-completion and pro-etale surjectivity text.
- Searching the upstream tree by this item's id found no occurrence. Searches for
  canonical Hom-colimit maps found the neighboring
  `Sheaf.AlgebraicGeometry.LocallyFinitePresentationAffineLimitCriterion`.
  I read it completely. It states the equivalence with BIJECTIVITY (Tag 01ZC),
  so is not this surjectivity-only implication. Its canonical-map construction is
  the existing Yoneda/colimit construction used here; nothing is copied as a new
  definition. The desired full theorem name was also searched in
  `dag/lean_names_upstream.json`, Mathlib and both source roots; it is fresh.

Validation: the delivered file compiled through `scompile.py` in both sandbox
and library mode, with no errors or non-sorry warnings (1.3 s and 1.4 s reported).
Every binder and universe is explicit, with `autoImplicit false`, and every Lean
line is at most 100 characters. There are no statement disputes or node faults.

## Second reading by Q29

I reopened the node, Tag 0CM0, and the finished module for a second reading.
The quantified universe, nonempty directed preorder, affine underlying stages,
limit cone, relative Hom sets, and the exact precomposition comparison all match
as detailed above. `hsurj` asserts surjectivity only, and the conclusion is local
finite presentation of the original `g`. In particular the affine condition is
on `(D.obj i).left`, not on its arrow to `B`, and `Over.mk g` enforces the original
base structure rather than a freely chosen map. I checked that `rightOp` makes the
set diagram covariant in `I`, and that `coconeRightOpOfCone` supplies the correct
projection direction. The slice-limit condition is equivalent to the source's
scheme-limit condition for these connected diagrams. No hypothesis or clause
was added, omitted, or changed, and no correction was needed. This is the worker's
second reading; the independent mathematical review is the maintainer's, as the
assignment specifies.
