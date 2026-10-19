## Worker report

Existing declaration attachment only; no new Lean module and no new theorem or definition.
The item is stated exactly by
`AlgebraicGeometry.Scheme.GradedAlgebraData.PullbackData.relProjIsoPullback`, in
`WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange`. Its supporting theorem
`AlgebraicGeometry.Scheme.GradedAlgebraData.PullbackData.isPullback` is also recorded.
Only the node's `lean` field changes.

Source read: the current blueprint `literature/blueprint/main-20261015/blueprint/`
`sec-nagata-compactification/sk-lem-nagata-sketch-blowups/`
`lemma-nagata-relative-proj-base-change-arbitrary.md` and its `.proof.md` companion.
The `blueprint_update` statement agrees verbatim with this snapshot.
No repair note exists for this item. There are no statement dependencies in its node.

The audited source file is missing in the older local checkout. Following the brief,
I read the full published `BaseChange` source with `scompile.py --source`, and likewise
read its `Universal`, `Basic`, and `GradedAlgebraData` interfaces. The exact signature
copied into `lean.statement` is the source signature, with binders inherited from the
explicit source context:

```lean
universe u
variable {X X' : Scheme.{u}} (g : X' ⟶ X)
  (A : X.GradedAlgebraData) (A' : X'.GradedAlgebraData)
variable {g A A'} (D : PullbackData g A A')
noncomputable def relProjIsoPullback : A'.relProj ≅ pullback A.relProjHom g
```

Clause-by-clause comparison:

- Any schemes and any morphism `g : Y ⟶ X`: upstream names `Y` as `X'` and binds
  `{X X' : Scheme.{u}}` and `g : X' ⟶ X`, with no property instances on `g`.
  In particular, it assumes neither flatness, affineness, nor finite type.
- Graded quasi-coherent algebra on `X`: `A : X.GradedAlgebraData`. The upstream
  `Scheme.GradedAlgebraData` structure in `RelativeProj.GradedAlgebraData` supplies
  an ℕ-graded commutative algebra on every affine open, functorial graded restriction
  maps, and `isGradedBaseChangeAlong` in every degree. This is the affine-basis
  encoding of exactly the stated graded quasi-coherent algebra, not a finite-generation
  or degree-one-generation specialization.
- Coefficientwise pullback `g^* A`: `A' : X'.GradedAlgebraData` together with
  `D : PullbackData g A A'`. The structure in `RelativeProj.BaseChange` provides
  `map` on every pair of affine opens satisfying `U' ≤ g⁻¹ U`,
  `isGradedBaseChangeAlong` along `g.appLE`, and `res_map`/`map_res` compatibility.
  Thus `A'` is the pullback algebra presented by its compatible coefficientwise
  tensor-product identifications; it is not an arbitrary algebra with an arbitrary map.
  The extra name `A'` presents the object denoted `g^* A`, rather than adding a
  geometric restriction on `g` or `A`.
- Relative Proj on both bases: `A'.relProj` and `A.relProj`, constructed in
  `RelativeProj.Basic` by gluing `Proj (A.grading U)` over all affine opens;
  their structure maps are `A'.relProjHom` and `A.relProjHom`.
- Canonical isomorphism: the primary declaration has type
  `A'.relProj ≅ pullback A.relProjHom g` and is defined as
  `D.isPullback.isoPullback`. The target is `Proj_X(A) ×_X X'`, canonically the
  same fibre product as the displayed `X' ×_X Proj_X(A)` after swapping projections.
  This factor-order convention does not change the statement. The supporting
  `isPullback` states
  `IsPullback D.relProjComparison A'.relProjHom A.relProjHom g`.
- Canonicity is construction-level: `D.relProjComparison` is the colimit descent
  of `Proj.map (D.map h)` followed by the affine-chart embeddings, over pairs
  `(U', U)` with `U' ≤ g⁻¹ U`. Its restriction identity is
  `relProjι_relProjComparison`. The two proven identities
  `relProjIsoPullback_hom_fst` and `relProjIsoPullback_hom_snd` identify the
  isomorphism's projections with this comparison and `A'.relProjHom` respectively.
  This supplies the specified canonical comparison, not merely existence of an iso.

The proof inspected in the published module first establishes the affine-chart
pullback using `Proj.isPullback_map_of_isGradedBaseChangeAlong`, pastes it with
`Spec` and relative-Proj chart squares, and then checks the global square on an
open cover of `X'`. This realizes the source's localization/tensor comparison and
gluing proof, without a flatness assumption. Its final isomorphism is extracted from
that pullback square. No source or node correction is needed.

Edge cases checked in the signatures and constructions: empty schemes, the zero
algebra and algebras concentrated in degree zero (empty Proj), identity maps, and
nonflat morphisms all remain admitted. There are no nonemptiness, domain,
Noetherian, positivity of algebra generators, or finite-generation assumptions.
The universe `u` is arbitrary and shared by the schemes and their affine algebra
presentations, so it introduces no independent small test universe and does not
exclude any fixed-size instance.

Searches actually run:

- `msearch.py ... leanfinder "Relative Proj of coefficientwise pullback of a graded
  quasi-coherent algebra commutes with arbitrary scheme base change"`: eight
  Mathlib hits, all on `Proj.pullbackAwayιIso` and its projection formulas; these
  concern intersections of standard charts, not relative-Proj base change.
- `msearch.py ... loogle "AlgebraicGeometry.Proj, IsPullback"`: no hit; service
  reported unknown identifier `IsPullback`.
- `msearch.py ... grep "relProjIsoPullback|isPullback.*[Pp]roj|[Pp]roj.*[Bb]ase[Cc]hange"
  AlgebraicGeometry`: three unrelated elliptic-curve projective base-change hits.
- `msearch.py ... leansearch "Relative Proj commutes with arbitrary base change
  of schemes"`: eight hits, on affine-target morphism properties, smooth and
  affine base-change stability, and one standard-chart `Proj.pullbackAwayιIso`
  formula; no exact Mathlib relative-Proj result.
- `rg -n "relProjIsoPullback|GradedAlgebraData|lemma-nagata-relative-proj-base-change-arbitrary"`
  in the local upstream `WeilConjectures` and side `lean/Sheaf` directories:
  no upstream hits in the older checkout; side hits concern the different
  `TensorGradedAlgebraData` used for square-zero immersions.
- Required plain `grep -rn "lemma-nagata-relative-proj-base-change-arbitrary"`
  in local upstream `WeilConjectures`: no hits.
- `rg` in `dag/lean_names_upstream.json`: this item's exact declarations are
  registered as `PullbackData.isPullback` and `PullbackData.relProjIsoPullback`.
  Their current published source was then read via `scompile.py --source` as above.

Validation: `scompile.py Q99 lemma-nagata-relative-proj-base-change-arbitrary`
compiled the sandbox scratch probe cleanly, both locally and in the published-library
check. It checked the full types of both recorded declarations and their projection
identities. `#print axioms` for both declarations reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; neither depends on `sorryAx`. Delivery also
checks each recorded existing declaration through its own generated import/#check
probe. No new modules require compilation.

## Second reading by Q99

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
