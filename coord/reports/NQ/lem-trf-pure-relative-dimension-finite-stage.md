## Worker report

The module `Sheaf.TraceFormula.PureRelativeDimensionFiniteStage` states
`AlgebraicGeometry.pure_relative_dimension_finite_stage` with a `sorry` proof.  It
formalizes Stacks Limits Tag 0EY2 (lemma-descend-dimension-d), with persistence of
pure relative dimension under later base change from Morphisms Tags 02NJ and 02NK.
The inverse system is a functor `D : Iᵒᵖ ⥤ Scheme`, its limit is a cone `c` with
`IsLimit c`, and each transition is represented by `IsAffineHom`.  The stage and
limit base changes are the canonical `CategoryTheory.MorphismProperty.Over.pullback`
objects and their mapped morphisms.

The Lean signature renders every clause as follows.

* `I : Type u`, `[Preorder I]`, `[IsDirected I (· ≤ ·)]`, and `[Nonempty I]` express
the nonempty directed index set.
* `D : Iᵒᵖ ⥤ Scheme.{u}` is the inverse system.  The quantified
`[∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]` gives affine transition maps.
* `[∀ i, CompactSpace (D.obj i)]` and `[∀ i, QuasiSeparatedSpace (D.obj i)]`
express that every stage is quasi-compact and quasi-separated.  `c : Cone D` and
`hc : IsLimit c` provide the limit scheme and its projections.
* `i₀ : I`, `X₀ Y₀ : Over (D.obj (op i₀))`, and `f₀ : X₀ ⟶ Y₀` give the
morphism over the chosen stage.  The four compact/quasi-separated typeclass
binders on `X₀.left` and `Y₀.left` give the qcqs hypotheses, and
`[LocallyOfFinitePresentation f₀.left]` gives local finite presentation.
* `d : ℕ` is the nonnegative dimension.
* `hpure` quantifies over every point `z` of the target of the limit base change
`((Over.pullback (c.π.app (op i₀))).obj Y₀).left`; it states the nonempty-fibre
condition as `IsEmpty fibre ∨ fibre.IsPureDimension d`, using Mathlib's
`Scheme.Hom.fiber` and the project definition `Scheme.IsPureDimension`.
* The conclusion is `∃ i, ∃ hi : i₀ ≤ i`, followed by every `j ≥ i` and every
point of the target of the stage-`j` base change.  The same empty-or-pure
predicate is asserted for the stage morphism, with the transition map
`D.map (homOfLE (hi.trans hj)).op`.

Dependency declarations used:

* `Sheaf.AlgebraicGeometry.LimitAffineTransition`,
  `AlgebraicGeometry.exists_limit_affine_transition` (the recorded declaration
  of `lem-weil-pbc-limit-affine-transition`).
* `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom` (Mathlib match for `pqf-def-affine-morphism`).
* `AlgebraicGeometry.LocallyOfFinitePresentation` from
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
* `CategoryTheory.Limits.pullback` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (the recorded
  declaration for `def-pc-fibre-product`).
* `AlgebraicGeometry.Scheme.Hom.fiber` from
  `Mathlib.AlgebraicGeometry.Fiber` (the recorded declaration for
  `def-pc-scheme-fibre`).
* `Sheaf.AlgebraicGeometry.PureDimension`,
  `AlgebraicGeometry.Scheme.IsPureDimension` (the recorded declaration for
  `def-weil-pure-dimension`).

Edge cases checked: `d = 0` is allowed by `d : ℕ`; an empty limit or stage fibre
satisfies the disjunction through `IsEmpty`; no surjectivity or nonemptiness of
individual fibres is imposed; the index set is explicitly nonempty; and the
conclusion applies uniformly to all later `j ≥ i`.  The universe of the index
and all schemes is the same explicit `u`, so no vacuous lower-universe index is
introduced.

Searches made before writing:

* `msearch.py NQ lem-trf-pure-relative-dimension-finite-stage leanfinder` with
  “inverse limit qcqs schemes affine transitions finitely presented morphism pure
  relative dimension finite stage”: no exact declaration.
* `msearch.py ... loogle` with `relativeDimension, IsPureDimension, fiber`: only
  smooth-relative-dimension and fibre declarations, no eventual finite-stage
  theorem.
* `msearch.py ... grep` and `rg` over Mathlib and `WeilConjectures/` for
  `descend.*dimension`, `pure.*relative.*dimension`, and the item id: no matching
  theorem or duplicate declaration.
* `rg` over `weil-newtargets/lean/Sheaf` found the existing
  `Scheme.IsPureDimension`, `Scheme.Hom.fiber`, affine-transition limit, and
  constructible-containment infrastructure, but no declaration of this item.

The source statement was retained unchanged.  No `STATEMENT-DISPUTED` issue or
node fault was found.

## Second reading by NQ

This is the independent maintainer second reading of the immutable delivery. I read `check-brief2.md`, the packet, the item node, all seven statement dependencies, their recorded source and Lean interfaces, the delivered module, and this report.

### Clause-by-clause audit

The item statement has the nonempty directed index set, qcqs schemes, affine transitions, inverse limit, chosen `i₀`, morphism `f₀ : Y₀ → Z₀` over `Sᵢ₀`, qcqs source and target, locally finite presentation, base changes at all later stages and the limit, and `d ≥ 0`. Its hypothesis quantifies every nonempty scheme-theoretic limit fibre and requires pure dimension `d`; its conclusion gives one `i ≥ i₀` and every `j ≥ i` has every nonempty stage fibre pure dimension `d`. The final sentence correctly records that flatness, separatedness, and properness are not assumed.

The Lean theorem renders these clauses with `D : Iᵒᵖ ⥤ Scheme.{u}`, `Preorder`, `IsDirected`, `Nonempty`, affine transition typeclasses, `CompactSpace` and `QuasiSeparatedSpace` for stages, `Cone D` and `IsLimit c`, `i₀`, `Over` objects `X₀,Y₀`, `f₀`, qcqs typeclasses for both objects, `LocallyOfFinitePresentation f₀.left`, and `d : ℕ`. The limit and stage base changes use `Over.pullback`; fibres use `Scheme.Hom.fiber`; the empty-or-pure disjunction exactly represents “every nonempty fibre”. The existential index, witness `i₀ ≤ i`, later `j` and `i ≤ j`, and all target points are present in the conclusion. No clause is strengthened or omitted.

The proof text follows Tag 0EY2: first the finite-stage upper dimension bound, then the retrocompact bounded-dimension locus and constructible complement, base-change invariance of local fibre dimensions, constructible containment, and finally purity and persistence under base change. The module theorem is intentionally a stage-2 statement with only `sorry`; it contains no local proof beyond that permitted hole. Its declaration and module docstrings cite Tag 0EY2, Tags 02NJ/02NK, and `(blueprint: lem-trf-pure-relative-dimension-finite-stage)`.

### Dependencies, edge cases, and searches

`def-weil-pbc-scheme-conventions` supplies the qcqs and scheme conventions; `pqf-def-affine-morphism` supplies affine transitions; `lem-weil-pbc-limit-affine-transition` supplies the limit interface; `def-sbc-locally-finite-presentation` is Mathlib `AlgebraicGeometry.LocallyOfFinitePresentation`; fibre products and scheme-theoretic fibres are Mathlib `CategoryTheory.Limits.pullback` and `AlgebraicGeometry.Scheme.Hom.fiber`; and pure dimension is the project `AlgebraicGeometry.Scheme.IsPureDimension`. I checked each recorded signature against the uses in the theorem. No dependency is a private duplicate or an arbitrary map.

`d = 0`, empty fibres, empty schemes, and disconnected systems are covered by `d : ℕ` and the empty-or-pure disjunction. No characteristic, flatness, separatedness, properness, or surjectivity assumption has been introduced. All scheme and index universes are explicitly `u`; no unbound variable or silent universe equality occurs. Searches recorded in the worker report and independently checked against Mathlib and the project found no existing theorem for this item. The source is Stacks `limits.tex`, Tag 0EY2; the relative-dimension definition and persistence source are `morphisms.tex`, Tags 02NJ and 02NK. The route-pivot dropped list contains no cited machinery and no repair note applies.

### Compiler evidence and findings

`python3 /home/ubuntu/weil-launcher-nt/scompile.py NQ lem-trf-pure-relative-dimension-finite-stage snapshot/lean/Sheaf/TraceFormula/PureRelativeDimensionFiniteStage.lean` compiled the sandbox and library file successfully (about 2.4s and 2.6s), with no errors and no reported warning (the theorem retains its permitted `sorry`). No lake/global build, live Lean write, Git mutation, or project-clone edit was performed.

The original report's second-reading heading was only a statement that no worker second reading existed, so it was not a real second reading section. This complete replacement report supplies this substantive section while preserving the Worker report. H8 is also repaired: the original theorem docstring had no step-by-step proof. The complete replacement Lean module supplies all six node proof steps; the signature is unchanged and remains verbatim equal to `lean.statement`. The mathematics and Lean statement pass.

The replacement module was compiled through the same wrapper using
`fixes/lean/Sheaf/TraceFormula/PureRelativeDimensionFiniteStage.lean`: exit 0, sandbox
4.3s and library 7.1s, no diagnostics. A text comparison verified the exact theorem
signature equals the immutable node's `lean.statement`, and every Lean line is at
most 100 characters. The index universe follows the explicit index-universe
convention in `coord/brief-stage2.md` §2. The worker's prose calls the pullback
`CategoryTheory.MorphismProperty.Over.pullback`; the actual declaration checked is
`CategoryTheory.Over.pullback`, whose object and map fields are the canonical
pullback and induced pullback map. The Lean code already uses this correct one.
