## Worker report

The node is recorded on two existing declarations in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange`:

* `AlgebraicGeometry.Scheme.Modules.isLocallyConstant_eulerCharFiber` (main declaration);
* `AlgebraicGeometry.Scheme.Modules.eulerCharFiber_pullback_of_isPullback` (base-change clause).

No Lean module, definition, theorem, proof, or dependency node is added. Only the item's
`lean` record changes. Its stage-1 split and review are preserved. The previous worker's
blocker confused a completed stage-1 review with a completed stage-2 binding: the node
had no `lean` record and no `reviewed_lean`. This is its first stage-2 binding.

Source checked: `literature/stacks-project/perfect.tex`, Tag 0B9T,
`lemma-chi-locally-constant-geometric`, lines 7961--7990. The statement explicitly says
proper of finite presentation, F finitely presented and flat over S, local constancy,
and commutation with base change. The library source was also read directly from the
live server using `scompile.py --source` and agrees with the local module.

Hypothesis and clause correspondence (namespace below is
`AlgebraicGeometry.Scheme.Modules` unless another namespace is specified):

1. Schemes X and S and their morphism are `{X T : Scheme.{u}}` and `(f : X ⟶ T)`.
   The universe `u` is arbitrary; there is no characteristic, nonemptiness, or dimension
   restriction.
2. Properness is `[IsProper f]`. Finite presentation is
   `[LocallyOfFinitePresentation f]` together with the quasi-compact and quasi-separated
   consequences of properness. The upstream section also lists `[QuasiCompact f]`, which
   follows from properness, so it adds no mathematical hypothesis.
3. F is `(ℱ : X.Modules)` and finite presentation is `[ℱ.IsFinitePresentation]`.
   Mathlib's `SheafOfModules.IsFinitePresentation` is exactly a local finite presentation
   by finite free sheaves; it also supplies quasi-coherence.
4. Relative flatness is `(hℱ : ℱ.IsFlatOver f)`. Its definition in
   `Cohomology.DirectImage.Basic` says that on every affine U over an affine V of T,
   Γ(U,F) is flat over Γ(V,O_T), via `Module.compHom` along `f.appLE`. For a quasi-coherent
   F this is equivalent to the node's flatness of every F_x over O_{T,f(x)}. Finite
   presentation supplies that quasi-coherence. It does not assume `Flat f`.
5. The fibre is exactly `f.fiber t = pullback f (T.fromSpecResidueField t)` and its map
   to X is `f.fiberι t = pullback.fst _ _` (Mathlib's `AlgebraicGeometry.Fiber`).
   `T.residueField t` is the residue field of the local ring at t, as recorded by the
   dependency. `hFiber` uses the canonical `f.fiberOverSpecResidueField t` structure
   and the pulled-back module `((Modules.pullback (f.fiberι t)).obj ℱ)`.
6. The integer-valued function is `ℱ.eulerCharFiber f : T → ℤ`. Expanding `eulerCharFiber`
   and `hFiber` gives the same alternating `finsum` of `finrankH` as the dependency's
   `eulerChar`, over `T.residueField t`. Proper coherent fibre cohomology is finite and
   bounded, so this is the intended finite alternating sum, including the empty fibre.
7. Local constancy is `IsLocallyConstant (ℱ.eulerCharFiber f)` in the main declaration.
   Mathlib's `IsLocallyConstant.tfae` identifies this with the assertion that every
   point has an open neighbourhood on which the function has its value at that point.
8. For arbitrary g:S'→S, take `T'` arbitrary, `g : T' ⟶ T`,
   `X' := pullback f g`, `g' := pullback.fst f g`, `f' := pullback.snd f g`, and the
   canonical `IsPullback g' f' f g` witness. The second recorded declaration actually
   allows any cartesian square, so it covers the chosen fibre product and every
   isomorphic model of it. Its conclusion is precisely
   `((Modules.pullback g').obj ℱ).eulerCharFiber f' t' = ℱ.eulerCharFiber f (g.base t')`
   for every `(t' : T')`. Expanding `hFiber` also supplies the second fibre pullback
   F'_{s'}. This existing theorem needs neither relative flatness nor local finite
   presentation, so specializes directly under the item's hypotheses; no extra
   condition is imposed on g or on S'.
9. Neither theorem assumes Noetherianity or reducedness of T. The injective-resolution
   parameter of the main theorem is available for every X: the theorem
   `isGrothendieckAbelian X` in `Cohomology.DirectImage.Basic` and the standard
   Grothendieck-abelian instances supply it. It is categorical infrastructure, not an
   extra geometric hypothesis.

Dependency declarations read and used to interpret the existing binding:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
* `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and `.Quasicoherent`:
  `SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation`.
* `Mathlib.RingTheory.RingHom.Flat` and `Mathlib.RingTheory.Flat.Basic`:
  `RingHom.Flat` and `Module.Flat`.
* `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, and `pullback.snd`.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`, with its actual
  tensor-pullback construction and canonical identity/composition comparisons.
  The existing result uses Mathlib's `Modules.pullback`, the left adjoint to the same
  `Modules.pushforward` (`Mathlib.AlgebraicGeometry.Modules.Sheaf`). The two are
  canonically isomorphic by uniqueness of left adjoints. Euler characteristics are
  invariant under module isomorphism, so this realizes the same dependency notion;
  no new pullback construction or normalization choice is introduced here.
* `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar`, and its `finrankH` definition.
* The existing proof dependency in
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`:
  `exists_isFiniteFreeComplex_higherDirectImage`. Its full statement and docstring
  were read. The existing local-constancy proof uses precisely this node's local
  finite-free model, then cancels consecutive boundary ranks.

Edge cases checked by reading the statements and definitions:

* Empty base: the local and pointwise conclusions quantify over no points.
* Empty X, empty fibres, and zero F: the cohomology dimensions and Euler characteristic
  are zero; no nonempty, positive-rank, or nonzero condition appears.
* A complex supported in degree zero: the alternating sum equals its degree-zero rank;
  the proof's boundary terms at -1 and d vanish also when d=0.
* Arbitrary characteristic, nonreduced base, and non-Noetherian base remain allowed.
* Identity, empty, nonflat, and non-finitely-presented base changes are included:
  the base-change declaration has no such hypothesis on g.

Searches (all through the prescribed `msearch.py N6 <item>` wrapper where applicable):

* LeanFinder: "Euler characteristic of a finitely presented sheaf flat over the base of
  a proper finitely presented morphism is locally constant and invariant under arbitrary
  base change". Eight hits, including `Module.isLocallyConstant_rankAtStalk` and
  `AlgebraicGeometry.Flat.isStableUnderBaseChange`; no matching Mathlib Euler theorem.
* Loogle: `"eulerChar", "IsLocallyConstant"`. Zero hits.
* Mathlib grep in `AlgebraicGeometry`:
  `eulerCharFiber|eulerChar.*[Ll]ocally|[Ll]ocally.*eulerChar`. Zero hits.
* LeanSearch: "Euler characteristic of fibre cohomology of a finitely presented flat
  sheaf in a proper family is locally constant". Eight hits; module rank local
  constancy and topology results, no matching coherent-cohomology theorem.
* Project rg over both `lean/WeilConjectures` and `lean/Sheaf`, using the preceding
  Euler patterns and base-change variants, found the two recorded declarations in
  `Cohomology/DirectImage/BaseChange.lean` at lines 96 and 112, and their uses in
  `Picard/Degree.lean`. No duplicate declaration is needed.
* The prescribed item-id search over `lean/WeilConjectures` found no attachment to
  this newly split node. This does not prevent reuse of the existing declarations.

There is no statement correction, disputed statement, dependency repair, or new node.
The main signature in `lean.statement` is copied verbatim from the source; its section
parameters and the second declaration's full signature are explained above.

Validation: the prescribed delivery dry run checks both fully qualified declarations
on the server by compiling an existing-declaration probe, and runs stage-2 preflight.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
