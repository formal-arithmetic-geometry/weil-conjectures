## Worker report

Module `Sheaf.AlgebraicGeometry.InvariantOpenImagePullback` states
`AlgebraicGeometry.invariant_open_image_pullback`, with one postponed theorem and
no definitions. The node is unchanged except for `lean`. No new nodes or dependency
repairs are needed. The source was read in `literature/stacks-project/descent.tex`,
Tag 0247, `lemma-quasi-affine`, especially the final paragraph identifying the stable
open with the inverse image of an open in the descended ambient scheme.

Hypothesis and conclusion correspondence:

- Schemes W, W', V and the morphisms q, j are explicit binders in `Scheme.{u}`.
  `[Flat q] [QuasiCompact q] [Surjective q]` are exactly the three hypotheses on q.
  `[IsOpenImmersion j]` gives the stated open immersion. There is no finite-type,
  finite-presentation, quasi-affine, or quasi-compact-V assumption.
- O is written directly as `Set.range j`; the kernel-pair projections are
  `pullback.fst q q` and `pullback.snd q q`. The equality of inverse images is `hinv`.
- The first conjunct quantifies over every x and y, assumes `q x = q y`, and
  concludes membership in `Set.range j` is equivalent.
- `∃ U : W'.Opens` gives the actual open-subscheme structure, with
  `(U : Set W') = q '' Set.range j`. The next equality is the required inverse image.
  The following universally quantified `S : Set W'` proves uniqueness among all
  subsets, rather than just among opens.
- `∃ h : V ⟶ U.toScheme` gives the factorization, with `h ≫ U.ι = j ≫ q`.
  The universally quantified k gives uniqueness for that equation.
  `IsPullback j h q U.ι` states the cartesian square. By the pullback universal
  property, its canonical comparison is an isomorphism compatible with j and h;
  this is the equivalent formulation in the node, not an additional assumption.
- The moreover clause remains inside the same existential U and h. It quantifies
  over A, B, `a : A ⟶ B`, `b : W' ⟶ B` and `theta : W ≅ pullback b a`.
  `_htheta` says the first projection is q. The f binder and `_hf` name exactly the
  induced map `j ≫ theta.hom ≫ pullback.snd b a`; this is definitional naming of
  the map specified by the node, not a restriction on the geometry.
- `D : Over.DescentDatum a (Over.mk f)` is the given datum. The recorded upstream
  interface uses natural transport of T-points instead of a separately packaged
  overlap isomorphism; its docstring explains the equivalence by Yoneda.
  `_hcompat` says transporting then mapping by theta-j leaves the ambient
  W'-coordinate fixed. Transport already prescribes the A-coordinate, so this
  is exactly intertwining with the canonical ambient descent datum.
- The isomorphism e lands in `pullback (U.ι ≫ b) a`; its two displayed projection
  equations say it is induced by h and f. The final equality for all T-points
  says D preserves the U-coordinate under e. Since it sends the A-coordinate
  from f₀ to f₁, this characterizes the canonical datum on U times_B A uniquely.
  Thus the conclusion recovers the actual D, not just an underlying isomorphism
  or an unspecified effective datum.

Recorded dependency interfaces read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` (including its stalkwise equivalence).
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; only its recorded
  `AlgebraicGeometry.QuasiCompact` notion is needed, not locally finite type.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective` (surjectivity on underlying points).
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; scheme pullbacks are supplied by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-pd-descent-datum`:
  `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`,
  `CategoryTheory.Over.DescentDatum` and its `transport`. Its `IsEffective` docstring
  explicitly uses the same pullback-plus-transport-invariance characterization.

Proof dependencies are available through the public imports of their owning
statement notions and the additional plain proof import
`Mathlib.AlgebraicGeometry.PullbackCarrier`:
`Scheme.image_preimage_eq_of_isPullback`, `Flat.isQuotientMap_of_surjective`,
`IsOpenImmersion.lift`, `IsOpenImmersion.lift_fac`, `IsOpenImmersion.lift_uniq`, and
`IsOpenImmersion.mono`. Their source signatures were read. The theorem docstring
carries all six proof steps, including explicit construction of the inverse of e
and cancellation to recover D.

Edge cases checked before writing: V empty gives U empty and the empty cartesian
model; O all of W gives U all of W' by surjectivity; q an isomorphism gives the
ordinary open image; if W' is empty then W and V are empty; no rational-point-pair
identification is used for scheme fibre products. The source proof correctly uses
the scheme image formula. Test schemes in the transport condition run through
all `Scheme.{u}`, the universe of the category used by the dependency, and u is
explicit and arbitrary. No index-set, nonempty, or dimension restriction is added.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query “An invariant open subscheme under the kernel pair
  of a flat quasi compact surjective morphism descends to a unique open image with
  its descent datum”: eight hits, led by
  `AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`.
  These descend a property of an already supplied morphism; they do not construct
  this open model or preserve the given datum as asserted here.
- `msearch.py loogle`, query `AlgebraicGeometry.Flat, "isQuotientMap"`: one hit,
  `AlgebraicGeometry.Flat.isQuotientMap_of_surjective`, the existing proof leaf.
- `msearch.py grep`, query
  `invariant.*open|isQuotientMap_of_surjective|exists_preimage_pullback` in
  `AlgebraicGeometry`: 22 hits, providing quotient topology and fibre-product
  point-lifting ingredients, no exact full statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `invariant.*[Oo]pen|invariant_open|open_image_pullback`, and the exact item id in
  `lean/WeilConjectures`: no declaration for this item. The related
  `WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent` was opened;
  it states gluing effective models on an invariant open cover, a different result.
  The named declaration is fresh. No notion has been privately duplicated.

Validation: the prescribed `scompile.py` compiled this module in sandbox mode
and at its intended library module path, both cleanly (3.7 s and 3.6 s).
Only the theorem proof is postponed. No statement fault was found.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
