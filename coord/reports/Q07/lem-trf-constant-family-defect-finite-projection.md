## Worker report

The repaired module `lean/Sheaf/AlgebraicGeometry/LinearProjectionFiniteClosure.lean`
contains three canonical helper definitions and the theorem
`AlgebraicGeometry.exists_linearProjection_finite_closure_avoids_infinity`.  The helpers
turn linear forms and a linear map on the coordinate vector space into affine-space
morphisms using `AffineSpace.homOfVector` and the standard coordinate sections.  The
helpers have real data and no postponed definitions.

The theorem has the following Lean rendering of the statement.  `k : Type u` has
`[Field k] [Infinite k]`; `m : ℕ` has `hm : 1 ≤ m`; `Y : Scheme.{u}` maps by `i` to
`𝔸(ULift (Fin m); Spec k)`, with `[IsClosedImmersion i]`, `[IsReduced Y]`, and
`hproper : ¬ Function.Surjective i.base`.  It produces a submodule `l` with
`Module.finrank k l = 1`, and a linear equivalence
`φ : (Fin m → k) ≃ₗ[k] k × (Fin (m - 1) → k)`.  The equation
`LinearMap.ker ((LinearMap.snd k k (Fin (m - 1) → k)).comp φ.toLinearMap) = l`
expresses that the quotient direction is exactly `l`.

The coordinate target is the scheme pullback over `Spec (.of k)` of the affine line and
`𝔸(ULift (Fin (m - 1)); Spec k)`.  The existential isomorphism `e` has its second
pullback component equal to `affineLinearRestMap` for the second component of `φ`, and
its first component equal to `affineLinearScalarMap` for the first component of `φ`.
Its further displayed equality says that the first component followed by the affine-line
structure map is the original affine-space structure map, so the identification is over
`Spec k`.  The finite clause is `IsFinite (i ≫ affineLinearRestMap ...)`.

For the compactification, the module maps the source pullback to the pullback of the
projective line and the transverse affine space with `Limits.pullback.map`, using
`ProjectiveLine.affineChart` and the identity.  The infinity section is the pullback
lift of `ProjectiveLine.infinity` and the identity.  The final clause is disjointness of
`Set.range` of the scheme-theoretic image closure (`imageι.base`) from the range of this
infinity section.  All products in these clauses are fibre products over `Spec k`.

The statement-dependency declarations used are:

- `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace` and its
  `AffineSpace.homOfVector`, `AffineSpace.coord`, and affine-space notation;
- `AlgebraicGeometry.IsClosedImmersion` from the recorded closed-immersion dependency;
- `AlgebraicGeometry.IsFinite` from the recorded finite-morphism dependency;
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line`, with
  `AlgebraicGeometry.ProjectiveLine.affineChart` and
  `AlgebraicGeometry.ProjectiveLine.infinity`;
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`, the module
  recorded by `def-sc-p1-standard`.

I checked the edge cases `m = 1` (the transverse type is `Fin 0`), the empty closed
subscheme, a degree-one monic equation, and a nonreduced scheme.  The theorem retains
`IsReduced` exactly as required by the node; the empty case still has a valid image and
is disjoint from infinity.  The linear equivalence and pullback formulation does not
identify `Spec k` with `Spec ℤ`, so it also covers fields such as `ℚ(x)` and `F_p(x)`.

The searches in the retained packet were repeated: `msearch.py` LeanFinder for a finite
linear projection and relative projective closure, Loogle for `NoetherNormalization`,
grep in Mathlib for `NoetherNormalization|noether_normalization|linearProjection`,
LeanSearch/LeanFinder for generic projection and monic-closure results, `rg` through
`WeilConjectures`, `rg` through shared `lean/Sheaf`, and a grep for this item id.  They
found only generic finite-morphism, polynomial, projectivization, and coordinate APIs;
no declaration states this theorem or the linear affine-map helpers.

## Second reading by Q07

I opened the corrected node and module together.  The field, infinitude, positive
integer, scheme, closed-immersion, reducedness, and proper-subscheme hypotheses are all
present.  The first conclusion clause is the one-dimensional submodule.  The second
introduces `φ` and explicitly identifies its second-component kernel with that line.
The next clause uses `Limits.pullback` over `Spec k`, and the two component equalities
force `e` to be induced by the first and second linear coordinates; the following
structure-map equality records that this is over the base.  The finite morphism is the
second-coordinate map restricted along `i`.  The final two expressions are the affine
chart pullback into `ProjectiveLine ×_k 𝔸^{m-1}` and the pullback lift of the infinity
section, followed by the required disjointness of the scheme-theoretic image closure.
No arbitrary `Limits.prod`, unrelated `l`, or product over `Spec ℤ` remains.

## Statement corrected

Old statement:

`Let $k$ be an infinite field, let $m\geq1$, and let $Y\subsetneq\mathbf A^m_k$ be a
proper reduced closed subscheme [def-sbc-affine-space, def-weil-closed-immersion]. There
is a one-dimensional linear subspace $l\subset k^m$ such that the quotient projection
$q:\mathbf A^m_k\to\mathbf A^m_k/l\simeq\mathbf A^{m-1}_k$ restricts to a finite
morphism on $Y$ [def-weil-finite-integral-morphism]. After choosing a linear complement to
$l$, identify $\mathbf A^m_k$ with $\mathbf A^1_k\times\mathbf A^{m-1}_k$ over the
quotient. The scheme-theoretic closure of $Y$ in $\mathbf P^1_k\times\mathbf A^{m-1}_k$
is disjoint from the infinity section $\{\infty\}\times\mathbf A^{m-1}_k$.`

The old Lean used an arbitrary `e` unrelated to `l`, and `Limits.prod`, which is a
product over `Spec ℤ`; hence the claimed quotient and infinity section were not the
field-relative objects and the statement was false for general fields.  Following
Varshavsky §3.2.4, the corrected statement uses the fibre products over `Spec k`, a
linear equivalence whose second component has kernel `l`, and component equations making
`e` the induced base-preserving linear-coordinate isomorphism.

The only citer is `lem-trf-specialization-zero-section`; its use of a finite projection
and a closure avoiding the relative infinity section still holds with these corrected
objects (`holds: true`), so it was not edited.
