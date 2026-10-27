## Worker report

The module `Sheaf.AlgebraicGeometry.InertiaLocallyQuasiFiniteDiagonal` states
`CategoryTheory.relative_inertia_locallyQuasiFinite_diagonal` with its whole proof
postponed by `sorry`. No definition is introduced or copied. The node's statement
is unchanged. Two existing landed definition nodes are added to `stmt_deps` to
name the canonical constructions and the already available scheme-test interface.

Hypotheses and clauses, matched individually:

- The base scheme S is `{S : AlgebraicGeometry.Scheme.{u}}`. Explicit universe
  levels `u v₁ w₁ v₂ w₂` implement the size convention. The two stacks' object
  and morphism universes are independent; no equality between them is imposed.
- The algebraic stacks X and Y are `F : BasedCategory.{v₁, w₁} (Over S)` and
  `G : BasedCategory.{v₂, w₂} (Over S)` with exactly the hypotheses
  `hF : IsAlgebraicModuliStack F` and `hG : IsAlgebraicModuliStack G`.
  This includes fibred groupoids and étale descent through `IsModuliStack`.
- The map f over S is `f : BasedFunctor F G`; it has no representability,
  finite-type, quasi-compactness, separatedness, or DM hypothesis.
- The relative inertia objects and arrows are given by the existing
  `relativeModuliInertia f`: the full subcategory of `ModuliInertiaObject F`
  satisfying `f.toFunctor.map x.automorphism.hom = 𝟙 (f.obj x.obj)`.
  Its arrows satisfy `α ≫ v = v ≫ α'`, precisely vα = α'v in the node's
  usual composition convention. The projection forgets the automorphism.
- Representability of the projection is the first conjunct
  `IsRepresentableByAlgebraicSpaces (relativeModuliInertiaProjection f)`.
- Representability of the relative diagonal is the second conjunct
  `IsRepresentableByAlgebraicSpaces (moduliRelativeDiagonal f)`.
  The existing diagonal sends x to (x,x,1), with the identity comparison in
  the existing `moduliTwoFiberProduct f f`.
- The equivalence is the third conjunct: `ModuliSpaceTest
  @AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` on the inertia projection
  if and only if that same predicate on the diagonal. Unfolding `ModuliSpaceTest`
  quantifies over every scheme T and map to the target, asks for an algebraic
  space Z presenting that exact 2-base change with its projection p, and tests
  `Scheme.Hom.IsLocallyQuasiFinite` on the composite of every representable
  étale chart of Z with p. In particular local finite type is retained:
  the weaker Mathlib `LocallyQuasiFinite` alone is not used.
- For Y=S the final conjunct says the canonical inclusion
  `relativeModuliInertiaToAbsolute (moduliBaseStructure F)` is an equivalence.
  It is a functor over the base, retaining the actual object, automorphism,
  arrow, and projection. The identity category over `Over S` represents S;
  this is the same specialization as the existing geometry theorem, and
  requires no extra choice or arbitrary equivalence.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (exposed transitively). The size node is a convention without a declaration.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `CategoryTheory.IsAlgebraicModuliStack`,
  whose complete definition uses `IsModuliStack`, `HasAlgebraicSpaceDiagonal`,
  and a smooth surjective scheme atlas.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (publicly exposed by the
  algebraic-stack module): `IsFibredInGroupoids`, `ModuliTwoIso`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `discreteModuli`,
  `HasSpaceBaseChange`, and `IsRepresentableByAlgebraicSpaces`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace` (exposed transitively):
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsEtale`, with its
  representable diagonal and surjective étale scheme atlas in fppf sheaves.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism` (exposed by the morphism
  properties module): `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`,
  defined pointwise using `IsQuasiFiniteAtPoint` including finite type.
- Added landed dependency `def-sfb-relative-moduli-inertia`, module
  `Sheaf.AlgebraicGeometry.RelativeModuliInertia`: `relativeModuliInertia`,
  `relativeModuliInertiaProjection`, `relativeModuliInertiaToAbsolute`,
  and `moduliBaseStructure`.
- Added landed dependency `def-sfb-dm-stack-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest` and
  `moduliRelativeDiagonal`. These definitions themselves have no DM assumption,
  so they apply unchanged to arbitrary algebraic stacks here.
- Proof-only import `Sheaf.AlgebraicGeometry.RelativeInertiaSecondDiagonalGeometry`:
  `relative_inertia_second_diagonal_geometry`, `relative_moduli_inertia_absolute`.
  The other proof-only statement nodes `lem-sfb-stack-relative-diagonal-finite-type`
  and `lem-sfb-locally-quasifinite-pseudo-torsor` have no Lean record yet, so there
  is no module to import for either. Their proof roles are included, step by step,
  in the theorem docstring; neither is needed to type this statement.

Source and edge-case reading:

Read `literature/stacks-project/stacks-morphisms.tex`, lemma-diagonal-diagonal,
Tag 0CL0, especially part (5) and its two relative Isom cartesian squares.
The source explicitly expands quasi-DM as locally quasi-finite diagonal.
Read the relative-inertia definition and geometry theorem in full, including
its canonical absolute specialization. There is no statement fault or dispute.

The empty stack and empty scheme tests are permitted; no nonemptiness or local
section is assumed. An empty Isom space is still a pseudo-torsor and remains
locally quasi-finite. For the identity map, the relative inertia kernel is
trivial, and both maps satisfy the asserted property. For a scheme over S,
the ordinary inertia has trivial automorphisms and its diagonal is locally
quasi-finite. For BG over a field, the assertion is exactly the local
quasi-finiteness test on G: positive-dimensional G_a makes both sides false;
a finite nonreduced group such as μ_p still makes both sides true. Thus there
is no hidden unramifiedness or characteristic restriction. Large stacks are
allowed by the independent explicit universes of both BasedCategory binders.
These are mathematical statement checks; no additional theorem was proved.

Searches made for an existing statement:

- `msearch.py ... leanfinder` with query "The relative inertia projection of a
  morphism of algebraic stacks is locally quasi finite if and only if its
  relative diagonal is locally quasi finite": 8 hits, all scheme local
  quasi-finiteness/base-change/composition or quasi-separatedness results;
  none states the relative-inertia assertion.
- `msearch.py ... loogle` with query `"inertia", "diagonal"`: OK, 0 hits.
- `msearch.py ... leansearch` with query "Relative inertia projection locally
  quasi finite if and only if relative diagonal of morphism of algebraic stacks
  locally quasi finite": 8 hits, all scheme or ring-map predicates and lemmas;
  none is the requested stack statement.
- `msearch.py ... grep` with regular expression
  `relativeInertia|relativeModuliInertia|inertiaStack|AlgebraicStack`: OK, 0 hits.
- `rg` of Mathlib/AlgebraicGeometry for `inertia|AlgebraicStack`: no hits.
- `rg` of `lean/WeilConjectures` for relative inertia and algebraic-stack names,
  and for the exact item id: no hits.
- `rg` of `lean/Sheaf` for relative inertia, inertia/diagonal, and the exact
  local-quasi-finite scheme-test expression found the canonical relative inertia
  and geometry modules, the morphism properties, and representable quasi-finite
  calculus. No declaration states the present equivalence. These existing
  definitions are reused; no new definition node is needed.

Validation uses the prescribed server `scompile.py`, followed by the `deliver2.py`
dry run and final delivery. The file has explicit universes and `autoImplicit false`;
only the expected declaration-uses-sorry warning is permitted.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
