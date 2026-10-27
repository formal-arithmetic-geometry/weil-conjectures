## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothPTorsionAdditiveEmbedding` states
`AlgebraicGeometry.smooth_p_torsion_additive_embedding`, with its entire proof `sorry`.
The node is unchanged except for its `lean` record. No definitions, new nodes,
dependency repairs, or statement corrections were needed.

Read Milne, Algebraic Groups (2017), PDF pages 307-309 (printed pages 295-297):
Definition 14.45 defines elementary unipotence by embedding in a vector group,
and Proposition 14.49 gives precisely the smooth commutative exponent-p case.
Neither connectedness nor perfection appears there. The proof docstring follows
all five steps of the accepted node, including the explicit Frobenius-injectivity
argument over an imperfect field and finite extraction of primitive coordinates.

Clause-by-clause rendering:

- The field is `{k : Type u} [Field k]`; positive characteristic is
  `(p : ℕ) [CharP k p] (hp : 0 < p)`. No extra prime or perfect-field hypothesis
  is imposed (primality follows for a field of positive characteristic).
- The k-group scheme is `(H : Grp (Over (Spec (.of k))))`. This bundles exactly
  a k-scheme with `GrpObj H.X`, whose multiplication, identity and inverse satisfy
  the group diagrams. Commutativity is `[IsCommMonObj H.X]`.
- Affineness is `[IsAffine H.X.left]`; smoothness is `[Smooth H.X.hom]`.
- Finite type is `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`, the
  recorded two-part rendering of `def-weil-finite-type-morphism`.
- The hypothesis `hkilled` quantifies over every `R : Type u` with `CommRing R`
  and `Algebra k R` and every morphism `Spec R -> H` over `Spec k`. It asserts
  `x ^ p = 1`. The scoped group-object operation on the Hom type is the group
  law of H(R); its multiplicative notation means precisely the stated p-fold
  additive sum being zero. It is not ring multiplication or composition.
- The conclusion quantifies over `n : ℕ`, including zero, and a morphism in
  `Grp (Over (Spec k))` from H to the categorical product of n copies of
  `Grp.mk (StandardGroupSchemes.additive k)`. Such a bundled morphism is a
  k-group-scheme homomorphism. Its underlying k-scheme map is `i.hom.hom`.
- `IsClosedSubgroupScheme i.hom.hom` supplies the closed immersion and the
  injectivity on algebra-valued points, using the dependency's exact predicate.
  Products in `Grp` are created by the forgetful functor, so the group law is
  coordinatewise. The empty product is terminal, hence Spec k with its trivial
  group law. No arbitrary new target group structure is chosen.
- No connectedness, nontriviality, or perfection assumption is present.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (`def-weil-field`).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, `Grp.homMk`, and the
  group law on Hom; `Mathlib.CategoryTheory.Monoidal.Mon`: `IsCommMonObj` and
  `IsMonHom` (`def-sc-group-scheme`). The full group-scheme interpretation is
  documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, which is
  publicly imported by `StandardGroupSchemes`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme` and
  `IsClosedSubgroupScheme` (`def-sc-group-scheme-subgroup`). The latter extends
  the former and adds `IsClosedImmersion i.left`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `additive`, `additiveComul`,
  `additiveCounit`, `additiveAntipode`, and `additiveGroup` (`def-sc-gm-ga`).
  The underlying scheme is Spec k[y], with substitutions y -> y⊗1+1⊗y,
  y -> 0, and y -> -y. The instance is fixed by these operations.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, the exact recorded
  affine-local smoothness predicate (`def-sbc-smooth-morphisms`).
- `Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits`: products in `Grp`,
  with limits created by `Grp.forget`.

The imports also retain the available proof dependencies:
`Sheaf.AlgebraicGeometry.AffineGroupFrobeniusVerschiebung`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`,
`Mathlib.AlgebraicGeometry.Geometrically.Integral`,
`Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`, `Mathlib.RingTheory.FiniteType`,
`Mathlib.AlgebraicGeometry.Group.Affine`, and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`. Reduced schemes and the
Hopf/spectrum interfaces are exposed through these modules. The proof-only node
`lem-sfb-zero-verschiebung-primitive-generation` has no recorded declaration at
the time of writing; no guessed module was imported for it. It is not needed to
type the statement.

Edge cases checked before writing:

- H = the trivial group and n = 0 are included. An empty group scheme cannot
  satisfy the group-object identity-section datum over a field.
- Constant Z/p is smooth, affine, commutative and killed by p; disconnectedness
  is allowed and the additive subgroup given by t^p-t supplies the expected case.
- Imperfect fields and their smooth exponent-p forms are included; the conclusion
  is an embedding, and imposes no isomorphism with an additive power.
- The characteristic p = 2 is included; p = 0 is excluded exactly by `hp`.
- Nonreduced test algebras and the zero algebra are included in `hkilled`; the
  latter has the unique empty-scheme point. Alpha_p and mu_p fail smoothness,
  and mu_p also fails the claimed additive embedding, as expected.
- The base, scheme and test-algebra universes follow the recorded group-scheme
  interface. Type-u test algebras include the affine universal point of H, so the
  hypothesis detects the morphism [p] itself and hence also its action on larger
  test algebras. No independent smaller test universe makes the condition vacuous.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder` with query "A smooth commutative affine group
  scheme in characteristic p killed by p admits a closed immersion into a finite
  power of the additive group": eight results about closed immersions and affine
  space, no group-scheme exponent-p embedding theorem.
- `msearch.py ... loogle 'GrpObj, IsClosedSubgroupScheme'`: zero results; the
  service reported unknown identifier GrpObj. Local source inspection resolved
  the interfaces instead.
- `msearch.py ... grep 'VectorGroup|vector.group|elementary.unipotent|additive.*embedding'
  AlgebraicGeometry`: zero Mathlib results.
- `msearch.py ... leansearch` with query "A smooth affine commutative algebraic
  group of exponent p embeds into a finite product of additive group schemes":
  eight unrelated affine-scheme, abstract-group and smoothness results, no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for exponent-p, additive-power,
  vector-group and additive-embedding names found the existing characteristic-zero
  vector-group theorem and the perfect-field additive-subgroup decomposition.
  Their hypotheses and conclusions differ. They confirm the existing bundled
  finite-product encoding, which this module reuses.
- Search for this node id in `lean/WeilConjectures` found no attachment. Search
  for the new theorem and module names in both source roots and
  `dag/lean_names_upstream.json` found no collision.

Validation: `scompile.py` compiled the file cleanly both as a sandbox module and
as `Sheaf.AlgebraicGeometry.SmoothPTorsionAdditiveEmbedding` (1.7 seconds each).
The initial compiler diagnosis was a missing `open scoped CategoryTheory.MonObj`
for the power and unit on H(R); this was repaired. No mathematical statement
changed. The only postponed proof is the named theorem above.

## Second reading by Q115

This dispatcher assignment forbids starting another agent. This section records
my separate rereading of the node and completed Lean file; independent review is
left to the maintainer's delivery reviewer, as specified in the assignment.

Compared every binder and clause again: positive characteristic has its explicit
strict inequality, H is affine and smooth and finite type and commutative,
`hkilled` ranges over arbitrary commutative algebras rather than just field-valued
points, and the conclusion uses the recorded additive group with its own group
law, the product in bundled group schemes, and the recorded closed-subgroup
predicate. The natural-number binder includes zero. No connectedness or
perfection was introduced, and the closed immersion is over k because the
ambient morphism is in `Over (Spec k)`. No mismatch was found on this rereading.
There are no new/dependency modules to review and no node-statement faults.
