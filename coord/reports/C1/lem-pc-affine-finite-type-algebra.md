## Worker report

The module states `AlgebraicGeometry.affine_finiteType_algebra_of_field` with a
`sorry` proof. The statement uses the coordinate ring `Γ(Y, ⊤)` and the algebra
structure induced by the structure morphism through `Scheme.ΓSpecIso`.

Hypotheses and conclusion, clause by clause:

- The field `k` is `{k : Type u} [Field k]`.
- The scheme is `{Y : Scheme.{u}}`; its affineness is `[IsAffine Y]`.
- The structure morphism is `(f : Y ⟶ Spec (.of k))`.
- Its finite-type condition is `[LocallyOfFiniteType f] [QuasiCompact f]`, the
  two parts of finite type in `def-weil-finite-type-morphism`.
- `B = Γ(Y, O_Y)` is `Γ(Y, ⊤)`. The local `Algebra k Γ(Y, ⊤)` instance comes from
  `f.appTop.hom` composed with the inverse of `Scheme.ΓSpecIso (.of k)`.
- Finite generation of that induced algebra is `Algebra.FiniteType k Γ(Y, ⊤)`.

Dependencies used: `def-pc-scheme` is Mathlib's
`AlgebraicGeometry.Scheme` and `AlgebraicGeometry.IsAffine`
(`Mathlib.AlgebraicGeometry.Scheme`, `Mathlib.AlgebraicGeometry.AffineScheme`);
`def-weil-finite-type-morphism` is `AlgebraicGeometry.LocallyOfFiniteType`
and `AlgebraicGeometry.QuasiCompact`
(`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`);
`def-weil-pbc-finite-type-algebra` is `Algebra.FiniteType`
(`Mathlib.RingTheory.FiniteType`). All dependency records are Mathlib matches.

Edge cases checked: `Y = Spec k` gives `B = k`; affine space has a polynomial
coordinate algebra; a finite disjoint union has a finite product algebra; the
empty affine scheme has the zero coordinate ring. No nonemptiness, reducedness,
integrality, or positive characteristic assumption is present. The shared
universe `u` matches the available `Spec (.of k)` interface in Mathlib.

Searches for an existing exact statement:

- `msearch leanfinder "An affine scheme of finite type over a field has a
  finitely generated coordinate algebra of global sections"`: found the
  related Mathlib affine-pair finite-type result, no exact theorem.
- `msearch loogle "Algebra.FiniteType, IsAffine, LocallyOfFiniteType"` and
  `"AlgebraicGeometry.IsAffineOpen.algebra_finiteType_of_field"`: the service
  reported unknown identifiers, so neither query yielded an exact match.
- `msearch grep "algebra_finiteType_of_field|finiteType.*isAffine"
  AlgebraicGeometry`: no exact theorem in Mathlib.
- `rg` in Mathlib's `AlgebraicGeometry` and in the source repository found
  `AlgebraicGeometry.IsAffineOpen.algebra_finiteType_of_field` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`. It applies
  to any affine open under the weaker `LocallyOfFiniteType` condition, so its
  signature is broader than this node's whole-scheme finite-type statement.
  No declaration named `affine_finiteType_algebra_of_field` exists upstream.
- `grep -rn "lem-pc-affine-finite-type-algebra"` in `WeilConjectures` and
  `rg` in the project's `lean/Sheaf` returned no match.

Source: Stacks Project, Morphisms, Lemma 29.15.2 (Tag 01T2), part (1) implies
part (2), taking both affine opens to be the whole schemes. The local
`literature/stacks-project/morphisms.tex` checkout was absent on this machine;
the corresponding Stacks page was read online. Its conclusion is the finite
type map on global sections used here. The Lean file compiles cleanly via
`scompile.py`.

## Second reading by C1

I read the item node, its three dependency records, and
`lean/Sheaf/AlgebraicGeometry/AffineFiniteTypeAlgebra.lean` independently.
The source place is Stacks Project, `morphisms.tex`, Lemma 29.15.2, Tag 01T2
(`lemma-locally-finite-type-characterize`), implication (1) => (2), with both
affine opens equal to the whole schemes. The source's conclusion is the finite
type map on global sections, which specializes to the stated coordinate
algebra.

Object and hypothesis checklist:

- The field `k` is rendered by `{k : Type u} [Field k]`; no characteristic or
  nonzero hypothesis is added.
- The affine scheme `Y` is rendered by `{Y : Scheme.{u}} [IsAffine Y]`, using
  the Mathlib scheme and affine-scheme notions recorded by `def-pc-scheme`.
- The structure morphism is rendered by `(f : Y ⟶ Spec (.of k))`.
- “Finite type” is rendered by `[LocallyOfFiniteType f] [QuasiCompact f]`,
  exactly the two Mathlib conditions specified by `def-weil-finite-type-morphism`;
  no stronger Noetherian, separated, finite-presentation, or integrality
  assumption appears.
- The coordinate ring is rendered by `Γ(Y, ⊤)`, and the induced `k`-algebra
  structure is explicitly the local instance
  `((f.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra`.
- The conclusion is exactly `Algebra.FiniteType k Γ(Y, ⊤)`, the notion in
  `def-weil-pbc-finite-type-algebra`. The `letI` scope makes clear that this is
  finite generation for the induced structure, rather than an unrelated
  algebra structure.

Clause-by-clause, the theorem therefore says precisely: an affine `Y` over a
field with a finite-type structure morphism has finitely generated global
sections as a `k`-algebra. Quantifier order and the universe are unchanged.
No mismatch was found, so no Lean or node statement was changed.

Edge cases checked: `Y = Spec k` gives `B = k`; affine space gives a polynomial
algebra; finite disjoint unions give finite products; the empty affine scheme
is not excluded and its zero global-sections ring is allowed; `n = 0` is
allowed by `Algebra.FiniteType`; and no characteristic restriction is present.
The shared universe `u` permits all cases covered by the node.

Searches for an existing exact declaration, using queries different from the
worker's: LeanFinder (`affine scheme finite type field global sections finite
type algebra`) returned only broader affine-pair and finite-morphism results;
Loogle (`Algebra.FiniteType IsAffine Γ scheme field`) returned no hits because
`IsAffine` is not a Loogle identifier; and grep over Mathlib, the source
repository, and `lean/Sheaf` found the broader
`AlgebraicGeometry.IsAffineOpen.algebra_finiteType_of_field` and related
affine-pair declarations, but no declaration with this whole-scheme statement
or name. The broader declaration has an affine-open argument and therefore is
not an exact replacement for this node.

Compilation with `scompile.py` succeeded with no errors or warnings. The
second reading found no mismatch and made no changes.
