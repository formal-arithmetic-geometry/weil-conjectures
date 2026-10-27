## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.MonomorphismClosedImmersion`
states `AlgebraicGeometry.isClosedImmersion_of_injective_algebraPoints`.
Its sole theorem has proof `by sorry`; there are no new definitions or helper
nodes. Only the item's `lean` field changes.

Source checked directly: Milne, Algebraic Groups (2017), Proposition 5.31(a),(b),
printed p.106, and the first proof of Theorem 5.34, printed p.107, using
Theorem 5.28. Read the local PDF via `pdftotext -layout`. Proposition 5.31(a)
uses injectivity for all small k-algebras; Theorem 5.34 gives closed immersion.
The docstring follows the node's four-step proof, including its prescribed
homogeneous-quotient route rather than Milne's alternative sketch.

Hypothesis and conclusion correspondence:

- A field k: `{k : Type u} [Field k]`.
- A and B are k-schemes: `(A B : Over (Spec (.of k)))`; their structure
  morphisms are `A.hom`, `B.hom`.
- Group structures: `[GrpObj A] [GrpObj B]`, the recorded definition of
  def-sc-group-scheme. They are not required to be commutative.
- Separatedness: `[IsSeparated A.hom] [IsSeparated B.hom]`. This uses the
  separatedness component of def-weil-proper-morphism, without imposing
  properness or universal closedness.
- Finite type: `[LocallyOfFiniteType A.hom] [QuasiCompact A.hom]` and
  `[LocallyOfFiniteType B.hom] [QuasiCompact B.hom]`. These are exactly the
  two components recorded by def-weil-finite-type-morphism.
- A homomorphism over k: `(u : A ⟶ B) [IsMonHom u]`. Being in Over enforces
  compatibility with the structure morphisms. IsMonHom expresses preservation
  of multiplication and identity; for group objects it also preserves inverse.
- Every commutative k-algebra R: `∀ (R : Type u) [CommRing R] [Algebra k R]`.
  The test rings use the same universe as k and the schemes; there is no
  independent smaller universe making the test condition vacuous.
- A(R) is the k-morphisms from Spec R to A:
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ A`.
  The same construction for B is the inferred codomain of `fun x => x ≫ u`.
- Injectivity of u(R): `Function.Injective` applied to exactly this
  postcomposition function. No Mono hypothesis or geometric-point condition
  replaces this assumption.
- Conclusion: `IsClosedImmersion u.left` on the underlying scheme morphism.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-sc-group-scheme: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp; `CategoryTheory.IsMonHom`,
  Mathlib.CategoryTheory.Monoidal.Mon. The specialization to
  `Over (Spec (.of k))` is documented in and imported from
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. No private notion is used.
- def-weil-proper-morphism: `AlgebraicGeometry.IsSeparated`,
  Mathlib.AlgebraicGeometry.Morphisms.Separated, publicly available through
  the recorded Mathlib.AlgebraicGeometry.Morphisms.Proper module.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- def-weil-closed-immersion: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- Proof dependencies: `CategoryTheory.Limits.pullback` (HasPullback module),
  `AlgebraicGeometry.Spec` and `Spec.map` (Scheme module), and
  `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`
  (ClosedImmersion module) are imported. The last is the recorded Mathlib match
  for lem-weil-pbc-closed-immersion-base-change.
- lem-sfb-trivial-kernel-homogeneous-quotient currently has no Lean record or
  Mathlib match. It is only a proof dependency and supplies no term in this
  statement, so its future module cannot yet be imported. Its required use is
  explicitly retained in the proof docstring. All statement dependencies have
  usable declarations; no dependency repair or extra definition is necessary.

Edge cases checked before writing:

- The trivial group scheme and identity homomorphism satisfy the intended
  statement. Empty group schemes over a field are impossible because of the
  identity section, and no separate Nonempty hypothesis is added.
- The zero k-algebra is allowed: CommRing does not demand Nontrivial. Its
  spectrum is empty, and both point sets are singletons.
- Nonreduced rings and group schemes are allowed. In characteristic p the
  Frobenius of the additive group fails the hypothesis on nonreduced test
  algebras; testing only fields would incorrectly admit it.
- Arbitrary characteristic, imperfect fields, disconnected groups and positive
  dimensional groups are included. No smoothness, reducedness, affineness,
  properness or finite-morphism hypothesis is present.
- Finite type includes quasi-compactness on both structure maps, without
  replacing it by mere local finite type. Algebra-valued points use the
  scheme/base universe u; every affine open chart can be tested at that size.

Searches for existing statements (2026-10-24):

- msearch.py leanfinder: "An injective homomorphism of separated finite type
  group schemes over a field is a closed immersion"; 8 results. These include
  `IsClosedImmersion.iff_isFinite_and_mono` and separatedness/closed-immersion
  facts, but no group-scheme theorem. The finite-and-mono result assumes a
  finite morphism, which the item does not assume.
- msearch.py loogle: `"GrpObj", "IsClosedImmersion"`; 0 results.
- msearch.py leansearch: "An injective homomorphism of algebraic group schemes
  of finite type over a field is a closed immersion"; 8 results, all general
  immersion definitions/facts and the finite-and-mono criterion, no exact match.
- msearch.py grep: `mono.*closed|closed.*mono|injective.*closed` in
  AlgebraicGeometry; 20 hits, including proper-and-mono and finite-and-mono
  criteria. Neither supplies this statement from finite-type group schemes.
- Local rg in lean/WeilConjectures and lean/Sheaf for monomorphism/closed,
  injective/closed, and the exact node id found the consumer
  GroupScheme.HomomorphismFactorization and unrelated general results.
  Targeted reads of GroupScheme.Basic and GroupScheme.Image found closedness
  of the image, translations of closed immersions, and images under properness,
  not the item. The exact node id does not occur in an upstream declaration.
  The proposed theorem name has no pre-existing declaration in these sources
  or Mathlib. Search result summaries are retained in sandbox searches.jsonl.

No statement fault or STATEMENT-DISPUTED issue was found. No statement
correction, new node, or dependency module is delivered.

Validation: prescribed scompile.py compiled the sandbox probe and final library
module separately on the server, with no error or non-sorry warning (3.1 s and
2.1 s respectively). The file uses module mode, exposed public declarations,
explicit universe u and `set_option autoImplicit false`.

## Second reading by Q78

Author's consistency reread, not an independent worker review: the dispatcher
explicitly prohibits starting other agents and assigns independent review to
the maintainer. I reread the node and final signature clause by clause. Field k
matches Field; both separated finite-type k-group schemes match Over, GrpObj,
IsSeparated, LocallyOfFiniteType and QuasiCompact for A and B; the homomorphism
matches u and IsMonHom; every k-algebra and the stated A(R), B(R) match the
quantifier and affine Over object; the function is postcomposition by u;
IsClosedImmersion u.left is exactly the conclusion. In particular, B is not
assumed proper, neither group is assumed commutative, and injectivity is not
restricted to reduced algebras or points over fields. No mismatch was found
and no change to the mathematical statement was made. The sole postponed
proof is the recorded theorem, with all four DAG steps in its docstring.
