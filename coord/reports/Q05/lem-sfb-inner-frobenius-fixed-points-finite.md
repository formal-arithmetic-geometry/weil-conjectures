## Worker report

The module `Sheaf.AlgebraicGeometry.InnerFrobeniusFixedPointsFinite` states
`AlgebraicGeometry.inner_frobenius_fixedPoints_finite`, with its only proof `sorry`.
The node's statement and dependency lists are unchanged. No new definitions or dependency
repairs are needed. The source is Milne, Algebraic Groups (2017), Theorem 17.96, proof,
printed pp.382–383 (PDF pages 394–395). I read that proof and its preceding Frobenius
paragraph, as well as the current latest blueprint unit sk-thm-sf-ctf-stability.

Hypotheses and conclusion, clause by clause:

- A finite field k is `(k : Type u) [Field k] [Fintype k]`. Fintype supplies the enumeration
  used by Mathlib's recorded Frobenius; it is equivalent to finiteness, with no bound on
  the finite field. The node's q is `Fintype.card k`, so no separate cardinality assumption
  or chosen prime-power presentation is necessary.
- An algebraic closure is `(Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]`.
  This is an arbitrary closure, not just the concrete `AlgebraicClosure k` construction.
- The group scheme is `(A : Over (Spec (.of k))) [GrpObj A]`.
- Affineness is `[IsAffine A.left]`.
- Finite type over k is `[LocallyOfFiniteType A.hom] [QuasiCompact A.hom]`, exactly the
  conjunction specified in the dependency's record.
- The coordinate algebra C is already the canonical `Γ(A.left, ⊤)` with `A.hom.ΓAlgebra`.
  Rather than copy its point group law to algebra homomorphisms, the statement uses
  `points A Ω`: actual scheme morphisms over k. The existing
  `A.hom.overHomEquivAlgHom Ω` identifies these with `C →ₐ[k] Ω`. Its full construction
  and naturality were read in `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.
  The implementation takes a point's global-section map followed by `ΓSpecIso`.
- The arithmetic Frobenius is
  `points.map A (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toAlgHom`.
  `points.map` precomposes by the spectrum of the displayed algebra homomorphism;
  contravariance of global sections makes this postcomposition on C-valued coordinates.
  Mathlib's `coe_frobeniusAlgEquivOfAlgebraic` says that coefficient map is exactly
  `z ↦ z ^ Fintype.card k`. Thus the orientation is arithmetic Frobenius, not its inverse.
- Every geometric point x is `(x : points A Ω)`.
- The exact fixed set is `{v : points A Ω | x * points.map A (...) v * x⁻¹ = v}`.
  Multiplication and inverse come from the given `GrpObj A`, via `Hom.group`, enabled by
  `open scoped MonObj`. There is no arbitrary group structure or arbitrary action.
- The conclusion `Set.Finite` is finiteness of that set, with no cardinality formula or
  additional conclusion. There is no smoothness, connectedness, reducedness, or
  commutativity binder.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, Algebra.Field.Defs.
- `def-weil-finite-field-q-elements`: Mathlib `GaloisField`, FieldTheory.Finite.GaloisField;
  arbitrary finite fields are used through `Fintype`, as in the match's uniqueness clause.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosure` and `IsAlgClosed`,
  FieldTheory.IsAlgClosed.Basic (the match explicitly includes the abstract interface).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` in Mathlib.CategoryTheory.Monoidal.Grp,
  and `CategoryTheory.Hom.group` in Mathlib.CategoryTheory.Monoidal.Cartesian.Grp.
  The recorded specialization to `Over (Spec (.of k))` was read in the upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs module.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and Morphisms.QuasiCompact.
- `def-weil-frobenius-substitution`: `FiniteField.frobeniusAlgEquivOfAlgebraic`,
  Mathlib.FieldTheory.Finite.Basic, with its explicit cardinality-power formula.
- The existing `AlgebraicGeometry.points` and `points.map` in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring provide exactly the needed
  functor-of-points evaluation and canonical coefficient map, and are used directly.
- Proof imports: Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
  (`affine_finiteType_algebra_of_field`), Sheaf.FieldTheory.UniqueSubfieldOfClosure
  (`FiniteField.exists_unique_subfield_of_closure`), Mathlib.RingTheory.FiniteType
  (`RingHom.FiniteType`/`Algebra.FiniteType`), and
  Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
  (`IntermediateField.finiteDimensional_adjoin`). These are plain proof imports;
  statement dependencies are public imports, including the transitive group and spectrum
  imports. Their signatures and docstrings were read. The theorem docstring records
  all seven proof steps and their DAG inputs.

Edge cases checked before writing: for x = 1 this is ordinary Frobenius-fixed-point
finiteness; for the trivial group the set is a singleton, also covering an empty coordinate
family. For μ_p over characteristic p the geometric point set is a singleton; nilpotents
cause no extra restriction. For G_m the condition reduces to the usual finite root set.
Finite noncommutative constant groups and disconnected finite groups are included, with
conjugation in the correct order. No characteristic is excluded (finite fields already
have positive characteristic), and there is no exponent n = 0 hypothesis hidden in the
statement. Universe u is explicit and arbitrary; it is the common scheme/ring universe
required by the existing scheme-points interface, and includes any finite field and its
algebraic closure. There are no auto-bound variables, local instances, or local notation.
No statement fault or dispute was found.

Searches for a pre-existing result:

- msearch.py leanfinder, query "inner twist Frobenius fixed points affine algebraic group
  finite": eight hits on field Frobenius, arithmetic Frobenius at a prime and abstract
  fixed fields; none is the theorem about affine group schemes.
- msearch.py loogle, query `"frobenius", "fixed"`: zero hits.
- msearch.py grep, query `frobenius.*(fixed|finite)|(fixed|finite).*frobenius`:
  eight hits on finite fields, perfect rings and Frobenius numbers; none is this statement.
- msearch.py leansearch, query "The fixed points of an inner twist of Frobenius on an
  affine finite type group over a finite field are finite": the returned field-Frobenius
  and abstract fixed-point results do not assert this theorem.
- rg in lean/WeilConjectures and lean/Sheaf for Frobenius/fixed points, inner twists,
  and the exact node id: ordinary finite-field Frobenius finiteness and semilinear
  vector-space results exist, but no inner-twisted affine-group finiteness theorem.
  `GroupScheme/Lie/Ring.lean` already gives points and points.map, so those are reused.
- rg for `inner_frobenius_fixedPoints_finite` in Mathlib and both project roots:
  no declaration-name conflict.

Validation: scompile.py compiled the sandbox and final module separately, each in 1.7 s,
with no errors or warnings. All compilation uses the prescribed live-server wrapper.

## Second reading by Q05

A second pass in this worker session read the node and completed module together. No
other agent was started, as the dispatcher brief expressly forbids it. The pass checked
all finite-field, algebraic-closure, affine-group and finite-type binders against the node,
then checked the coordinate interpretation using overHomEquivAlgHom and the actual
implementation of points.map. In particular, contravariant Spec gives postcomposition by
arithmetic q-power Frobenius, and multiplication reads x σ(v) x⁻¹, in that order. The
conclusion is finiteness of the exact fixed set. The proof docstring includes both iterate
identities and the non-smooth/disconnected cases. No mismatch was found and no statement
correction was made. The maintainer's independent delivery review remains separate.
