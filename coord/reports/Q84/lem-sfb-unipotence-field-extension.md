## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.UnipotenceFieldExtension` states
`AlgebraicGeometry.unitriangularEmbedding_iff_baseChange`, with its sole proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.

Source read: Milne, Algebraic Groups (2017), printed pp.279--282, particularly
Proposition 14.3, Theorem 14.5(a),(b), and Corollary 14.9 including its proof.
Corollary 14.9 applies to arbitrary extensions and arbitrary affine algebraic groups,
including nonreduced groups. Its representation-theoretic notion is equivalent to
closed unitriangular embeddings by Theorem 14.5. The six-step DAG proof is included
in the theorem docstring, including the fixed-line induction and coordinate surjectivity.

Clause-by-clause correspondence:

- The fields k and K are `{k K : Type u} [Field k] [Field K]` and their arbitrary
  extension is `[Algebra k K]`. No perfectness, separability, finite-degree, or
  algebraic-extension instance is assumed.
- The k-group scheme is `G : Grp (Over (Spec (.of k)))`, carrying its actual group law.
  Affineness is `[IsAffine G.X.left]`. Finite type is exactly the recorded conjunction
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- Unipotence over k is the left existential. The size is `n : ℕ` with `0 < n`, and
  `r : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k` is a closed group embedding
  through `IsClosedSubgroupScheme r`, which includes group compatibility and a closed
  immersion of underlying schemes. The redundant all-points injectivity in that
  established class is a consequence of being a closed immersion, not an extra restriction.
- For every commutative k-algebra R, the quantifier
  `∀ (R : Type u) [CommRing R] [Algebra k R] (x : ... ⟶ G.X)` includes every R-valued
  point. Under `GeneralLinearGroup.homMulEquiv`, diagonal entries equal 1 and entries
  `(i,j)` with `j < i` equal 0. The remaining upper entries are unrestricted.
  These are the equations cutting out U_n as a closed subgroup of GL_n; a closed
  embedding in GL_n satisfying them factors as a closed embedding in U_n, since its
  surjective coordinate map factors surjectively through the defining quotient.
  Conversely compose a closed embedding in U_n with its closed inclusion in GL_n.
  Thus no unitriangular-group construction or new definition is needed to state the node.
- G_K is exactly
  `((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj G)`.
  Its underlying scheme is the prescribed fibre product and its structure map is
  the second projection; `mapGrp` transports multiplication, unit and inverse.
  This is the recorded base-change construction, not an arbitrary chosen group structure.
- The right existential repeats the same closed-embedding and all-test-algebra
  equations over K. The two sizes are independent, as the statement requires.
  The equivalence is `↔`. No smoothness or connectedness assumption occurs.

Dependency interfaces read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, class and docstring at 168--180.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`/`Grp` and the group-scheme convention
  in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. The bundled G supplies GrpObj G.X.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  and `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact. The classes and
  module docstrings confirm that finite type means their conjunction.
- `def-sc-group-scheme-subgroup`: `IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs; read its extension of
  `IsSubgroupScheme`, the latter's `IsMonHom` and test-algebra injectivity fields,
  and its underlying `IsClosedImmersion` field.
- `def-weil-closed-immersion`: `IsClosedImmersion`, Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  the closed-embedding plus stalk-surjectivity class.
- `def-sc-general-linear-group`: import its recorded module
  Sheaf.AlgebraicGeometry.LinearGroupSchemes, which reuses the upstream
  `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv` from
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear. Read that full module:
  GL is Spec of the determinant-localized matrix coordinate ring, and homMulEquiv
  identifies every algebra-valued point with an invertible matrix. `ULift (Fin n)`
  is only the universe-compatible index set, canonically equivalent to Fin n.
- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs, with structure
  morphism `Spec.map (CommRingCat.ofHom (algebraMap k K))`.
- `def-pc-base-change`: import WeilConjectures.AlgebraicGeometry.BaseChangeConventions;
  its module documentation records `Over.pullback`, the prescribed fibre product
  and its projections. Read Mathlib's `Functor.mapGrp` and cartesian Over interface
  for the canonical induced group structure.

The imports also include the stated proof-dependency modules: affine fibre products,
tensor pushouts, basis extension, module tensor products, quotient algebras,
AffineFiniteTypeAlgebra, and RationalRepresentationComoduleDictionary. The DAG's
unitriangular fixed-vector theorem, rational fixed-space comparison and faithful
linear representation theorem have no usable Lean record yet; no import is invented
for these proof-only prerequisites.

Edge cases checked: K=k gives the identity-extension equivalence. The trivial group
is included with n=1. Neither side is allowed n=0. Characteristic p infinitesimal
examples such as alpha_p remain covered because the equations are imposed over all
commutative algebras, including nonreduced algebras, rather than only over fields.
Disconnected finite unipotent groups are not excluded. Imperfect fields and
transcendental extensions are included. Test algebras include the zero ring.
The common ambient universe is arbitrary; the scheme and GL interfaces use Scheme.{u}
and k,K,R : Type u. This imposes no cardinality restriction: any chosen fields and
finite-type scheme fit in a common universe. All binders and the universe are explicit,
with autoImplicit disabled.

Searches actually run:

- msearch leanfinder: "An affine algebraic group is unipotent if and only if its scalar
  extension to a field extension is unipotent": eight unrelated geometric-reducedness
  and unramifiedness results, no matching theorem.
- msearch loogle: "IsUnipotent, AlgebraicGeometry": zero results; unknown IsUnipotent.
- msearch grep: "unipotent|Unipotent|unitriangular|Unitriangular" in AlgebraicGeometry:
  no Mathlib hits.
- msearch leansearch: "unipotence of an affine algebraic group is invariant under field
  extension": eight unrelated unramifiedness, invariants and field results, no match.
- msearch grep: "unitriangular|Unitriangular|unipotent.*base|Unipotent.*base": no Mathlib hits.
- rg of WeilConjectures, Sheaf, and dag/lean_names_upstream.json for unipotent,
  unitriangular and field/base-change names: no exact statement. The node-id search
  in WeilConjectures also returned no match. Sheaf's SolvableGroupStructure.IsUnipotent
  includes Smooth and therefore cannot express this node. Existing
  CharZeroCommutativeUnipotentVectorGroup and AdjointKernelCentralQuotientUnipotent
  use the same closed-GL-embedding plus universal unitriangular-equations formulation;
  their full signatures and docstrings were read and reused as the interface pattern.

No STATEMENT-DISPUTED issue or node fault was found. Compilation and the delivery
preflight are run through the prescribed server wrappers.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
