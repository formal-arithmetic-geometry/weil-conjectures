## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.UnipotentRationalRepresentationFixedVector`
states `AlgebraicGeometry.exists_nonzero_fixedVector_of_faithful_unipotent` with one
`sorry` proof. It introduces no definitions. The item's natural-language statement,
statement dependencies, proof and proof dependencies are unchanged; only `lean` changes.

Hypothesis and conclusion correspondence:

- An algebraically closed field K is `(K : Type u) [Field K] [IsAlgClosed K]`.
  Mathlib's `IsAlgClosed` is explicitly equivalent to every nonconstant polynomial
  having a root (`IsAlgClosed.exists_root` and `IsAlgClosed.of_exists_root`).
- The K-group scheme is `(U : Over (Spec (.of K))) [GrpObj U]`. Its underlying
  scheme is `U.left`, and its structural morphism is `U.hom`.
- Affineness is `[IsAffine U.left]`, smoothness is `[Smooth U.hom]`, and finite
  type is `[LocallyOfFiniteType U.hom] [QuasiCompact U.hom]`. All three properties
  in the node are retained, including the local finite-type hypothesis implied by
  smoothness and the quasi-compactness available for morphisms of affine schemes.
- The faithful representation's positive rank is `(m : ℕ) (_hm : 1 ≤ m)`.
  The morphism is `i : U ⟶ GeneralLinearGroup (ULift.{u} (Fin m)) K` with
  `[IsMonHom i]`. This is a group-scheme homomorphism, not merely a scheme map.
- Faithfulness is `_hfaithful`, universally quantifying `(R : Type u)` with
  `[CommRing R] [Algebra K R]` and requiring `Function.Injective` on `x ↦ x ≫ i`.
  Its domain is the actual set of morphisms `Spec R → U` over `Spec K`.
  No reducedness or field condition is imposed on R. The common universe u is
  the existing group-scheme API convention; it includes the coordinate algebras
  needed to detect scheme-theoretic faithfulness. Faithfulness on all such affine
  tests is equivalent to monicity, hence also to faithfulness after universe lift;
  this does not silently replace faithfulness by injectivity on K-points.
- The pointwise unipotence assumption is `_hunipotent`: for every
  `x : (Spec (.of K)).asOver (Spec (.of K)) ⟶ U`, there is a natural N with
  `1 ≤ N` and `(matrix - 1) ^ N = 0`. `homMulEquiv` converts `x ≫ i` to the
  corresponding invertible matrix, and `.val` takes its underlying matrix.
  The existential lies inside the point quantifier, so N may depend on x.
- Every positive representation rank is an arbitrary `(d : ℕ) (_hd : 1 ≤ d)`.
  Every rational representation is the arbitrary morphism
  `ρ : U ⟶ GeneralLinearGroup (ULift.{u} (Fin d)) K` with `[IsMonHom ρ]`.
  These theorem parameters are universally quantified, as required.
- The conclusion is `∃ v : ULift.{u} (Fin d) → K, v ≠ 0 ∧ ...`.
  `ULift (Fin d)` is canonically equivalent to `Fin d`, so these are exactly d
  column coordinates, with no change to dimension or nonvanishing. This is the
  same index convention used by the dependency's `LinearGroupSchemes.Index`.
- The last clause quantifies every actual K-point x and requires
  `Matrix.mulVec (homMulEquiv ... (x ≫ ρ)).val v = v`, the ordinary matrix action
  in the node. A single vector is fixed simultaneously by every point.

Dependency declarations read and used:

- `def-weil-field`: `Field` from `Mathlib.Algebra.Field.Defs`, the field class.
  `IsAlgClosed` is from `Mathlib.FieldTheory.IsAlgClosed.Basic`, lines 58-64,
  including its docstring explaining the root criterion.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, lines 59-65.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` from
  `Mathlib.CategoryTheory.Monoidal.Grp`, lines 40-47, and `IsMonHom` from
  `Mathlib.CategoryTheory.Monoidal.Mon`, lines 211-215. Read the group-scheme
  interpretation in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, lines 39-46, and `QuasiCompact`
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, lines 38-46.
- `def-sc-general-linear-group`: imported its recorded module
  `Sheaf.AlgebraicGeometry.LinearGroupSchemes`. Its record and module explicitly
  reuse `AlgebraicGeometry.GeneralLinearGroup` and
  `AlgebraicGeometry.GeneralLinearGroup.homMulEquiv` from the public upstream
  import `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
  Read that upstream file in full: GL is the affine spectrum of the localized
  determinant coordinate algebra and `homMulEquiv` identifies points with
  invertible matrices as groups. The newly constructed special-linear scheme is
  not the object used here. No duplicate GL construction is introduced.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`, lines 469-480. `asOver` supplies the canonical
  structural morphism of the spectrum of a K-algebra.

The two non-definition proof dependencies,
`lem-sfb-rational-representation-unipotent-point` and
`lem-sfb-unipotent-matrix-group-fixed-vector`, have no recorded declarations or
Mathlib matches in the node files read. They are not needed to type the statement
and therefore introduce no dependency-module work in this statement delivery.
They remain in the unchanged proof plan and are named step by step in the
statement's docstring. The defined proof dependencies are already public imports.

Source and edge checks:

Read the current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`.
The alteration/GIT chain is the intervening DAG provenance, not a new assertion
inserted into that unit. Read Milne's PDF, printed pp.279-283 (PDF pp.291-295):
Proposition 14.1, Proposition 14.3, the section 14.b fixed-vector definition,
and Corollary 14.12 give exactly the stated interpretation. The retained proof
uses the pointwise representation-independence input followed by Proposition 14.1.

For the trivial group every nonzero vector is fixed. At d=1 the assertion says
that all scalars in the representation are 1; no zero-coordinate vector can
satisfy the nonzero clause. At m=1 the faithful unipotent representation forces
the group to be trivial on K-points, which is consistent. Rank zero is excluded
by the original node: d=0 would make the conclusion false, and m=0 is not
introduced. No connectedness, characteristic-zero, finite-group or uniform
nilpotence-exponent hypothesis is added: disconnected finite p-groups in
characteristic p remain covered. The quantifier for all commutative K-algebras
includes nonreduced rings; the zero ring is allowed as a test algebra. A group
scheme has its identity section, so the empty scheme cannot satisfy `GrpObj U`.
The field and group-scheme universe is arbitrary u. No statement fault found.

Searches actually run (msearch.py, Q17 and this item's id):

- LeanFinder: `Every rational representation of a smooth affine unipotent algebraic
  group over an algebraically closed field has a nonzero fixed vector` returned
  eight hits about Hilbert 90, parabolic fixed points, sl2 vectors and Lie algebra
  regularity/triangularizability; none states this algebraic-group theorem.
- Loogle: `"unipotent", "fixed"` returned zero hits.
- Mathlib grep: `unipotent|Kolchin|fixed.*vector` returned eleven hits, concerning
  Euclidean vectors, PSL stabilizers, biproduct matrices and tactic text; no match.
- LeanSearch: `A unipotent algebraic group has nonzero invariants in every nonzero
  rational representation` returned eight hits in representation theory, including
  `Representation.invariants`, `Representation.mem_invariants` and invariant-functor
  definitions, but none asserts this nonvanishing theorem.
- Project searches: `rg` for `unipotent|Unipotent|Kolchin` in `lean/WeilConjectures`
  found only unrelated strict-Weil-complex and derived-biproduct modules; searching
  the exact item id there found none. `rg` in `lean/Sheaf` for fixed-vector and
  unipotence patterns found proof-plan references and definitions of smooth
  unipotent groups, but no existing theorem with this signature. In particular,
  `SimpleModuleDualHighestWeight` refers to this node in its proof plan, and
  `SmoothUnipotentExtension` refers to the different unitriangular-subgroup lemma.
  The upstream declaration index also has no matching fixed-vector declaration.

Validation: scompile.py compiled the module on the server against current sources
in 2.3 seconds with no Lean errors or warnings. The wrapper's earlier sandbox
artifact attempt reported disk-full, then its prescribed current-source confirmation
succeeded with exit 0. No direct compiler or global build was invoked.

## Second reading by Q17

A separate reading pass by this worker (no other agent was started, as directed)
checked the node and final module side by side. In particular, faithfulness is on
all algebra points, whereas unipotence and the final invariance clause are on
K-points; these quantifiers are deliberately different. The same K, U, i and rho
occur throughout. The positive rank conditions are retained twice, the exponent
is existential for each point, and the conclusion supplies one common nonzero
vector. Smoothness is explicit even though the pointwise proof plan can avoid it.
The only adjustment was to import the general-linear dependency's recorded module
rather than just its upstream GL import. No mathematical mismatch or statement
correction was found. Independent maintainer review remains the delivery review.
