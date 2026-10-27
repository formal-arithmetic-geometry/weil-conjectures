## Worker report

The delivery states `AlgebraicGeometry.GeneralLinearGroup.exists_eigenline_of_isCommMonObj`
in `Sheaf.AlgebraicGeometry.CommutativeGroupRepresentationEigenline`. Its proof is `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The original node is changed only in `lean`.

Source read: Milne, Algebraic Groups (2017), Definition 16.1 (printed p.324),
Lemma 16.11 (p.327), and Corollary 16.14 (p.329), directly from the repository PDF.
Definition 16.1 identifies trigonalizability with a nonzero eigenvector in every
nonzero representation, including the coaction condition v tensor a. Corollary
16.14 assumes commutativity and algebraic closure, with no smoothness hypothesis.
The docstring records all five steps of the node's universal-coefficient proof.

Hypothesis-by-hypothesis correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- A k-group scheme: `G : Over (Spec (.of k))` with `[GrpObj G]`.
- Affine: `[IsAffine G.left]`.
- Finite type: `[LocallyOfFiniteType G.hom]`; quasi-compactness is automatic
  because G and Spec k are affine. Mathlib's Morphisms/Affine.lean supplies
  `IsAffineHom G.hom` and then `QuasiCompact G.hom`. Omitting a redundant
  quasi-compact binder follows the prohibition on hollow hypotheses; it does
  not omit the mathematical finite-type condition.
- Commutative multiplication, unchanged by swapping factors: `[IsCommMonObj G]`.
  Its defining field is `(beta_ G G).hom` followed by multiplication equals
  multiplication, exactly the node's condition.
- Finite-dimensional vector space V: `{V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]`, with independent vector-space universe v.
- Nonzero V: `[Nontrivial V]`.
- Chosen basis: finite index `{n : Type u} [Fintype n] [DecidableEq n]` and
  `b : Module.Basis n k V`. The theorem is for any such basis. The index can
  always be `ULift (Fin (Module.finrank k V))`, so no finite-dimensional space
  is excluded by the matrix universe convention.
- Rational group-scheme representation: `r : G` to `GeneralLinearGroup n k`
  with `[IsMonHom r]`, rather than an arbitrary abstract action of G(k).

Conclusion clause-by-clause:

- A subspace L of V: `exists L : Submodule k V`.
- Dimension one: `Module.finrank k L = 1`.
- A character: `exists chi : G` to `GeneralLinearGroup
  (LinearGroupSchemes.Index.{u} 1) k`, together with `IsMonHom chi`.
  The node explicitly defines G_m as GL_1. This uses precisely GL_1 and its
  existing group law, without replacing the character by an arbitrary scalar
  family or merely an abstract homomorphism of rational-point groups.
- All commutative k-algebras: `forall (A : Type u) [CommRing A] [Algebra k A]`.
  This is the existing Scheme.{u}/GL_n functor-of-points convention, the same
  universe as k and G, so the coordinate algebra k[G] and its tensor square
  are among the tests. There is no Nontrivial, reducedness or field assumption
  on A. Universes can be enlarged uniformly for larger test algebras.
- Every point: `g : (Spec (.of A)).asOver (Spec (.of k))` to G.
- The point-action matrix is the existing `homMulEquiv n k A (g >> r)`.
  `Matrix.GeneralLinearGroup.toLin' (b.baseChange A)` turns it into the
  corresponding A-linear automorphism of the actual `A tensor_k V`.
- G-stability is the explicit first conjunct: every z in
  `LinearMap.range (L.subtype.baseChange A)` is carried into that same range.
  The range is the image of the canonical inclusion A tensor L to A tensor V;
  since k is a field, it identifies with A tensor L. The condition is on
  every element, not only generators or rational points.
- The character formula is the second conjunct, for every `x` with `x in L`:
  the automorphism sends `1 tensor x` to the scalar `(0,0)` entry of the
  one-by-one matrix `homMulEquiv (Index 1) k A (g >> chi)` times `1 tensor x`.
  This entry is the unit chi_A(g) viewed in A. Thus the scalar action is
  exactly the action of the character on the restricted line.
- No Smooth, IsReduced, ConnectedSpace, CharZero, faithfulness or connectedness
  hypothesis occurs.

Dependency declarations read and used:

- `Field`: Mathlib.Algebra.Field.Defs, the match for def-weil-field.
- `IsAlgClosed`: Mathlib.FieldTheory.IsAlgClosed.Basic, the algebraically
  closed-field clause recorded by def-weil-algebraic-closure. No particular
  algebraic closure of another field is needed here.
- `CategoryTheory.GrpObj`, `IsCommMonObj`, `IsMonHom`: Mathlib.CategoryTheory.Monoidal.Grp
  and Mon, as specialized and documented in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs for def-sc-group-scheme.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`:
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact, the recorded
  finite-type terminology. The latter is inferred from affineness.
- `AlgebraicGeometry.GeneralLinearGroup`, `GeneralLinearGroup.homMulEquiv`:
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear, the existing GL
  scheme and its natural matrix-valued point identification, used by the
  recorded module Sheaf.AlgebraicGeometry.LinearGroupSchemes.
- `LinearGroupSchemes.Index`: Sheaf.AlgebraicGeometry.LinearGroupSchemes,
  the recorded module of def-sc-general-linear-group; `Index 1` is `ULift (Fin 1)`.
  The recorded main declaration `specialLinear` owns the whole GL/SL node;
  this item uses its already-existing GL component and index, not SL.
- `Spec`, `Spec.map`: Mathlib.AlgebraicGeometry.Scheme, for def-weil-affine-spectrum.
- `TensorProduct`, `LinearMap.baseChange`, `Module.Basis.baseChange`,
  `Matrix.GeneralLinearGroup.toLin'`: existing module tensor, scalar extension,
  base-changed basis, and basis-to-matrix conversion. No duplicate construction.
- Proof import Mathlib.RingTheory.TensorProduct.Maps provides the algebra tensor
  product, `Algebra.TensorProduct.productMap` and its universal formulas for
  lem-weil-pbc-algebra-tensor-pushout-universal-property; the tensor definitions
  also supply def-weil-pbc-module-tensor-product.
- Proof import Sheaf.LinearAlgebra.CommutingEndomorphismsCommonEigenvector
  provides `Module.End.exists_common_eigenvector_of_commute`, the recorded
  declaration for lem-sfb-commuting-endomorphisms-common-eigenvector.

All statement dependencies are available through public imports; additional
proof dependencies are imported without public visibility.

Edge cases checked mathematically before drafting:

- V = 0 is excluded by exactly the node's nonzero hypothesis. An empty basis
  index cannot be a basis for a Nontrivial vector space. No extra dimension
  bound or Nonempty index binder is added.
- Dimension one: L is the whole space and the character is the rank-one action.
- The trivial group gives any line and the trivial character.
- Nonreduced commutative groups in positive characteristic, such as alpha_p,
  are allowed. Testing only G(k) would lose their infinitesimal action; the
  universal algebra and all-algebras quantification retain it.
- Disconnected commutative finite groups, and characteristic p torsion, remain
  allowed; neither connectedness nor characteristic zero occurs.
- A = 0 is allowed: its tensor modules vanish and the unique GL_1 point has
  scalar entry 0 = 1, so both conditions hold.
- The scalar formula uses GL_1, whose sole entry is a unit, including over
  nonreduced A; no regularity or invertibility condition is accidentally lost.

Searches actually run (2026-10-24):

- msearch.py leanfinder: "Every rational representation of a commutative affine
  group scheme over an algebraically closed field has an invariant line and a
  character". Eight hits about AffineSpace and pointsPi; no matching theorem.
- msearch.py loogle: "GeneralLinearGroup, IsCommMonObj". Zero hits; the service
  reported unknown identifier GeneralLinearGroup. This is not evidence that
  the GL scheme is missing: its project declaration was found and read.
- msearch.py grep: "eigenline|common_eigen|invariant.*line", RepresentationTheory.
  Twenty invariant/coinvariant results, no all-algebras eigenline theorem.
- msearch.py leansearch: "commutative affine algebraic group representation
  invariant one dimensional subspace". Eight hits on abstract Representation
  invariants and their maps; none states the requested scheme-character result.
- rg in lean/WeilConjectures and lean/Sheaf and dag/lean_names_upstream.json for
  eigenline, common_eigen, commutative representations, and the proposed name.
  Existing common-eigenvector theorem is linear algebra only; cyclic-closure
  and tangent-weight results have different objects/hypotheses. No duplicate.
- grep -rn for the node id in lean/WeilConjectures: no hits.
- Read GL, rational-representation and comodule-dictionary modules; existing
  RationalHom.representation works only on k-points, so it is not used as a
  replacement for the all-algebras condition. Its docstring explicitly warns
  of the characteristic-zero/density restriction for that stability notion.

Validation: prescribed scompile.py compiled this one module both as a sandbox
and under its final library module name, cleanly (7.5 and 8.6 seconds). No errors
or warnings were printed. No proof was supplied. There is no statement dispute.

## Second reading by Q42

Author's separate clause-by-clause self-check; the maintainer performs the
independent review, as required by this dispatcher's brief. I reread the node,
Milne pp.324/327/329, and the complete final theorem. The field, commutative
scheme group, affineness, finite-type condition, arbitrary finite-dimensional
nonzero space and basis, and group-homomorphism representation match the binders.
The image of the actual tensor inclusion implements stability; the character
is a scheme homomorphism to the exact GL_1 of the node, and its sole matrix
entry supplies the displayed scalar for all A, g and x in L. The two conditions
share the same line and character. No action is inferred merely from k-points.
The redundant QuasiCompact binder was omitted because affineness already
supplies it; this is explained above and in the module docstring. I found no
mathematical mismatch requiring a statement correction or dependency repair.
