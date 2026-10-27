## Worker report

The module `Sheaf.AlgebraicGeometry.RationalRepresentationSemisimplePoint` states
`AlgebraicGeometry.rationalRepresentation_diagonalizable_of_faithful`, with its
entire proof postponed by `sorry`. No definitions, new nodes, dependency repairs,
or statement corrections are needed.

Source read: `literature/milne-algebraic-groups_iAG2017.pdf`, Theorem 9.18,
printed p.170, and Section 9.19, printed p.171, using `pdftotext -layout`.
The latter explicitly says that detection in one faithful representation implies
semisimplicity in all representations. Theorem 9.18 supplies the compatible
Jordan decomposition. Algebraically closed fields are perfect, so its source
hypothesis is satisfied in every characteristic. The theorem's docstring gives
all four steps of the DAG proof, including naturality, tensor and unit
compatibility, reconstruction of h, faithfulness at k, and substitution h = g.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field k is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The k-group scheme is `(J : Over (Spec (.of k))) [GrpObj J]`.
- Affineness is `[IsAffine J.left]`.
- Finite type is `[LocallyOfFiniteType J.hom] [QuasiCompact J.hom]`, exactly
  the recorded finite-type dependency's conjunction.
- Positive integral dimensions are `(m d : ℕ) (_hm : 1 ≤ m) (_hd : 1 ≤ d)`.
  These are precisely the positive integers of the node. The index type
  `LinearGroupSchemes.Index.{u} n = ULift.{u} (Fin n)` is an n-element set;
  it preserves every positive dimension and meets the upstream GL universe convention.
- The morphisms i and r have targets `GeneralLinearGroup (Index m) k` and
  `GeneralLinearGroup (Index d) k`, with `[IsMonHom i]` and `[IsMonHom r]`.
  These are group-scheme homomorphisms, with no separate arbitrary point action.
- Faithfulness `hi` quantifies over `(A : Type u) [CommRing A] [Algebra k A]`.
  A point is an actual morphism `(Spec (.of A)).asOver (Spec (.of k)) ⟶ J`.
  The map whose injectivity is required is exactly
  `fun x ↦ GeneralLinearGroup.homMulEquiv (Index m) k A (x ≫ i)`.
  Thus the injectivity concerns the specified matrix-valued i_A, on all test
  algebras in the scheme universe, without a reducedness or nontriviality assumption.
- The arbitrary rational point g is
  `(g : (Spec (.of k)).asOver (Spec (.of k)) ⟶ J)`.
- The hypothesis `hg` is existence of `P : GL (Index m) k` and a diagonal
  `a : Index m → k` such that `P⁻¹ * i_k(g) * P = Matrix.diagonal a`.
- The conclusion is the same existence and conjugation formula in dimension d,
  for `r_k(g) = GeneralLinearGroup.homMulEquiv (Index d) k k (g ≫ r)`.
- No smoothness, connectedness, reducedness, or characteristic-zero hypothesis is present.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`, line 180; the field structure of k.
- `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`, line 62;
  its docstring identifies polynomial splitting with having roots for all
  nonconstant polynomials. Also read the recorded `AlgebraicClosure` definition
  (AlgebraicClosure.lean:127) and `IsAlgClosure` (Basic.lean:264); the statement
  needs algebraic closedness of k, not a chosen extension of a smaller field.
- `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom`,
  `Mathlib.CategoryTheory.Monoidal.Grp` and `.Mon`, lines 43 and 213.
  These give the group object and homomorphisms of the recorded group-scheme node.
- `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, line 43;
  `AlgebraicGeometry.QuasiCompact`, `.Morphisms.QuasiCompact`, line 43.
- `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 470 and 479.
- The recorded GL node's `Sheaf.AlgebraicGeometry.LinearGroupSchemes` imports
  the exact upstream `AlgebraicGeometry.GeneralLinearGroup` and
  `GeneralLinearGroup.homMulEquiv` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
  Their complete definitions and docstrings were read: Spec of the localized
  generic-matrix coordinate algebra and its canonical multiplicative point equivalence.
  The recorded module's `LinearGroupSchemes.Index` is used directly.
  No second general-linear group or point identification is constructed.

The two proof dependencies, `lem-sfb-multiplicative-jordan-linear-compatibility`
and `lem-sfb-tannaka-rational-point-reconstruction`, have no Lean records or
upstream audit declarations in the current read clone. They are not needed to
state this item and therefore supply no proof imports yet. Both are explicitly
named, with their roles, in the theorem's proof docstring.

Edge cases checked before writing: m = d = 1 gives scalar conjugation; g = identity
has identity matrix in both representations; r can be trivial or nonfaithful;
J can be trivial, disconnected, or nonreduced in positive characteristic.
The formulation retains all these cases. Zero dimensions are excluded exactly
by the original node's m,d ≥ 1, while the proof's auxiliary zero representation
remains permitted by its proof dependencies. Test algebras include nonreduced
algebras and the zero ring; no extra condition is imposed on A. The shared universe u
is the existing scheme and GL convention, not an independent smaller test universe.

Searches actually run with `msearch.py Q91 lem-sfb-rational-representation-semisimple-point`:

- `leanfinder`: "An element of an affine group scheme diagonalizable in a faithful
  rational representation is diagonalizable in every rational representation".
  Eight hits: scheme diagonals and abstract `Rep.diagonal` constructions;
  no rational-representation detection theorem.
- `loogle`: "GeneralLinearGroup, IsDiagonalizable".
  Zero hits, with diagnostic `unknown identifier 'GeneralLinearGroup'`;
  this query was inconclusive, not evidence of nonexistence by itself.
- `grep`: "IsSemisimple|diagonali[sz]able", subdirectory `RepresentationTheory`.
  Twelve hits concerning abstract representations and semisimple modules;
  no matching group-scheme point theorem.
- `leansearch`: "An element diagonalizable in a faithful representation of an
  algebraic group is diagonalizable in every rational representation".
  Eight hits involving diagonal abstract representations, finite-group injectivity,
  invariants and a Lie-algebra radical result; no exact match.
- `rg` in project `lean/WeilConjectures` and `lean/Sheaf`, by node id,
  rational/semisimple/representation keywords, proposed declaration name and
  faithful/semisimple names; also `dag/lean_names_upstream.json`.
  Found the existing semisimple-point definition and cyclic-closure consumer,
  but no theorem proving faithful detection. Read both files: the definition
  requires every representation, so it does not imply the desired theorem.
  The consumer only mentions the present node in its proof plan.
- The required `grep -rn` of the node id in `lean/WeilConjectures` returned no matches.
- Matrix searches found diagonal-matrix algebra, with no exact replacement theorem.

The search wrapper's actual structured results are in the sandbox `searches.jsonl`.
Server validation with the prescribed `scompile.py` succeeded both for its sandbox
module and the library module (14.3 s and 5.1 s). No errors or unexpected warnings.

## Second reading by Q91

Author's final comparison for direct delivery; independent review belongs to the
maintainer, as the assignment specifies. Re-read the node and the complete Lean
signature, including the two existential conjugation formulas. The only apparent
encoding differences are the finite-index ULift (a bijective relabeling) and
positive integers as natural numbers with lower bounds. Both preserve the exact
objects and cases of the statement. Faithfulness uses the same canonical GL point
equivalence as both matrix formulas. Neither rationality nor faithfulness has been
replaced by an assumption on an abstract group representation. All original
hypotheses and the single conclusion are present; no mismatch or source error found.
