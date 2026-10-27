## Worker report

Item: lem-sfb-multiplicative-jordan-linear-compatibility.
Module: `Sheaf.LinearAlgebra.MultiplicativeJordanLinearCompatibility`.

The module states the existence and uniqueness, linear intertwiner, and tensor clauses as
three named theorems, each with proof `sorry`. A real Prop-valued helper,
`LinearEquiv.IsMultiplicativeJordanDecomposition`, packages exactly the decomposition
conditions intrinsic to this node. It introduces no independent notion or new DAG node.
All four declarations are listed in `lean.declarations`. The item is unchanged except for
its `lean` field. There is no statement correction, disputed statement, or dependency repair.

Source read: Milne, Algebraic Groups (2017), Theorem 9.11 and Propositions 9.13–9.15,
printed pp.168–170, PDF pp.180–182. The algebraically closed specialization of Theorem 9.11
matches the node. The source also states polynomial dependence, which this node does not
claim and the Lean does not add. Each theorem's docstring gives the relevant proof steps
of this node, including uniqueness on an eigenbasis and the characteristic-independent
tensor-primary calculation.

Hypotheses and clauses:

- The field is `{K : Type u} [Field K]`. Algebraic closedness is `[IsAlgClosed K]` in
  all three theorems. Mathlib's class means every polynomial splits; its documentation and
  `IsAlgClosed.exists_root` / `IsAlgClosed.of_exists_root` identify this with the node's
  root condition for nonconstant polynomials. This is no perfect-field or characteristic
  restriction beyond algebraic closedness.
- An arbitrary finite-dimensional vector space is `{V : Type v} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V]`. The second space has its own universe `w` and
  analogous binders. Neither space is assumed nonzero.
- Invertible linear maps `A`, `B` and all factors have type `V ≃ₗ[K] V` or `W ≃ₗ[K] W`.
  Thus no inverse is left unspecified and no surjectivity hypothesis is dropped.
- `A = S * U ∧ A = U * S` in the predicate says precisely `A = A_s A_u = A_u A_s`.
  `LinearEquiv.mul_apply` confirms multiplication is composition in the node's order.
- Diagonalizability is expressed directly as
  `∃ (n : ℕ) (b : Module.Basis (Fin n) K V) (a : Fin n → K),
  ∀ i : Fin n, S (b i) = a i • b i`.
  It specifies a full eigenbasis, not a spanning family without independence. In finite
  dimension every basis has a finite indexing set that can be reindexed by `Fin n`.
- Unipotence is `∃ N : ℕ, 1 ≤ N ∧ (U.toLinearMap - LinearMap.id) ^ N = 0`.
  Positive natural numbers are precisely the integers at least one in the node. The
  power is in the endomorphism ring, not pointwise scalar exponentiation.
- Existence and simultaneous uniqueness of both parts are
  `∃! p : (V ≃ₗ[K] V) × (V ≃ₗ[K] V),
  IsMultiplicativeJordanDecomposition A p.1 p.2`.
  Uniqueness is of the ordered pair of maps, not of basis or nilpotence witnesses.
- For linear compatibility, `f : V →ₗ[K] W` is arbitrary and
  `hf : f.comp A.toLinearMap = B.toLinearMap.comp f` is exactly `fA = Bf`.
  `hA` and `hB` specify any decompositions of `A` and `B`; these are the unique parts
  by the existence theorem. The two conclusions are
  `f.comp S.toLinearMap = T.toLinearMap.comp f` and
  `f.comp U.toLinearMap = Z.toLinearMap.comp f`.
  No injectivity, surjectivity, or equivariance beyond the stated intertwiner is assumed.
- The tensor vector space is Mathlib's `TensorProduct K V W`, with its actual bilinear
  universal property. `TensorProduct.congr A B` is the tensor automorphism;
  `TensorProduct.congr_tmul` has precisely the prescribed action on pure tensors.
  `hC` names an arbitrary decomposition `(P,Q)` of that automorphism. The conclusions
  `P = TensorProduct.congr S T` and `Q = TensorProduct.congr U Z` are the two exact
  tensor-part equalities. This formulation avoids a choice of canonical parts: existence
  and uniqueness give the parts, and compatibility holds for every representative.
  The finite dimensionality of the tensor space follows from the finite tensor basis,
  rather than being added as a new independent hypothesis.

Dependencies used:

- `def-weil-field` is status `mathlib`, matched to `Field`, read in
  `Mathlib.Algebra.Field.Defs`, including the full class and its docstring at line 180.
  There is no project module or missing `lean` record for this dependency.
- `IsAlgClosed`, its root characterization, and class documentation were read in
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (public import).
- `Module.Basis` is Mathlib's basis, read in `Mathlib.LinearAlgebra.Basis.Defs:90`;
  `FiniteDimensional` is its finite-module abbreviation from
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs` (public import).
- `TensorProduct.congr`, `toLinearMap_congr`, and `congr_tmul` were read at
  `Mathlib.LinearAlgebra.TensorProduct.Map:248–267` (public import). The tensor basis
  construction was read in `Mathlib.LinearAlgebra.TensorProduct.Basis`.
- The proof dependency `lem-sfb-generalized-eigenspace-direct-sum` is status `mathlib`.
  Its complete record and the matched declarations were read:
  `Module.End.iSup_maxGenEigenspace_eq_top` in
  `Mathlib.LinearAlgebra.Eigenspace.Triangularizable:75–76`,
  `Module.End.independent_maxGenEigenspace` in
  `Mathlib.LinearAlgebra.Eigenspace.Basic:714–716`, and
  `Module.End.maxGenEigenspace_eq_genEigenspace_finrank` in that file at 602–607.
  The triangularizable module is a plain proof import and brings Basic transitively.

Edge cases checked mathematically before writing:

- On the zero space the only automorphism is the identity, a `Fin 0` eigenbasis is empty,
  and exponent one kills zero. The pair uniqueness assertion remains true; no
  `Nontrivial V`, positive dimension, or nonempty basis hypothesis appears.
- If either factor is zero, its tensor product with the other space is zero, and the
  tensor-part equalities assert equality of the unique automorphisms of that space.
- The zero intertwiner and intertwiners to/from zero satisfy both equalities. The theorem
  allows all such linear maps, including noninvertible intertwiners.
- Identity and scalar automorphisms have unipotent part the identity; a nontrivial
  unipotent Jordan block has semisimple part the identity. The predicate permits each.
- Positive characteristic is allowed. The tensor proof uses commuting nilpotent maps
  and a power expansion without division; colliding product eigenvalues cause no issue.
- Field, source space, and target space have independently declared universes. All
  variables and universes are explicit, with `set_option autoImplicit false`.

Searches actually run:

- `msearch.py leanfinder`, query
  `Multiplicative Jordan decomposition of linear automorphisms with intertwiner and tensor product compatibility`:
  eight unrelated hits on star-module splitting and signed-measure Jordan decomposition;
  no exact match. Repeating the query gave the same results.
- `msearch.py loogle`, queries
  `Module.End.IsDiagonalizable, IsNilpotent, LinearEquiv.tensorProduct` and
  `Module.End.IsDiagonalizable, IsNilpotent, TensorProduct.congr`:
  zero hits with the diagnostic `unknown identifier 'Module.End.IsDiagonalizable'`.
  This diagnostic is recorded as such, not as a proof that no diagonalizability API exists.
- `msearch.py grep`, query
  `multiplicative.*Jordan|Jordan.*multiplicative|IsDiagonalizable|IsUnipotent`,
  subdirectory `LinearAlgebra`: zero hits.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Jordan, multiplicative Jordan,
  diagonalizable, and unipotent terms found no equivalent declaration. Node-id search of
  `lean/WeilConjectures` gave no hit. `dag/lean_names_upstream.json` had unrelated
  Jordan–Hölder declarations, not this statement. The proposed full declaration names
  were also searched across Mathlib, both library roots, and that upstream name index:
  no collisions.
- Read `Mathlib.LinearAlgebra.JordanChevalley:44–95`: the existing existence and
  uniqueness theorems concern additive nilpotent-plus-semisimple decomposition, without
  the multiplicative tensor and intertwiner statements, so are not exact matches.
- Direct searches in Mathlib's eigenspace files found semisimplicity and the spanning
  eigenspace characterization, but no `IsDiagonalizable` declaration. The delivered
  helper uses the node's explicit eigenbasis description, built from the existing basis
  type, rather than introducing a second general diagonalizability definition.

Verification: the prescribed `scompile.py Q130` invocation compiled this file in sandbox
and library modes on the server, each in 1.9 seconds, without errors or unexpected warnings.
No proof has been supplied; the only postponed declarations are the three named theorems
owned by this DAG node, with source and complete proof docstrings.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
