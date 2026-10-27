## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusFreeUnipotent` states
`AlgebraicGeometry.exists_unitriangular_embedding_of_torusFree`. Its single theorem
has proof `sorry`; no definitions or other theorems are introduced. The node is
unchanged except for its `lean` record. No dependency repair or new node is needed.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- An arbitrary field is `{k : Type u} [Field k]`, without perfectness, infinitude,
  characteristic, separable-closure, or algebraic-closure assumptions.
- The k-group scheme H is `H : Grp (Over (Spec (.of k)))`. The bundled group's
  `H.X` carries the recorded `CategoryTheory.GrpObj` structure.
- Affineness is `[IsAffine H.X.left]`. Finite type is
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`, as specified by the
  recorded finite-type dependency (Mathlib has no bundled finite-type predicate).
- Smoothness is `[Smooth H.X.hom]`; connectedness of the underlying scheme is
  `[ConnectedSpace H.X.left]`, which includes nonemptiness.
- `htorus` quantifies over every k-group scheme T and group homomorphism `i : T ⟶ H`.
  `IsClosedSubgroupScheme i.hom.hom` says that it is a closed subgroup inclusion;
  `MultiplicativeType.IsTorus T` is exactly the recorded torus predicate, using
  scalar extension to `AlgebraicClosure k` and a finite product of G_m, rank zero
  included. The conclusion `Nonempty (T ≅ Grp.trivial (Over (Spec (.of k)))))`
  says that this subgroup is trivial as a group scheme. An inclusion of a trivial
  group has necessarily the unit image, so this says that the subgroup itself is
  the trivial subgroup, not merely that it has trivial k-points. No assumptions
  on T are added; tori already are smooth affine of finite type, and a closed
  subgroup of this affine finite-type H is affine of finite type.
- The positive integer n in the conclusion is `∃ n : ℕ, 0 < n ∧ ...`.
  `ULift.{u} (Fin n)` supplies exactly n matrix indices in the common universe
  required by the upstream GL construction; it does not alter the matrix size.
- `r : H.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k` together with
  `IsClosedSubgroupScheme r` is a group homomorphism and a closed immersion into
  GL_n. Its matrices are obtained by the recorded natural identification
  `GeneralLinearGroup.homMulEquiv` of algebra points with invertible matrices.
- For every commutative k-algebra R and every R-point x of H, diagonal entries
  are one (`∀ i, ... ⟨i⟩ ⟨i⟩ = 1`) and entries below the diagonal vanish
  (`∀ i j, j < i → ... ⟨i⟩ ⟨j⟩ = 0`). These are exactly the defining closed
  equations of U_n in GL_n. Thus r factors through U_n and the factor is a
  closed immersion: on coordinate rings its surjection kills precisely the
  equations required for factorization. Conversely an embedding in U_n gives
  this r by composition with its closed inclusion into GL_n. This direct
  equation formulation avoids introducing a second notion of unipotence or
  selecting an unspecified ambient group. Testing all algebras, rather than
  geometric points alone, retains the scheme-theoretic conclusion.

Dependency declarations read and used:

- `Field`: `Mathlib.Algebra.Field.Defs`.
- `CategoryTheory.GrpObj` and `CategoryTheory.Grp`:
  `Mathlib.CategoryTheory.Monoidal.Grp`. The project's
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents the precise
  specialization to `Over (Spec (.of k))`.
- `AlgebraicGeometry.LocallyOfFiniteType`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`;
  `AlgebraicGeometry.QuasiCompact`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `AlgebraicGeometry.Smooth`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `ConnectedSpace`: `Mathlib.Topology.Connected.Basic`.
- `AlgebraicGeometry.IsClosedSubgroupScheme` and its `IsSubgroupScheme` parent:
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`;
  `AlgebraicGeometry.IsClosedImmersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `AlgebraicGeometry.MultiplicativeType.IsTorus`, `baseChange`, and `splitTorus`:
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`. Its rank-one factor uses
  `AlgebraicGeometry.StandardGroupSchemes.multiplicative` from
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`, which is its public import.
- `AlgebraicClosure`: `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, used
  inside the recorded torus definition.
- `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`:
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`. These are the
  existing GL constructions explicitly reused by the recorded dependency
  module `Sheaf.AlgebraicGeometry.LinearGroupSchemes`, which is publicly imported.
  Its special-linear constructions are not substituted for GL.

All nine proof dependencies currently have neither a Lean record nor a Mathlib
match, so there are no recorded proof modules to import. Their names and the
full induction/finite-field proof route are preserved in the theorem docstring.
The proof dependencies are not needed to elaborate the statement.

Edge cases checked before writing: the trivial group satisfies the hypothesis
and has its required embedding in U_1; n = 0 is excluded exactly as the node
requires, whereas the rank-zero torus remains allowed. G_m fails the hypothesis
by its own closed subgroup inclusion. G_a satisfies the expected unitriangular
conclusion in size two. Finite fields and imperfect fields are included. The
empty scheme is excluded by the group identity and connectedness, consistently
with the node. Nonreduced test rings, including the zero ring, are included;
coordinate equations apply scheme-theoretically, rather than only to rational
or geometric points. Field, scheme, test-algebra and GL index universes follow
the recorded common-u APIs; there is no independently smaller test universe.

Searches made before writing:

- `msearch.py Q116 <item> leanfinder` with query
  `A smooth connected affine algebraic group over an arbitrary field with no nontrivial torus subgroup is unipotent`:
  OK, eight hits on abstract nilpotent groups and Lie-algebra Cartan/radical
  results; none states this group-scheme theorem.
- `msearch.py Q116 <item> loogle` with query `"IsUnipotent", "Subgroup"`:
  OK, zero hits.
- `msearch.py Q116 <item> grep` with query `unipotent|[Tt]orus` in
  `AlgebraicGeometry`: OK, zero Mathlib hits.
- `rg -n 'IsUnipotent|unitriangular|Unitriangular|IsTorus|IsClosedSubgroupScheme|torus_free|torusFree'`
  in the named project AlgebraicGeometry source directories found the recorded
  torus API and GL/group-scheme API, the geometric unipotence predicate of
  `SolvableGroupStructure`, and the all-algebra coordinate formulation used by
  `CharZeroCommutativeUnipotentVectorGroup`. None states this result.
- `rg -n 'lem-sfb-torus-free-implies-unipotent-arbitrary-field' lean/WeilConjectures`
  returned no hits. `rg -n '17\.81|torus-free|no nontrivial torus|torusFree'`
  in `lean/Sheaf` and `lean/WeilConjectures` found only a mention in
  `GroupScheme/CentralMaximalTorusNilpotent.lean`, not the arbitrary-field theorem.

Source checked directly with `pdftotext -layout` on the recorded local Milne
PDF: Proposition 17.81 and its proof on printed pp.378--379, including its
separate finite-field argument via 17.99, and Theorem 14.5 on pp.281--282,
whose clause (b) is the closed unitriangular-embedding conclusion used here.
There is no statement dispute or source-based correction.

## Second reading by Q116

I reread the node and the final signature after writing, in this dispatcher-run
single-worker session. This is a self-check, not an independent second agent;
the brief reserves the independent delivery review to the maintainer.

I checked each binder against the node: arbitrary field; group scheme; affine;
finite type; smooth; connected; every closed base-field torus subgroup trivial.
I checked each conclusion: a positive finite size, a closed group embedding,
and all diagonal/below-diagonal equations on every test algebra. The trivial
subgroup condition uses a group-scheme isomorphism, not a subsingleton set of
k-points. The upper-triangular condition has `j < i` (row i, column j), not its
reverse. The GL point equivalence is applied to `x ≫ r`, not to x alone.
The repeated finite-type/smooth consequences are standard assumptions from
the node, and no perfectness or infinitude hypothesis slipped in. No mismatch
or change to the mathematical node was found. The theorem docstring includes
all five supplied proof steps, including the connected centralizer and the
finite-field representation comparison. All implicit variables are explicitly
bound, with `set_option autoImplicit false` in the module.

Validation: prescribed `scompile.py` compiled the sandbox and final library module
cleanly (2.7 s and 3.0 s). The prescribed `deliver2.py --no-push` reported
`OK (dry run)`: commit `9127045840d` passed preflight and compilation, nothing pushed.
