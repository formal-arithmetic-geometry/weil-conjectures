## Worker report

The module `Sheaf.AlgebraicGeometry.CentralSemisimpleRestrictedSubalgebra` states
`AlgebraicGeometry.central_semisimple_restricted_subalgebra`. Its only theorem has
`by sorry`; there are no new definitions, additional axioms, or new DAG nodes.
The item node changes in `lean` and adds the landed owner node
`def-wf-lie-algebra-derivation` to `stmt_deps`, as required by the H2 return. The source was read directly: Milne,
Algebraic Groups (2017), printed pp.377–378, Proposition 17.80's first reduction
and Corollary 17.77. The scalar-extension conclusion is the explicit clause of
the DAG node, and the proof docstring carries all five supplied proof steps.

Hypothesis and clause correspondence:

- Field: `(k : Type u) [Field k]`. The fixed algebraic closure is the existing
  `AlgebraicClosure k`, in the same universe, with its canonical algebra structure.
- Group scheme: `J : Grp (Over (Spec (.of k)))`. Its underlying group object is `J.X`.
  Affineness is `haff : IsAffine J.X.left`. Finite type is exactly the conjunction
  of `hft : LocallyOfFiniteType J.X.hom` and `hqc : QuasiCompact J.X.hom`.
- Smoothness and connectedness: `hsm : Smooth J.X.hom` and
  `hconn : ConnectedSpace J.X.left`, respectively. ConnectedSpace includes nonemptiness.
- Fixed faithful closed linear representation: `r : GeneralLinearGroup.RationalHom J.X n`,
  `[IsMonHom r]`, `[IsClosedImmersion r.left]`, for an arbitrary finite index type `n`.
  A finite type with a Fintype and DecidableEq is precisely a choice of finite matrix
  coordinates; it is not a restriction on the representation's dimension or the field.
- Tangent Lie algebra: the existing `GrpObj.Lie J.X`, whose commutator bracket is the
  upstream `GroupScheme.Lie.Bracket` construction. The existing `r.differential` is
  its Lie homomorphism into matrices, obtained from `GrpObj.differential` and the
  canonical `Lie(GL_n)` matrix equivalence. No bracket or differential is supplied
  arbitrarily as a hypothesis. The imported scheme tangent-space declaration is
  the dependency's recorded one; the canonical group tangent interface represents
  tangent vectors at the identity by the same dual-number points.
- Nonnilpotence: `hnil` negates existence of a finite chain `C` indexed by
  `Fin (m + 1)`, embedded by `i` as closed normal subgroup schemes. `IsIso (i 0)`
  says its first term is J, and the final term is isomorphic to `Grp.trivial _`.
  The factorization clause makes the chain descending. The final clause says
  `[J(A), C_j(A)]` factors through `C_(j+1)(A)` for every commutative k-algebra A.
  These are scheme-theoretic containments: for affine schemes the algebra-valued
  point criterion includes the universal points, not merely rational field points.
  Intermediate subgroups inherit affineness and finite type from closedness in J;
  no smoothness or connectedness of these intermediate terms is required.
- Geometric centrality: `hcentral` quantifies over the algebraic-closure span of
  the entrywise extensions of `r.differential`'s image. This is the faithful matrix
  realization of `bar k tensor_k Lie(J)`. Diagonalizability is existence of an
  invertible matrix P with `P⁻¹ X P` satisfying Mathlib's `Matrix.IsDiag`.
  The consequent `Commute X Y` for every Y in the same tangent space says that
  the commutator bracket is zero. It is exactly geometric centrality.
- Positive characteristic: `∃ p : ℕ, p.Prime ∧ CharP k p`. Prime implies p > 0;
  over a field this is equivalent to the stated positive-characteristic conclusion.
- The semisimple set is a restricted Lie subalgebra: the existential
  `S : LieSubalgebra k (GrpObj.Lie J.X)` gives the linear subspace and bracket
  closure; its first conjunct is an iff identifying its carrier with exactly all
  tangent vectors whose matrices diagonalize over the algebraic closure.
  The second conjunct says `∀ x ∈ S, ∃ y ∈ S, dr(y) = dr(x)^p`.
  Restricted rational differentiation identifies matrix p-th power with the
  p-fold invariant-derivation operation specified by the node. Since r is a
  closed immersion its differential is injective, so this y is uniquely the
  canonical x^[p]. Thus this does not choose a different restricted operation,
  omit p-closure, or impose an additional premise on it.
- Adjoint triviality: for every A and g in J(A), the third conjunct states
  `Commute (r.points A g : Matrix n n A) X` for EVERY X in the A-span of
  the entrywise images of S. This span is the image of A tensor_k S.
  Conjugation by an invertible matrix fixes X exactly when it commutes with X.
  The faithful closed representation identifies this with the adjoint action.
  Quantification over A is at the field/scheme universe u, not a potentially
  smaller independent universe, so it includes the coordinate algebras and universal
  points that detect equality of the group-scheme representation.
- Scalar extension: the last conjunct is an iff, for every X of the geometric
  tangent space, between diagonalizability and membership in the geometric span
  of S. This states exact equality of the embedded `bar k tensor_k S` and the set
  of all geometric semisimple tangent vectors, in both directions. The span is
  the actual tensor image, not an arbitrary proposed comparison map.
- Tori and multiplicative type are only standing terminology in the node; no torus
  or multiplicative-type assumption is added. Their recorded module is imported.

Dependency declarations read and used:

The landed definition node `def-wf-lie-algebra-derivation` owns the canonical
`GrpObj.Lie` module, bracket and LieAlgebra instances, together with
`GeneralLinearGroup.RationalHom` and `RationalHom.differential`. Its Q08
`existing: true` record points at
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket`; its unchanged
`lean_audit.slopmaster2` and `dag/lean_names_upstream.json` also record the matrix
representation declarations in
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`.
Both are already publicly available through the delivered imports. This owner
node is now explicitly included in the item's `stmt_deps`. The abstract Lie
algebra definition and the separate `schemeTangentSpace` record do not replace
that ownership. The owner's general upstream declarations apply over the
arbitrary field k used here; no characteristic-zero premise is added.

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure` gives its meaning.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, and group homomorphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme`, and their parent `IsSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: the recorded `MultiplicativeType`
  declarations, including `IsTorus` (only standing terminology).
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace`,
  its canonical additive/module instances and `schemeTangentMap`. For identity tangent
  Lie coordinates use the already existing group-scheme tangent theory, not a copy.
- `Mathlib.Algebra.Lie.Basic`, `Mathlib.Algebra.Lie.Subalgebra`: `LieRing`,
  `LieAlgebra`, and `LieSubalgebra`.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`: the recorded general/special-linear
  interface, which explicitly reuses `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`
  for `GeneralLinearGroup`. Its `.Lie` module supplies `RationalHom`,
  `RationalHom.differential`, `RationalHom.points`, and `lieAlgebraEquivMatrix`.
- `Mathlib.LinearAlgebra.Matrix.IsDiag`: `Matrix.IsDiag` is the existing condition
  that off-diagonal entries vanish. The existential change of basis is written inline.

Proof imports: the two currently stated proof inputs are imported:
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`
(`GeometricallyConnected.of_connectedSpace_of_section`) and the smooth morphism
module (open immersion/composition instances). The other eight proof-dependency
nodes have no Lean record or Mathlib match at this reading; their precise proof
roles are retained in the docstring. None is needed as an unstated definition
or supplied as a replacement assumption in the signature.

Edge cases checked before writing: zero semisimple subspace has the zero Lie
subalgebra, the p-closure witness zero, the zero scalar span, and automatic
fixedness of that span. Characteristic zero is excluded only by the theorem's
hypotheses and concluded prime-characteristic result, not by an added binder.
Finite fields and imperfect fields are allowed. The scalar extensions use spans,
not set-theoretic images of semilinear powers. The chain permits length zero,
which describes the trivial group; this makes the nonnilpotence hypothesis false
for the trivial group. A dimension-zero faithful representation can represent
only the trivial group, also excluded by hnil; allowing an empty finite index
therefore adds no prohibited nonnilpotent case. Nonreduced algebras and p=2 are
included; no division by p, cardinality hypothesis, or perfectness is imposed.
There is no STATEMENT-DISPUTED issue and no node correction.

Searches (2026-10-24):

- msearch.py leanfinder: "Semisimple tangent elements of a smooth connected algebraic
  group that are central form a restricted Lie subalgebra commuting with base change".
  Eight hits on Engel/Cartan subalgebras and abstract Lie central radicals; no match.
- msearch.py loogle: `"RestrictedLieAlgebra"`. Zero hits.
- msearch.py leansearch: "central semisimple tangent subspace of algebraic group
  in positive characteristic". Eight hits, including central simple algebras,
  manifold GroupLieAlgebra and Cartan subalgebras; no match.
- msearch.py grep: `central.*semisimple|semisimple.*central|restricted.*Lie`,
  subdirectory `Algebra/Lie`. One unrelated hit in Lie/Submodule.lean.
- rg of the upstream WeilConjectures and Sheaf trees for semisimple tangent,
  restricted power, adjoint and nilpotent scheme notions: no existing theorem.
  This did find the canonical GroupScheme/Lie and GeneralLinear/Lie interfaces,
  the existing restricted-enveloping abstract-operation predicate (unneeded here),
  and CentralMaximalTorusNilpotent's explicit central-series convention, all read.
- Exact blueprint-id search in upstream and Sheaf: no existing declaration for the item.
- Mathlib matrix search found Matrix.IsDiag; no new diagonalizability predicate was
  introduced. The relevant tensor images, semisimple predicates and nilpotence
  conditions can all be written inline from existing notions.

Validation: scompile.py compiled both the sandbox module and its actual library-path
module cleanly, with no errors or warnings, on 2026-10-24. The expected stage-2
sorry is the only postponed theorem.

## Second reading by Q144

The dispatcher explicitly prohibits starting a second agent; this is a separate
in-thread rereading, with independent maintainer review supplied after delivery.
I reopened the node and the final signature and checked the hypothesis/conclusion
mapping above. In particular I checked that hcentral ranges over the full geometric
span, that the final iff has both directions, that p-closure witnesses stay in S,
and that fixedness is for every algebra and every vector of the extended subspace.
The normal and closed subgroup requirements and descending-chain factorizations
are present, with the entire group first and the trivial group last. No smoothness
of intermediate subgroups is assumed. The canonical restricted power is represented
by its injective matrix image, not an arbitrary map. No mathematical mismatch was
found. Compilation initially exposed missing scoped MonObj operations and ambiguous
unit coercions; these were repaired, and three overlong lines were wrapped. The
final compiler run is clean. No mathematical statement correction was needed.
The returned H2 ownership omission is repaired below.

## Returned delivery repair

Return H2, immutable head `a1e75d14fba0`: added the existing landed definition
node `def-wf-lie-algebra-derivation` to `stmt_deps` and identified it above as the
owner of the tangent Lie and rational differential declarations. I reread its
Q08 record, audit and upstream declaration docstrings/signatures, and checked
its statement/proof dependency closure: it does not reach this item, so the
added dependency introduces no cycle. The node otherwise agrees with current
main outside `lean`; its mathematical statement, proof and proof dependencies
are unchanged. The prescribed delivery wrapper rebases the repaired packet
on the current live branch.

The Lean file remains byte-identical to the retained returned version: SHA256
`3127d408a92efaf28a153b169da5e7858a976ac003ce3a02deaf827ac3f81344`.
Its imports, declarations, theorem signature and proof docstring are unchanged;
`lean.statement` still equals its signature verbatim. This repair changes only
the item's dependency metadata and this report, beyond the original delivery.
The maintainer already checked the mathematics and all edge cases as faithful;
the added ownership citation is the only requested repair.
