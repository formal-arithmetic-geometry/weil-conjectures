## Worker report

The module Sheaf.AlgebraicGeometry.TorusNormalizedSimpleSubmodule states
AlgebraicGeometry.exists_torus_stable_simple_submodule, with exactly one postponed
proof. No definitions or supplementary theorems are introduced. The statement is
unchanged; stmt_deps gains the landed definition owners
def-sfb-tori-multiplicative-type, def-wf-algebraic-representations and
def-sc-general-linear-group. The returned theorem-node dependency is removed.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- A k-group scheme T: `(T : Scheme.{u}) [T.Over (Spec (.of k))]` and
  `[GrpObj (T.asOver (Spec (.of k)))]`. The over structure is its specified map
  to Spec k, and GrpObj supplies the actual multiplication, inverse and identity.
- T is isomorphic as a group scheme to G_m^r, including r=0:
  `(r : ℕ)` and `hT : Nonempty (Grp.mk (T.asOver (Spec (.of k))) ≅
  MultiplicativeType.splitTorus k r)`. The iso is in bundled group objects,
  so respects the group law. splitTorus is the existing finite product of the
  Laurent-polynomial multiplicative group, with the terminal group at rank zero.
- Nonzero finite-dimensional vector space M: `(M : Type u) [AddCommGroup M]
  [Module k M] [FiniteDimensional k M] [Nontrivial M]`.
- Rational representation tau: `τ : GeneralLinearGroup.RationalHom
  (T.asOver (Spec (.of k))) (ULift.{u} (Fin (Module.finrank k M)))`
  and `[IsMonHom τ]`. RationalHom is an actual morphism of schemes over Spec k
  to the general linear group, and IsMonHom makes it a group-scheme homomorphism.
  The basis `(Module.finBasis k M).reindex Equiv.ulift.symm` identifies GL(M)
  with that matrix group. This is a specified basis construction, not an added
  basis hypothesis, dimension restriction or replacement of M by another space.
  `τ.points R t` is its invertible matrix over each commutative k-algebra R;
  `Matrix.GeneralLinearGroup.toLin'` applied to the scalar-extended basis,
  followed by `.toLinearEquiv`, is exactly its action on `R ⊗[k] M`.
  These points come from a scheme morphism; no natural-family or point-only
  action is assumed in place of that morphism.
- Unital k-subalgebra B inside End_k(M): `B : Subalgebra k (Module.End k M)`.
- Normalization over every R and t: `hnormalizes` quantifies over `(R : Type u)
  [CommRing R] [Algebra k R]` and `t : points (T.asOver (Spec (.of k))) R`.
  `Submodule.span R (Set.range (fun b : B ↦
  (b : Module.End k M).baseChange R))` is B_R as an operator subspace.
  `Submodule.map` of the displayed linear equivalence's `.conj.toLinearMap`
  sends b to tau*b*tau^{-1}.
  Equality with the original span is exactly the stated equality, not a one-sided
  normalization assumption. Finite sums of scalar multiples of b baseChange are
  precisely the image of R tensor B; this embeds into End_R(R tensor M) because
  M is finite-dimensional and every k-algebra is flat as a k-module.
- Nonzero k-linear subspace U of M: `∃ U : Submodule k M, U ≠ ⊥ ∧ ...`.
- BU is contained in U: `∀ (b : B) (m : M), m ∈ U →
  (b : Module.End k M) m ∈ U`.
- Only B-stable k-subspaces of U are zero and U: the next conjunct quantifies
  over every ambient `W : Submodule k M` with `W ≤ U`, assumes precisely
  the same B-invariance condition for W, and concludes `W = ⊥ ∨ W = U`.
  Ambient W≤U is equivalent to a k-linear subspace of U itself.
- Full scheme-theoretic torus stability: the last conjunct quantifies over all
  the same coefficient algebras and points and asserts
  the equality of `U.baseChange R` with its image under the displayed
  linear equivalence's `.toLinearMap`.
  `Submodule.baseChange` is the range of the base-changed inclusion, namely
  R tensor U as a subspace of R tensor M; flatness over k makes this faithful.
- No semisimplicity assumption occurs anywhere in the signature.

The node uses M tensor R, whereas the existing Mathlib and rational representation
interfaces use R tensor M. The canonical tensor symmetry identifies these spaces,
their induced operators, and every subspace after scalar extension. This is a
change of tensor order only. The single explicitly declared universe u is shared
by fields, schemes, vector spaces, the lifted finite matrix index and test algebras. No independent smaller test universe makes
normalization vacuous. This is universe-polymorphic with no equality constraints.

Dependency declarations read and reused:

- Mathlib.Algebra.Field.Defs: Field (def-weil-field).
- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed; the recorded
  AlgebraicClosure/IsAlgClosure interfaces distinguish algebraically closed fields
  from a chosen algebraic closure. Only the former is needed here.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj and Grp;
  Mathlib's IsMonHom is built into the bundled iso. Read also the recorded
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs conventions.
- Mathlib.LinearAlgebra.FiniteDimensional.Defs: FiniteDimensional = Module.Finite.
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType:
  AlgebraicGeometry.MultiplicativeType.splitTorus (newly cited landed owner).
- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation:
  the recorded algebraic-group module interface (def-wf-algebraic-representations),
  publicly importing GeneralLinear.Lie, where RationalHom and RationalHom.points
  are defined. The statement uses only these genuine group-scheme constructions;
  it does not use the separate characteristic-zero simplicity interface.
- Sheaf.AlgebraicGeometry.LinearGroupSchemes: the module recorded for
  def-sc-general-linear-group, importing the upstream general linear group.
  The upstream GeneralLinearGroup and homMulEquiv identify its points with GL.
- Mathlib.LinearAlgebra.Dimension.Free: Module.finBasis; its reindex and
  baseChange give the chosen scalar-extended basis.
- Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs:
  Matrix.GeneralLinearGroup.toLin', the matrix-to-automorphism equivalence.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring:
  AlgebraicGeometry.points, actual over-Spec morphisms from Spec R.
- Mathlib.LinearAlgebra.TensorProduct.Tower: LinearMap.baseChange,
  Module.End.baseChangeHom and Submodule.baseChange.
- Mathlib.Algebra.Module.Equiv.Basic: LinearEquiv.conj, whose formula is
  e composed with b composed with e.symm.

Proof-only imports follow the recorded proof plan:
Sheaf.AlgebraicGeometry.FreeQuotientGrassmannProjective
(exists_freeQuotientGrassmann_projective),
WeilConjectures.AlgebraicGeometry.AffineFreeMapZeroLocus
(Scheme.exists_affineFreeMapZeroLocus),
WeilConjectures.AlgebraicGeometry.LocalClosedLocusGluing
(Scheme.exists_closedLocus_of_local_charts),
WeilConjectures.AlgebraicGeometry.ProjectiveSpace
(ProjectiveSpace.instIsProper), Mathlib.AlgebraicGeometry.Morphisms.Proper
(IsProper and permanence instances),
Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
(MultiplicativeType.multiplicativeType_largestSubtorus), and
Sheaf.AlgebraicGeometry.StandardGroupSchemes (multiplicative).
lem-sfb-solvable-proper-fixed-point has no Lean record or mathlib_match at reading
and hence has no module to import yet; no replacement theorem is invented. This
proof-only missing statement does not prevent stating this item. Its use remains
explicit in the seven-step proof docstring.

Source and edge cases:
Read Milne printed p.146 (PDF p.158), Propositions 7.29--7.30, including rank-d
subbundles and projectivity; and printed p.353 (PDF p.365), Corollary 17.3,
including scheme-theoretic fixed locus and no reduction assumption on X. The
node accurately labels this as an auxiliary argument rather than a verbatim
Milne theorem. Current blueprint sec-six-functors-basics searches for Grassmannian,
Borel fixed point and the node identify no separate statement replacing this item.
Rank zero is allowed by r:ℕ and the existing empty product. Dimension one and the
case d=dim(M) are allowed; U=top is not excluded. M=0 is correctly excluded by
Nontrivial. B=k and B=End(M) are both allowed. Nonsemisimple examples such as an
upper-triangular operator algebra are not excluded. All characteristics, including
positive characteristic, and nonreduced coefficient algebras are included; R is
not required to be a field, reduced or nontrivial, so the zero algebra is included.
At the zero algebra all scalar extensions vanish and both equality clauses remain
meaningful. No assertion that U has dimension one is added.

Searches actually run:

- msearch leanfinder: "A split torus normalizing a unital endomorphism subalgebra
  has a torus invariant simple submodule of a finite dimensional rational
  representation". Eight hits, including FDRep.simple_iff_end_is_rank_one,
  FDRep.simple_iff_char_is_norm_one, root-system irreducibility, and IsIsotypic
  decomposition results. These either concern different objects or impose
  semisimplicity; no exact theorem.
- msearch loogle: "Representation.invtSubmodule, IsSimpleModule". Zero hits.
- msearch grep: "torus.*simple|Borel.*fixed|RationalRepresentation". Zero
  Mathlib hits.
- msearch leansearch: "A torus normalizing a unital algebra of endomorphisms
  stabilizes a simple submodule of a finite dimensional rational representation".
  Eight hits: Lie normalizers, Maschke semisimplicity, representation invariant
  submodules, Tannaka and the dimension of a simple commutative-algebra module.
  No torus-normalized operator-algebra existence theorem.
- rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  the item id, RationalRepresentation, rationalRepresentation, torus.*simple,
  normalized.*submodule and exists_torus_stable_simple_submodule. No existing
  theorem; found and reused the rational dictionary and splitTorus interfaces.
  The upstream RationalHom.IsSimple interface assumes characteristic zero and
  concerns simplicity under a group action; it is not the B-module statement.
- DAG search for rational representation and split torus found the two added
  dependency interfaces; their full statements, records and source declarations
  were read. Repair review found the natural-family structure lacked a definition
  node owner, so the final statement instead uses the existing RationalHom interface. No new notion or duplicate definition is needed.

## Repair of returned delivery 8cc78e346ca9

H2 is repaired by the second option expressly requested in the return. Removed
NaturalRepresentation, its module import and the theorem stmt_dep
lem-sfb-rational-representation-comodule-dictionary. Added the two existing
definition stmt_deps def-wf-algebraic-representations and def-sc-general-linear-group,
and their public module imports. Tau is now RationalHom with IsMonHom, and its
action in both clauses is obtained directly from its R-points and the finite basis.
No new definition, theorem, node, mathematical assumption or statement correction
is needed. The current main node has no lean record and retains the same statement
and proof; only lean and the authorized added statement dependencies differ.
The seven-step proof docstring remains unchanged.

Validation: the prescribed scompile.py compiled the repaired module in sandbox
and library modes with exit code zero and no diagnostics. The separate dry run
checks preflight and per-file compilation again. Module mode,
public statement imports, private proof imports and disabled autoImplicit remain.

## Second reading by N9

Reread the returned H2, the current main node, the modified module and the owning
definition records. The field and algebraic closure, specified k-group scheme,
split group iso including rank zero, nonzero finite-dimensional M, unital B,
all-algebra conjugation equality, nonzero invariant U, simplicity among subspaces
inside U, and all-algebra stability equality match clause by clause as detailed
above. The changed tau binder is a morphism to the genuine general linear group
with precisely the group-law compatibility; the basis transport converts its
points to automorphisms of the original scalar extension, rather than changing M.
The former theorem node is absent from stmt_deps and imports. The definition
owners are cited instead, as the return requests. No T(k)-only condition,
semisimplicity, characteristic-zero condition or dimension-one conclusion occurs.
Tensor symmetry and the faithful operator span retain their previous meaning.
The edge cases above remain included. Independent review remains the maintainer's.
