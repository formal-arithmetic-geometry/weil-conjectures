## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusActionLieRigidity` states
`AlgebraicGeometry.torus_action_connected_group_iff_tangent_trivial`, with `sorry`.
There are no new definitions or auxiliary theorems. The original mathematical
statement and proof are unchanged. Two already landed definition nodes are added
to `stmt_deps`: `def-sfb-tori-multiplicative-type` and `def-sc-dual-numbers`.
They record the existing notions expressly used by the original statement.

Source checked: Conrad, *Reductive Group Schemes*, Proposition 3.3.8 proof,
printed p.102, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
PDF page index 101, paragraph citing CGP Corollary A.8.11. This explicitly
applies tangent detection to a connected finite-type group, including the
possibly nonreduced identity component of the adjoint kernel.

Clause-by-clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The group scheme over k is `H : Over (Spec (.of k))` with `[GrpObj H]`.
  These are precisely the recorded group-scheme declaration and specialization.
- Affineness is `[IsAffine H.left]`. Connectedness is `[ConnectedSpace H.left]`,
  which includes nonemptiness. Finite type is `[LocallyOfFiniteType H.hom]`
  together with `[QuasiCompact H.hom]`, as in its dependency record.
- The split torus is `T : Grp (Over (Spec (.of k)))`, `r : ℕ` and
  `hT : Nonempty (T ≅ MultiplicativeType.splitTorus k r)`. The isomorphism is
  an isomorphism of group schemes, and rank zero is allowed. The existing
  splitTorus is the finite product of the existing Laurent Hopf G_m, with
  units as algebra-valued points. It is not an arbitrary abstract group.
- The action is `[ModObj T.X H]`. Its structure map `γ[T.X, H]` is a morphism
  over Spec k, and its `one_smul` and `mul_smul` fields are exactly the two
  action laws. On algebra-valued points it induces the existing Hom action.
- `hgroup` is the multiplication compatibility on every commutative k-algebra
  `B : CommAlgCat.{u} k`. The two action laws make the action of t invertible,
  with inverse the action of t inverse. A bijective multiplication-preserving
  map of groups preserves the identity and inverses. Thus this condition is
  exactly action by group-scheme automorphisms, without any smoothness premise.
- The left side `γ[T.X, H] = snd T.X H` is equality with the projection as
  morphisms of k-schemes, as required, not merely equality at rational points.
- The entire tangent condition on the right quantifies over every B, every
  `t : Spec B ⟶ T`, and every `θ : Spec (DualNumber B) ⟶ H`, in the slice over k.
  The equation `Spec(fstHom) ≫ θ = 1` says that theta reduces to the identity
  under epsilon -> 0. The morphism `Spec(inlAlgHom)` lifts t from B to
  B[epsilon]. The remaining equation says its action fixes theta.
  This is the defining differential of a(t,-) at the identity over B: it
  postcomposes the dual-number point by that automorphism. Hence equality on
  all such theta says its induced B-linear map is the identity. Over a field,
  this tangent functor is the scalar extension of the tangent vector space:
  it is Hom_k(m/m^2,B), and m/m^2 is finite-dimensional. This identification
  needs finite type, already assumed, and does not need smoothness or reducedness.
  The formula never replaces this action by the differential of T itself.
- There is no reduced, smooth, reductive, or characteristic-zero hypothesis.
  The equivalence includes both directions, in the original order.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`, as specified by the
  algebraic-closure dependency's match. No algebraic extension datum is needed
  when k itself is assumed algebraically closed.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj` and `Grp`;
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents their group-scheme
  specialization and supplies the subgroup terminology of the proof.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`.
- WeilConjectures.AlgebraicGeometry.SchemeTangentSpace: `schemeTangentSpace`
  and `schemeTangentMap`, whose full definitions and docstrings were read.
  Those definitions use a residue-field dual-number point and postcomposition.
  The statement expands exactly that tangent-map formula for the rational
  identity over every algebra B, since B need not be a field. It does not
  create a competing tangent-space definition or select an arbitrary map.
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType:
  `MultiplicativeType.splitTorus`; its underlying
  `StandardGroupSchemes.multiplicative` and Laurent Hopf group law were read.
- Mathlib.Algebra.DualNumber: `DualNumber`; Mathlib.Algebra.TrivSqZeroExt.Basic:
  `TrivSqZeroExt.fstHom` and `TrivSqZeroExt.inlAlgHom`.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Mod: `ModObj`, the Hom action,
  `Hom.mulAction`, and its naturality `ModObj.comp_smul`.

The modules of the already stated proof dependencies are imported: local jets,
rational tangent/cotangent duality, weight bases, subgroup schemes, tangent
spaces, and Krull intersection (`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`).
The fixed subscheme, rational thickenings, and identity-stalk criterion have no
Lean records in the read clone and are not imported. Their full proof roles
remain in the theorem docstring; they are not statement prerequisites.

Edge cases checked before writing:

- r=0: the existing splitTorus is the tensor unit and its action law forces
  triviality. No positive-rank assumption is present.
- H the trivial group: both conditions hold, including zero tangent space.
- H nonreduced, e.g. alpha_p: all dual-number points are still quantified;
  there is no replacement of H by its reduced subscheme.
- Positive characteristic: a weight divisible by p can have zero infinitesimal
  differential while its torus representation is nontrivial. The formula tests
  all t, rather than tangent vectors of T, so does not erase that weight.
- B can have nilpotents or be the zero algebra. Both remain in the universal
  quantifier, and the condition is meaningful in both cases.
- An empty H is already excluded by the group identity and ConnectedSpace,
  consistently with the node. Nonconnected groups are outside its hypotheses.
- The index B lives in the same arbitrary universe as k and its schemes, with
  no independent smaller universe and no nonempty or nontrivial-algebra premise.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "A split torus action on a connected affine group scheme is trivial if and only if its tangent representation is trivial"`:
  eight hits including Rep.instIsTrivialOfOfIsTrivial, Galois-category group
  results, formally smooth/etale vanishing, and an Engelian statement. None
  states this group-scheme theorem.
- `msearch.py ... loogle "GrpObj, Action, DualNumber"`: no hits;
  service reported unknown identifier GrpObj.
- `msearch.py ... leansearch "A torus acting by group scheme automorphisms on a connected affine algebraic group is trivial if its induced representation on the tangent space is trivial"`:
  eight hits about Rep.IsTrivial, Representation.IsTrivial and Action.rhoAut;
  none is the scheme-theoretic assertion.
- `msearch.py ... grep "torus.*(tangent|[Ll]ie)|rigidity" AlgebraicGeometry/Group`:
  zero hits.
- `rg -n 'torus.*(tangent|Lie)|torus_action_connected_group|lie_rigidity'`
  in both lean/Sheaf and lean/WeilConjectures found character-weight and
  reductive-group tangent uses, without this theorem. A separate recursive
  item-id search in lean/WeilConjectures returned no match.
- Concept searches for splitTorus, ModObj, dual numbers and Lie tangent points
  found the reused existing declarations listed above. No notion was duplicated.

No STATEMENT-DISPUTED flag and no statement correction are needed.

## Second reading by Q74

The dispatcher forbids starting other agents. This section records a second
self-reading of the node and module, not an independent-agent review; the
maintainer's independent review follows delivery.

The algebraically closed base, connected affine finite-type group and arbitrary
rank split torus match their binders. The action structure supplies precisely
unit and associativity; hgroup supplies multiplication preservation on all
algebra-valued points. Its inverse follows from the action law, so no extra
identity-preservation hypothesis is needed. The left conclusion is morphism
equality, and the right conclusion uses all algebras and dual-number vectors.
The directions of Spec(fstHom) and Spec(inlAlgHom) were checked against their
actual signatures: the former inserts the closed section and the latter lifts
t to the infinitesimal thickening. No field structure is assumed on B. The
right formula is the identity of the full tangent action, including nonreduced
B, not a condition on Lie(T). There are no silently changed hypotheses or
clauses, no data chosen using sorry, and just the one postponed theorem. The
added dependencies name existing notions, with no new module or node repairs.
