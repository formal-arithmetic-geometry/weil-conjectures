## Worker report

The module Sheaf.RepresentationTheory.SemisimpleGroupCasimirTrace states
AlgebraicGeometry.semisimpleGroup_casimir_trace, with one sorry and no new definitions.
The node statement and proof are unchanged. Its stmt_deps gains three already-landed
owning definition nodes, avoiding private copies of semisimplicity, stable rational
subspaces, and the coaction laws. There is no statement correction or disputed statement.

Source read: Milne, Algebraic Groups (2017), PDF pp.487--489 (printed pp.475--477),
Section 22c and Proposition 22.41; PDF p.208 (printed p.196), Proposition 10.31.
The source defines the faithful Casimir by the trace-dual sum and treats nonfaithful
representations through the faithful complementary ideal. The node's differential-image
formulation gives exactly that operator through the induced faithful representation.

Hypothesis and clause correspondence:

- Algebraically closed field of characteristic zero: F : Type u with Field F,
  IsAlgClosed F and CharZero F.
- Affine finite-type smooth connected group scheme: G : Scheme.{u}, its Over and
  GrpObj instances, IsAffine G and hG : IsSemisimpleGroupScheme. The latter is exactly
  smoothness, connectedness, affineness, locally finite type plus quasi-compactness,
  and triviality of every smooth connected solvable normal closed subgroup. The
  explicit IsAffine instance exposes an already implied property for type inference.
  Its solvability definition iterates the scheme-theoretic derived subgroup to a
  terminal group over Spec F; it is not solvability only on rational points.
- Rational finite-dimensional module: V : Type v with AddCommGroup, Module F and
  FiniteDimensional F, the linear coaction α into V tensor Γ(G,top), and the existing
  HopfAction.Coassociative and HopfAction.Counital hypotheses. Simplicity is introductory
  terminology in the node, not a hypothesis or conclusion of this lemma.
- Tangent Lie algebra: GrpObj.Lie (G.asOver (Spec (.of F))), using its upstream canonical
  identification lieEquivTangent with dual-number tangent points at the identity.
  This is the identity-point specialization of the recorded tangent-space notion.
- Actual differential: existential dr is linear. For every x an algebra map g is
  required to equal the coordinate ring map of the actual lieEquivTangent point,
  via appTop and Scheme.ΓSpecIso. The equality on α(v) is precisely
  r(1+epsilon x)v = v tensor 1 + dr(x)v tensor epsilon. Thus neither g nor dr is
  an arbitrary chosen map. All vectors determine dr uniquely.
- Differential image and dimension: LinearMap.range dr and Module.finrank F of that
  range. This is the actual subspace of Module.End F V, not an abstract Lie algebra.
- Trace form: LinearMap.trace F V (X.val * Y.val). Nondegeneracy is the stated
  implication (forall Y, trace(XY)=0) -> X=0. Symmetry follows directly from trace(XY)
  = trace(YX), so this is the node's nondegenerate trace form.
- Actual Casimir and independence: one existential c : Module.End F V works for every
  basis b indexed by Fin (finrank F (range dr)). The first clause supplies a basis d
  with trace(b_i d_j)=delta_ij. The next quantifies every such pair b,d and asserts
  c = sum_i (b i).val * (d i).val. In particular it is the actual operator and is
  independent of both basis and its trace-dual presentation. All bases of size n
  occur; arbitrary finite index sets can be reindexed by Fin n.
- Rational G-equivariance: α composed with c equals c.rTensor Γ(G,top) composed with α.
  This is the coaction square, hence equivariance over every algebra extension.
- Trace: LinearMap.trace F V c equals the natural-number cast of finrank F (range dr)
  into F, exactly n times 1_F.
- Nontrivial action: α differs from (TensorProduct.mk F V Γ(G,top)).flip 1, the linear
  map v -> v tensor 1. The implication gives 0 < finrank F (range dr).
- Every rational submodule: for every Submodule F V named W, the existing
  RationalHighestWeight.IsStable α W means α(W) is in the tensor inclusion range.
  The conclusion forall w in W, c w in W is c(W) contained in W.
- Trivial quotient: forall v, (W.mkQ tensor 1)(α v) = (W.mkQ v) tensor 1.
  This states the induced quotient coaction is trivial without introducing an
  arbitrary quotient action. The conclusion forall v, c v in W is c(V) contained in W.
- Empty basis: range dr = bottom implies c=0 explicitly. The displayed finite sum
  is also empty when the dimension is zero.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed
  (the algebraic-closure node explicitly records IsAlgClosed for this clause).
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, specialized to the over
  category of Spec F; upstream GroupScheme.Defs supplies the scheme specialization.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Morphisms.QuasiCompact: QuasiCompact; Morphisms.Smooth: Smooth;
  Mathlib.Topology.Connected.Basic: ConnectedSpace. These occur inside the imported
  semisimple predicate; their full class fields and docstrings were read.
- WeilConjectures.AlgebraicGeometry.SchemeTangentSpace: schemeTangentSpace,
  schemeTangentSpaceAddCommGroup, schemeTangentSpaceModule and schemeTangentMap.
  The module's canonical identity-point implementation is GrpObj.Lie and
  GrpObj.lieEquivTangent from WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.
- Mathlib.Algebra.DualNumber: DualNumber and DualNumber.eps.
- Sheaf.AlgebraicGeometry.GroupScheme.Semisimple: IsSemisimpleGroupScheme (including
  IsSolvableGroupScheme, GroupSchemeDerivedLength and IsDerivedGroupScheme).
- Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData:
  RationalHighestWeight.IsStable and its actual coordinateAlgebra abbreviation.
  The affine instance is passed explicitly through inferInstanceAs (IsAffine G)
  when applying this predicate to Grp.mk (G.asOver ...).
- Sheaf.RingTheory.HopfActionModuleData: HopfAction.Coassociative and Counital;
  their canonical coordinate-Hopf instance is imported through the owning modules.
- Mathlib.LinearAlgebra.Trace: LinearMap.trace, ordinary endomorphism trace.
- Proof imports: Sheaf.RepresentationTheory.CharZeroDifferentiationHom,
  charZero_differentiation_hom; Sheaf.AlgebraicGeometry.CharZeroSemisimpleGroupLie,
  semisimpleGroupScheme_lie_hasTrivialRadical. Their full signatures and proof
  docstrings were read. The other two proof dependencies (surjective semisimple
  Lie image, faithful semisimple trace form) have no Lean record or mathlib match
  at inspection, so have no module to import; they remain named in the proof plan.

Edge cases checked before writing: V=0; a nonzero trivial representation; the trivial
semisimple group; h=0 and the empty trace-dual bases; W=0 and W=V; a nontrivial module
with trivial quotient. None requires Nontrivial V, a nonempty basis, or faithfulness.
The trace form on h=0 is nondegenerate, n=0, and c=0. For W=0 the quotient condition
forces the whole action trivial. For W=V the quotient condition holds and the image
claim is automatic. The coefficient and scheme universe u and vector-space universe v
are explicit and independent. Characteristic zero remains an explicit assumption.

Searches actually run through msearch.py, group Q10 and this item:

- leanfinder: "Casimir operator of rational semisimple algebraic group representation
  is equivariant with trace dimension of differential image" returned eight Lie weight
  trace and trace-form lemmas, including LieModule.traceForm_lieInvariant, and no
  Casimir construction or matching algebraic-group assertion.
- loogle: '"casimir"' returned zero hits.
- grep: 'casimir|Casimir' returned zero Mathlib hits.
- leansearch: "Casimir endomorphism of a semisimple algebraic group has trace the
  dimension of its differential image" returned eight Lie trace-form/weight lemmas,
  including LieModule.traceForm and traceForm_apply_apply. No complete match.
- rg 'casimir|Casimir|semisimple.*[Tt]race' over lean/WeilConjectures and lean/Sheaf:
  only the complete-reducibility proof docstring cites this missing lemma.
- rg by the exact item id in lean/WeilConjectures: no match. Searches for the chosen
  declaration in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json:
  no pre-existing declaration.

Validation: the initial scompile diagnosed only bundled IsAffine inference at IsStable;
explicitly supplying the existing instance fixed it. Both the sandbox and the library-name
compiles then passed, approximately four seconds each. The temporary #check is removed
from the final module. Final clean compile and delivery preflight follow below.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
