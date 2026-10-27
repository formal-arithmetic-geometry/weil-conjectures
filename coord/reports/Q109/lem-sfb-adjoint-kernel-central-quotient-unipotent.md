## Worker report

Q109 states `AlgebraicGeometry.adjointKernel_central_quotient_unipotent` in
`Sheaf.AlgebraicGeometry.AdjointKernelCentralQuotientUnipotent`. Its sole proof
is `sorry`. The delivery also defines `AlgebraicGeometry.adjointKernelPoints`
with actual data (a set comprehension) in a new definition node. No mathematical
statement has been corrected, and no source or compiled library file was edited.

Source checked: Milne, Algebraic Groups (2017), printed p.285 (PDF p.297),
Proposition 14.23, and printed pp.192--193 (PDF pp.204--205), 10.20--10.23.
10.20 explicitly defines Ad on every algebra R by inner automorphisms on
ker(G(R[epsilon]) -> G(R)); equation (60) is precisely the commutation test used
here. Proposition 14.23 uses truncated local rings and their maximal-ideal flags,
as does the full five-step proof docstring. The current blueprint is
literature/blueprint/latest (main-20261024); blueprint_refs ancestor returns null
for this inherited chain, as in the node's retained provenance. The item is a
supporting lemma, not the blueprint unit's own statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The universe u is explicit, with no characteristic assumption.
- A group scheme is `Grp (Over (Spec (.of F)))`; its homomorphisms are bundled
  morphisms of that category. These use the recorded `GrpObj`/`Grp` interface.
- Smooth connected affine finite type G is `hG : SolvableGroupStructure.IsAlgebraic G`,
  `hsm : Smooth G.X.hom`, and `hc : ConnectedSpace G.X.left`. IsAlgebraic is exactly
  IsAffine, LocallyOfFiniteType and QuasiCompact, not a reductivity hypothesis.
- The tangent space and differentiated conjugation are specified without choosing
  a basis or a new Lie algebra: `adjointKernelPoints G A` tests the actual tangent
  points in `G(A[epsilon])` that reduce to 1. The constant extension of g must commute
  with every such point. Milne 10.20 and (60) identify this exactly with Ad_A(g)=1.
  The existing upstream tangentGroup uses the identical augmentation criterion.
  In particular this is the kernel of group-scheme Ad, not the kernel of the
  Lie-algebra map ad, nor a test solely on F-valued points.
- N=ker Ad is `(N, iN, hiN, hN)`: iN is its specified closed subgroup inclusion,
  and hN identifies its represented image with `adjointKernelPoints` for EVERY
  commutative F-algebra A. This is an exact interface for the canonical N already
  named in the node, not an arbitrary action or an extra faithfulness assumption.
  Closedness is intrinsic to that kernel, as the recorded
  `isClosedSubgroupScheme_kerι` confirms. No finite type, smoothness, reducedness
  or connectedness hypothesis is imposed on N.
- Z(G)(A) is the EXISTING
  `ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A`. Its definition quantifies
  over every A -> B and every G(B)-point, retaining exactly the universal
  commutation condition. `exists_affine_group_centre_baseChange` supplies its
  represented closed subgroup. It is not replaced by the centre of G(A).
- `∃ n : ℕ, 0 < n` is the requested n>=1. `ULift.{u} (Fin n)` only aligns the
  index universe of the existing GL_n construction with F; it has exactly n elements.
- `U` and `j : U.X -> GeneralLinearGroup ... F` with `IsClosedSubgroupScheme j`
  are a closed subgroup of GL_n. For EVERY commutative algebra A and every U(A)-point,
  the first matrix clause says every diagonal entry is 1 and the second says
  entry (a,b) is zero when b<a. These are exactly the equations defining U_n.
  This is equivalently a closed subgroup U of U_n: U_n is the closed subscheme of
  GL_n cut out by those equations; test the universal point of the affine U to
  factor j through it. The resulting factor is closed since the ideals defining
  U_n are contained in those defining U. Conversely composing any closed subgroup
  U -> U_n with U_n -> GL_n gives exactly this j. Thus no representation,
  point condition, smoothness or connectedness of U has been added or dropped.
- `q : N -> U` is a group-scheme homomorphism.
- The first kernel clause takes the range of the actual pullback-kernel inclusion
  `GrpObj.kerι q.hom.hom` followed by iN and identifies it with Z(G)(A), on every A.
  This is equality of the CLOSED represented subgroup functors in G, hence a
  scheme-theoretic equality, including its embedding. In particular it explicitly
  asserts that all centre points lie in N. The final equivalence separately states
  `q_A(g)=1 iff iN_A(g) in Z(G)(A)`, as the node's last clause asks.
- There is no reductivity assumption on G and no smoothness or connectedness
  assumption on N or U. q is not required to be surjective, just as in the node.

Dependency declarations reused:

- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, Grp, IsMonHom and
  the group of points; WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  IsSubgroupScheme, IsClosedSubgroupScheme and the intrinsic closedness of kernels.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth;
  Morphisms.FiniteType: LocallyOfFiniteType; Morphisms.QuasiCompact: QuasiCompact;
  Mathlib.Topology.Connected.Basic: ConnectedSpace;
  Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed.
- Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange:
  exists_affine_group_centre_baseChange, publicly exposing the existing
  centralizerPoints, SolvableGroupStructure.IsAlgebraic and affine test schemes.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: affine and map. The maps in the
  definition are precisely TrivSqZeroExt.fstHom F A A and inlAlgHom F A A;
  Mathlib.Algebra.DualNumber: DualNumber. There is no second dual-number definition.
- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear:
  GeneralLinearGroup and homMulEquiv. Its source docstrings and full signature
  were read; no GL_n definition is copied.
- Proof-only imports are RationalTangentCotangentDuality and
  GroupScheme.HomomorphismFactorization, matching their recorded proof dependencies.
  lem-sfb-conjugation-finite-jet-kernel currently has no Lean record/module, so
  there is no module to import; it is named with its use in the proof docstring.
  It is not needed to elaborate the statement and is not restated in this delivery.

Edge cases checked: trivial G and arbitrary commutative G have N=G and centre G;
U can be trivial in U_1 and q trivial. n=1 is allowed (the below-diagonal condition
has no pairs); n=0 is excluded exactly as the node says. Positive characteristic,
including nonreduced central kernels such as mu_p, remains included because all
conditions quantify over arbitrary algebras. The zero test ring is allowed; its
points are unique, and all equations remain valid. The empty scheme cannot be a
group over a nonzero field; ConnectedSpace has its intended nonempty convention.
Nontrivial unipotent adjoint kernels are not ruled out. No reducedness assumption
on A is made anywhere.

Searches: msearch.py leanfinder queried the item in plain words and the dual-number
adjoint-kernel functor; results were LieDerivation.ad_ker_eq_center and other
Lie-algebra/adjunction results, not group-scheme Ad. Loogle queried
AlgebraicGeometry.GeneralLinearGroup, TrivSqZeroExt.fstAlgHom, and inlAlgHom;
the service did not index the project GL_n name and reported no hit. msearch.py
grep for adjointRepresentation|adjointKernel|unitriangular|Unitriangular found none.
LeanSearch queried the adjoint kernel via dual numbers, finding Lie-algebra ad
kernels, Scheme.kerAdjunction and unrelated kernels. All exact tool responses are
in searches.jsonl and copied into the new definition node's mathlib_searches.
Direct rg searches of WeilConjectures, Sheaf and Mathlib found the existing GL_n,
dual numbers, and tangentGroup, but no group-scheme adjoint kernel interface.
The required item-id search in WeilConjectures found no declaration. DAG searches
and blueprint_refs search found no definition of the adjoint-kernel point functor;
sk-d-tangent discusses the adjoint ACTION, not its kernel point subfunctor.
The existing CompactObject example has been withdrawn, so its recorded upstream
module was inspected for the module/header conventions instead.

Validation: both delivered modules compiled separately through scompile.py against
the live server build; the only postponed result is the main theorem.
No STATEMENT-DISPUTED or node fault was found.

## New nodes

`def-sfb-adjoint-kernel-points` defines K_G(A) by the actual constant inclusion
A -> A[epsilon], augmentation A[epsilon] -> A, and commutation with the kernel
of reduction on G-points. Source is Milne 10.20--10.23 and 14.23. It is needed
because no existing recorded declaration gives the group-scheme adjoint kernel
on arbitrary algebras. It reuses the existing affine/map and DualNumber
constructions. The set definition contains no sorry, choice or arbitrary map.
The three search kinds, direct source searches, and blueprint/DAG searches are
recorded in its mathlib_searches. Its only new declaration is adjointKernelPoints.

## Second reading by Q109

Self-review by the dispatched worker; no other agent was started (the brief
forbids it). The maintainer performs the independent review of the delivery.
I reopened the node, definition and theorem and checked each binder and conjunct
against the correspondence above. The main signature initially only expressed
q(g)=1 iff iN(g) is central. I added the separate equality of the actual pullback
kernel's image subfunctor with the entire centre subfunctor, so the inclusion of
Z(G) into N and the scheme-theoretic kernel equality are explicit, in addition
to the node's requested pointwise equivalence. I checked the orientation of matrix
indices (b<a is below the diagonal), both directions of the equivalence between
a closed subgroup of U_n and the stated closed GL_n embedding, and the dual-number
maps (fst reduces a tangent point; inl extends g constantly). The final statements
use the source's objects and all its hypotheses. No node statement changed.
