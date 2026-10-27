## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.InfiniteFieldSemisimpleCentralizerReduction`
states `AlgebraicGeometry.exists_semisimple_lie_centralizer_reduction`, with one `sorry` and
no proved theorem. Its docstring contains all eight proof steps of the DAG verbatim, with
line wrapping only. The mathematical statement is unchanged. The semisimple-element helper definition module
has real data and no `sorry`; the coefficient map is reused from its existing live module. No released repair note exists for this item.

Hypothesis and clause correspondence:

- A field, infinite: `{k : Type u} [Field k] [Infinite k]`.
- A fixed algebraic closure: `(Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]`.
  This allows an arbitrary chosen algebraic closure, rather than assuming perfection of k.
- Group scheme: `G : Grp (Over (Spec (.of k)))`. The existing group object supplies all group
  laws. Affineness is `[IsAffine G.X.left]`; finite type is
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- Smoothness and connectedness: `[Smooth G.X.hom] [ConnectedSpace G.X.left]`.
  ConnectedSpace includes nonemptiness, as the definition node requires.
- Geometric Lie algebra: `GrpObj.Lie ((MultiplicativeType.baseChange (K := Ω)).obj G).X`.
  This is the actual scalar-extended group with its pulled-back group structure, not an
  arbitrary Lie algebra or an assumed base-change isomorphism.
- A geometric semisimple noncentral element: `hgeom` supplies S, its
  `HasDiagonalizableFaithfulLieImage Ω ... S`, and Y with `⁅S, Y⁆ ≠ 0`.
  Over Ω the diagonalization is over Ω itself; over k it is after entrywise scalar extension.
- Rational semisimple noncentral X: the conclusion existentially supplies
  `X : GrpObj.Lie G.X`, `HasDiagonalizableFaithfulLieImage Ω G X`, and a rational Y with
  `⁅X, Y⁆ ≠ 0`. The new predicate means a positive-size closed faithful representation whose
  differential becomes conjugate to `Matrix.diagonal d` over Ω. It does not substitute
  semisimplicity of the abstract Lie algebra or of the adjoint endomorphism alone.
- C is a smooth proper closed subgroup: `C : Grp ...`, `i : C ⟶ G`,
  `IsClosedSubgroupScheme i.hom.hom`, `¬ IsIso i.hom.hom.left`, `Smooth C.X.hom`.
  Its affine, local finite type and quasi-compact properties are stated explicitly, matching
  the node's standing conventions for all groups.
- Representation of the entire adjoint stabilizer functor: for every commutative k-algebra R
  and `g : points G.X R`, existence of c with `c ≫ i.hom.hom = g` is equivalent to
  commutation of the constant lift of g with the scalar-extended tangent point of X.
  Scalar extension is `points.map ... (dualMap (Algebra.ofId k R)) (GrpObj.tangentPoint X)`;
  the constant lift is `points.map ... (TrivSqZeroExt.inlAlgHom k R R) g`.
  The canonical calculus's `Data.normalize` and `Data.natural` identify this point with
  E_R(1 tensor X). Its `Data.conjugation` identifies commutation exactly with
  Ad_R(g)(1 tensor X)=1 tensor X, since E_R is injective. Thus no arbitrary map is used.
  Closed immersion gives injectivity on points and this image equality gives the natural
  representing identification, including nonreduced and zero test algebras.
- K=C^0 with its open-subscheme structure: `j : K ⟶ C`,
  `IsOpenImmersion j.hom.hom.left`, and
  `Set.range j.hom.hom.left = connectedComponent (GrpObj.onePoint C.X)`.
  An open immersion with that range identifies K with that precise open subscheme. No
  connectedness assumption on C occurs.
- K is a smooth connected affine closed k-subgroup of G:
  `IsClosedSubgroupScheme (j ≫ i).hom.hom`, `IsAffine K.X.left`, `Smooth K.X.hom`,
  `ConnectedSpace K.X.left`, plus the finite-type pair for K.
- Strict dimension drop: `topologicalKrullDim K.X.left < topologicalKrullDim G.X.left`,
  using the extended Krull dimension rather than a natural-number truncation.
- K is not unipotent: the negation of existence of n>0 and a closed group-scheme embedding
  r into GL_n such that every R-point has diagonal entries 1 and below-diagonal entries 0.
  This is precisely a closed immersion into U_n; no geometric-point replacement or smoothness
  assumption is buried in this notion. We do not reuse `SolvableGroupStructure.IsUnipotent`,
  whose definition instead adds smoothness and uses nilpotent geometric matrices.
- The torus sentence only sets terminology; no torus is quantified or asserted in this lemma.
  The existing `MultiplicativeType.IsTorus` has exactly the stated meaning, including rank 0.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`, `Grp`, `IsMonHom`; group schemes in Over Spec k.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`. Its parent classes supply a genuine homomorphism and point
  injectivity, and its last field supplies `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact: `LocallyOfFiniteType`,
  `QuasiCompact`; Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`, `connectedComponent`.
- Mathlib.FieldTheory.IsAlgClosed.Basic and AlgebraicClosure: `IsAlgClosure`, `AlgebraicClosure`.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `multiplicative`, the recorded G_m; this is
  publicly imported by ToriMultiplicativeType, whose `baseChange` is used in the hypothesis.
- Sheaf.AlgebraicGeometry.LinearGroupSchemes: the general-linear node's main declaration is
  SL, but its record explicitly uses the upstream GeneralLinearGroup rather than defining a
  new GL. That exact upstream `GeneralLinearGroup` and `homMulEquiv` are used here.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- WeilConjectures.AlgebraicGeometry.SchemeTangentSpace: `schemeTangentSpace` and its canonical
  vector-space and differential declarations were read. We use its existing identity-tangent
  realization `GrpObj.Lie`, not a second tangent space.
- Mathlib.Algebra.Lie.Basic and OfAssociative: `LieRing`, `LieAlgebra`, bracket, `LieAlgebra.ad`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket and Lie.Differential:
  `GrpObj.Lie`, `lieEquivTangent`, the canonical commutator Lie instances, `tangentPoint`,
  `differential`. The owning definition `def-wf-lie-algebra-derivation` is added to stmt_deps.
- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie:
  `RationalHom.differential`, `lieAlgebraEquivMatrix`, with their complete signatures read.
- Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus: the existing `dualMap`, reused
  with an `existing: true` record on def-sfb-dual-number-coefficient-map. The existing
  `Data.normalize`, `Data.natural`, `Data.conjugation` explain the stabilizer rendering.
  Its theorem remains only in proof_deps; the definition node is cited in stmt_deps.
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType: `baseChange` and `IsTorus`; its owning node
  is added to stmt_deps. No new scalar-extension construction is introduced.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`.

Proof imports are the recorded existing `LieLocalDimension`, `IdentityLocalDimension`,
`Mathlib.AlgebraicGeometry.OpenImmersion`, and the Smooth module; the calculus module is a
public import because it also supplies the existing coefficient-map definition.
Other proof nodes currently have no recorded module, so there is no module to import for them.
No missing proof theorem is assumed as an extra hypothesis. No import cycle was introduced.

Edge cases checked before drafting: trivial and commutative groups cannot satisfy hgeom because
all brackets vanish; dimension-zero smooth connected groups are likewise excluded by that
hypothesis. C need not be connected. K is the whole open identity component, with no reduction.
Positive characteristic and imperfect fields remain allowed; neither CharZero nor PerfectField
is assumed. The node's proof separately handles restricted powers in positive characteristic.
The zero tangent vector can satisfy the helper definition but fails the noncentrality condition.
A positive-size representation of a trivial group is allowed; n=1 unitriangular matrices are
trivial, so that case is correctly included in the negated existential. The zero algebra R is
included in both the stabilizer and unitriangular clauses. ULift (Fin n) matches the existing
GL universe convention. Ω, group schemes and their coefficient test algebras have the common
universe of the library's group-scheme API; arbitrary sizes are covered by universe u, with
no site-universe equality or algebraic-closedness restriction on k imposed.

Searches actually run with msearch.py:

1. leanfinder: “Over an infinite field a smooth connected affine group with a geometric
   noncentral semisimple Lie element has a smaller smooth nonunipotent centralizer identity
   component”: 8 hits, Cartan/regular elements, nilpotence, and central radical results;
   none states this group-scheme result.
2. loogle: `LieAlgebra, "centralizer"`: 0 hits.
3. grep Mathlib: `semisimple.*centralizer|centralizer.*semisimple`: 0 hits.
4. leansearch: “A tangent element of an affine group scheme is geometrically semisimple if its
   differential in a faithful closed linear representation is diagonalizable over an algebraic
   closure”: 8 hits, affine schemes/geometric reducedness/analytic tangent spaces; no match.
5. leanfinder: “A Lie algebra element of an affine group scheme is semisimple when its matrix
   differential under a faithful closed representation is diagonalizable over an algebraic
   closure”: 8 hits, semisimple Lie algebras, regular elements, and Killing results; no match.
6. grep Mathlib: `IsSemisimpleLieElement|semisimpleLieElement|[Ss]emisimple.*[Tt]angent|`
   `[Tt]angent.*[Ss]emisimple`: 0 hits.
7. rg of the same concepts in WeilConjectures and Sheaf finds only a tangent Lie algebra of a
   semisimple group, not an element predicate. Searches by the item id and centralizer/reduction
   find no existing statement. dag/lean_names_upstream.json has semisimple modules and Lie
   algebras, no semisimple tangent-element predicate. DAG search finds statements using the
   inline notion, no definition node. blueprint_refs search “semisimple element”: 0 matches;
   ancestor reports blueprint.from.node=None, retained on the new definition node.

Source read directly: Milne printed pp.377--379 (PDF pages 389--391), including the proofs of
17.76--17.79 and the semisimple-centralizer case of 17.81. There is no statement correction
and no STATEMENT-DISPUTED flag.

Validation: scompile.py compiled both delivered modules separately in dependency order with
no errors or unexpected warnings (definition 1.4 seconds, theorem 14.3 seconds for library names).
The theorem has the single intended sorry. All universes and variables are explicit, with
`set_option autoImplicit false`. No local notation, local instance or private definition.

## New nodes

`def-sfb-semisimple-lie-element` defines `GrpObj.HasDiagonalizableFaithfulLieImage K G X` by a
positive-size closed representation and a genuine invertible conjugating matrix over K. Its
specialization to an algebraic closure is the node's geometric semisimplicity. Source: Milne
17.74--17.75, p.377, read with the algebraic-representation faithful-detection clause in the
existing Jordan node. It reuses the actual group-scheme differential, Matrix.map and diagonal.
LeanSearch, LeanFinder, Mathlib grep, source/Sheaf/DAG searches and blueprint search above find
no existing definition of this element notion; semisimplicity of Lie algebras or lisse Weil
representations has different objects. No theorem, choice or arbitrary data is postponed.


`def-sfb-dual-number-coefficient-map` owns the existing
`AlgebraicGeometry.AffineGroupDualNumberCalculus.dualMap` in
`Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus`, with `existing: true` and no file. For a field k, commutative k-algebras
R,S and h:R→ₐ[k]S it sends a+bε to h(a)+h(b)ε as a k-algebra map. These are exactly its
binders and output; its data is the existing upstream `DualNumber.mapRingHom h.toRingHom`
with the unchanged scalar-compatibility field. Source: Milne 10.18--10.19, pp.191--192.
The existing definition stays in the live calculus module. Its signature and full
implementation were reread locally and with scompile.py --source. This new node binds that
exact existing declaration without creating a second implementation or moving any live code. Edge cases: h=id, k→R, nonreduced and zero coefficient algebras are allowed.

Searches for the new ownership node: msearch LeanSearch with “A homomorphism of k algebras
induces a k algebra homomorphism of dual number rings by applying it to both coefficients”
gave 8 hits (polynomial and power-series maps, and the general DualNumber.lift universal
property), no direct bundled coefficient map. Loogle `DualNumber.mapRingHom` gave unknown
identifier/0 hits; Mathlib grep `mapRingHom|mapAlgHom` in Algebra/DualNumber.lean gave 0 hits.
Upstream/project rg found the exact old dualMap in the calculus module and the underlying
ring map in WeilConjectures.AlgebraicGeometry.DualNumbers:80. Mathlib has no direct bundled
k-algebra coefficient map. The specialized upstream mapOfAlgHom has target k[ε], so cannot
replace general R[ε]→S[ε]. DAG search found no definition node for the algebra map;
coefficientwise-ring-hom-map concerns polynomials and power series. blueprint_refs search
“dual number” returned 0 matches, and ancestor remains null. Actual search results are in
the new node's mathlib_searches and the sandbox search log.

## Second reading by Q151

This is the dispatcher's single-worker self-audit; no separate agent was started, as instructed.
The maintainer's independent reading remains the external review. I reopened the item JSON and
both complete modules after compilation. Every binder and conclusion was matched above.
The helper has n>0, a closed group representation, the canonical differential, entrywise base
extension and invertible conjugation, rather than an arbitrary Lie representation. The main
hypothesis uses Lie of the actual base-changed group; its conclusion uses rational Lie(G).
The centralizer's iff quantifies all test algebras. Its dual-number equation is pinned to the
existing tangent point and the exact natural scalar-extension map. j is an open immersion
with exact identity-component range. The closed-subgroup, affine, finite type, smooth,
connected, strict-dimension and nonunitriangular clauses are all present. No assumption of
connected C or perfect k was introduced. The only node changes are lean and additions of the
owning definition dependencies. The current repair reuses the existing coefficient map
through its definition node, with no dependency-module replacement, as detailed below. No mathematical statement correction is needed.


## Returned delivery repair

Repaired the duplicate-declaration return at immutable head 30450226f1f0. Compared the
retained returned sandbox with current live source, also read through
`scompile.py --source Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus`. The live
module still defines `AlgebraicGeometry.AffineGroupDualNumberCalculus.dualMap`, whose
complete signature and body are exactly the coefficient map required here. Following this
return's instruction to import and reuse it, removed the delivered DualNumberCoefficientMap
module and the replacement calculus module and dependency-node record. The definition node
def-sfb-dual-number-coefficient-map now has `existing: true`, no `file`, and points directly
to the existing live calculus declaration. No declaration is renamed or declared twice.
The main module publicly imports that existing module once.

The earlier H2/H4 distinction is preserved: the coefficient-map definition node is in
stmt_deps, and the calculus theorem is only in proof_deps. Importing its module to use
a plain definition does not assume its theorem. No theorem signature, mathematical
statement, docstring proof step or semisimple-element definition changed in this repair.
No dependency modules are delivered. The wrapper constructs the repaired commit on current
main, without any direct git mutation by this worker.

Repair self-audit: reread the main signature and definition records with the live calculus
source open. The coefficient-map binders are arbitrary commutative k-algebras R and S and
a k-algebra homomorphism h; the underlying DualNumber.mapRingHom applies h to each
coefficient and commutes with k. This matches every clause of the new definition node,
including identity maps, nonreduced rings and the zero algebra. Exactly two Lean modules
remain in this delivery, neither defining dualMap. The main theorem's complete signature
is unchanged from the reviewed head; only its imports and record date changed.

Current repair validation: scompile.py compiled the two remaining delivered modules
separately against the live build, including the original calculus module supplying dualMap.
It exited 0 with no errors or unexpected warnings (library definition 1.4 seconds;
library theorem 14.3 seconds). The exact recorded theorem signature is present verbatim
in the main file, all Lean lines are at most 100 characters, and the item changes only
lean and stmt_deps relative to current main.
