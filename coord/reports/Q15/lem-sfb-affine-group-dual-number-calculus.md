## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus` states
`AlgebraicGeometry.AffineGroupDualNumberCalculus.exists_compatible_calculus` with one `sorry`.
The structures `Data` and `Compatible` spell out the conclusion, rather than postulating
unspecified maps. The only map definitions are actual bundlings of existing coefficient
maps: `dualMap` is `DualNumber.mapRingHom` over k, and `reduction` is the existing
`TrivSqZeroExt.fstHom` with restricted scalars. `Kernel` is the exact subtype of points
reducing to identity. No data is chosen from a sorried existence theorem. No other theorem
is postponed, no definition contains sorry, and no statement correction is needed.

Source checked: Milne, *Algebraic Groups* (2017), printed pp.188--193, especially
10.14 and 10.18--10.21 and equations (59)--(61). The arbitrary-R extension follows the
augmentation-quotient calculation of 10.19; none of its steps uses finite generation of R.
The module docstring and theorem docstring carry the source and all twelve DAG proof steps.

Hypotheses and clauses, in order:

- Field k: `{k : Type u} [Field k]`. No algebraic closure, perfectness, or characteristic
  assumption appears. `set_option autoImplicit false` enforces explicit binding.
- Affine finite-type k-group J: `G : Grp (Over (Spec (.of k)))`, with
  `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
  These are precisely the recorded group-object, affine and finite-type conventions.
- The identity and its tangent space: the existing `GrpObj.Lie G.X`, whose actual
  k-linear equivalence with the dependency's `schemeTangentSpace` at the identity is
  `GrpObj.lieIdentityTangentEquiv G.X`. Read its full signature: scalars are restricted
  along the structural k-to-identity-residue-field map. This is an equivalent existing
  model of the same tangent vectors, not a new vector space or an assumed identification.
  `GrpObj.tangentPoint` is the corresponding actual dual-number point. Its formula
  is `infPointsEquivTangentGroup G.X ((lieEquiv G.X).symm v)`, and the source formula
  for `lieIdentityTangentEquiv` uses the same `lieEquiv` and identity-residue transport.
- Finite dimension: `Data.finite : Module.Finite k (GrpObj.Lie G.X)`.
- Every commutative k-algebra R: the fields quantify `(R : Type u) [CommRing R]
  [Algebra k R]`, with no `Nontrivial`, local, finite-type or reduced assumption.
  The common universe includes the field itself, so the test condition is not vacuous;
  the theorem is universe-polymorphic. It follows the existing group and point interfaces.
- Dual numbers and projection: `DualNumber R`, `reduction R`; the latter is exactly
  epsilon-to-zero, as specified by `TrivSqZeroExt.fstHom R R R`.
- Canonical bijections: `Data.E R : (R ⊗[k] GrpObj.Lie G.X) ≃ Kernel G R`.
  Mathlib's extension-of-scalars order R tensor L is used, precisely as the recorded
  `def-weil-module-base-change` specifies; tensor symmetry identifies it with L tensor R.
  Bijectivity includes both directions and kernel membership is part of the codomain.
- R=k defining identification: `Data.normalize` says `E k (1 tensor v)` is exactly
  `GrpObj.tangentPoint v`. The tensor unit isomorphism identifies every k tensor L vector
  this way. Normalization together with coefficient naturality and scaling fixes E on
  every pure tensor r tensor v; additivity fixes it on the whole tensor product.
- Addition, zero, inverse: `Data.add`, `Data.zero`, `Data.neg` state all three displayed
  formulas as equalities in the ambient group of dual-number points.
- Scaling epsilon to a epsilon for every a in R: `Data.scale` uses the existing
  `DualNumber.scale a`, restricted from R-algebras to k-algebras. Its image equals E(a*v)
  using the actual R-module structure on R tensor L.
- Naturality R-to-S: `Data.natural` uses `dualMap h` on points and
  `TensorProduct.map h.toLinearMap LinearMap.id` on the scalar extension.
- Homomorphisms f:J-to-J': the theorem quantifies arbitrary `f : G.X ⟶ H.X`
  with `[IsMonHom f]`. The actual existing `GrpObj.differential f` is a k-linear
  Lie homomorphism; `.toLinearMap` is its k-linear tangent map, not a new supplied map.
  Its defining formula is postcomposition on tangent points
  (`GrpObj.tangentPoint_differential`, read in Lie.Differential).
  `Compatible.differential` is exactly the equation for f(E(v)), with
  `LinearMap.baseChange R` giving df tensor 1 in Mathlib's order.
- Closed subgroup: `Compatible.closed` applies to every `IsClosedSubgroupScheme f`,
  using the recorded definition, and asserts `Function.Injective (GrpObj.differential f)`.
  The range on its left is E_J applied to the image of L_B tensor R under di tensor 1.
  Its right side is literally the range of B(R[epsilon])-to-J(R[epsilon]) intersected
  with the subtype condition defining the kernel of J(p_R). Via `Compatible.differential`
  the left side is precisely the included image of E_B. A closed subgroup of an affine
  finite-type group is affine and finite type, so both groups occur in the quantified
  family; these typeclass binders impose no extra condition on the closed-subgroup clause.
- Ad acts by invertible R-linear maps: `Data.Ad R` is a monoid homomorphism from
  J(R) to `LinearMap.GeneralLinearGroup R (R ⊗[k] L)`, whose units give exactly those
  automorphisms (including the zero-ring case).
- Ad is algebraic, not merely an action on points: `Data.regular` states that in EVERY
  finite basis b, including the empty basis, a UNIQUE actual arrow
  `rho : G.X ⟶ GeneralLinearGroup (ULift (Fin n)) k` is `IsMonHom` and induces Ad on
  ALL algebra-valued points. `GeneralLinearGroup.homMulEquiv` is the existing natural
  points-to-matrices equivalence, and `Matrix.GeneralLinearGroup.toLin' (b.baseChange R)`
  identifies those matrices with invertible R-linear maps on the actual scalar extension.
  Finite dimension ensures such a basis exists, so this condition is not vacuous. Changing
  basis gives the same GL(L) morphism under the usual canonical representation. ULift only
  aligns the index universe with the existing group-scheme interface; it does not exclude n=0.
- Conjugation characterization and constant lift: `Data.conjugation` is the displayed
  formula, and `TrivSqZeroExt.inlAlgHom k R R` is precisely R-to-R[epsilon]. E's injectivity
  fixes Ad uniquely; `regular` also explicitly asserts uniqueness of the scheme morphism.
- Functoriality of Ad under every f: `Compatible.equivariant` is precisely the last
  displayed equation, using `LinearMap.baseChange R (GrpObj.differential f).toLinearMap`.
- All these objects are supplied simultaneously by `exists_compatible_calculus`, so the
  naturality equations refer to the SAME family E and Ad for all groups, never unrelated
  pointwise existentials.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `IsMonHom`, and the group
  structure on point morphisms. Bundling as `Grp` simply supplies the group's structure.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace` and its
  canonical residue-field module; its existing bridge is in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv`:
  `GrpObj.lieIdentityTangentEquiv`. This explains the model mathematically; that
  theorem is not used in the Lean statement and its node is not added to stmt_deps.
  The owning landed definition node `def-wf-lie-algebra-derivation` is cited instead: its
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` record exposes `GrpObj.Lie`,
  its module structure, and `tangentGroup`. It is imported through `Lie.Differential`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring` (through Differential):
  `points`, `points.map`, `GrpObj.Lie`, its base-ring module, `GrpObj.tangentPoint`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential`:
  `GrpObj.differential`, `GrpObj.tangentPoint_differential`.
- `Mathlib.Algebra.DualNumber`: `DualNumber`, `DualNumber.eps`;
  `WeilConjectures.AlgebraicGeometry.DualNumbers`: `DualNumber.mapRingHom`;
  `WeilConjectures.Mathlib.Algebra.DualNumber`: `DualNumber.scale`;
  `Mathlib.Algebra.TrivSqZeroExt.Basic`: `fstHom`, `inlAlgHom`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsClosedSubgroupScheme`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs/Map/Tower`: `TensorProduct`, tensor map,
  `LinearMap.baseChange`; `Mathlib.LinearAlgebra.TensorProduct.Basis`: `Basis.baseChange`.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` (recorded general-linear dependency,
  added to stmt_deps because GL occurs in the statement) publicly imports the existing
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`: `GeneralLinearGroup`
  and `GeneralLinearGroup.homMulEquiv`. No GL or SL scheme is redefined.
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`: `Matrix.GeneralLinearGroup.toLin'`
  and `LinearMap.GeneralLinearGroup.toLinearEquiv`.
- Proof imports: `Mathlib.AlgebraicGeometry.Group.Affine` supplies the coordinate Hopf
  instance; `FiniteType` supplies the affine-pair criterion; `Mathlib.LinearAlgebra.Dual.Lemmas`
  supplies finite duals and rank; `Mathlib.LinearAlgebra.Contraction` supplies
  `lTensorHomEquivHomLTensor`; `Mathlib.Algebra.Module.Projective` supplies projectivity;
  `Mathlib.CategoryTheory.Yoneda` supplies `Yoneda.fullyFaithful`. Every recorded
  proof-dependency module is imported, either publicly when also a statement dependency,
  or as a plain proof import.

Edge cases checked mathematically: the trivial group and any zero-dimensional tangent
module use the empty GL index; R=0 is allowed in every binder and its points and tensor
module are singleton; in characteristic p, alpha_p and mu_p still have nonzero tangent
space and valid E formulas although non-smooth and nonreduced; characteristic 2 retains
negation/inversion and uses no division by 2. Ga and Gm give the expected 1+epsilon*v
formulas and trivial Ad, while noncommutative matrix groups give matrix conjugation.
The identity subgroup, the identity inclusion, zero scalars and identity algebra/group
maps are all retained. No proof branch relies on smoothness or connectedness.

Searches for an exact existing statement:

- msearch leanfinder: "For an affine group scheme, tangent vectors at the identity tensored
  with a k-algebra R identify with dual number points reducing to identity, compatibly
  with conjugation and adjoint action". Eight hits concern cotangent/extensions; no match.
- msearch loogle: "GrpObj.LieAlgebra, GrpObj.lieEquivTangent, DualNumber". No hits;
  the service reports the first identifier unknown (the actual Lie module is project code).
- msearch leansearch: "affine group scheme Lie algebra scalar extension dual number points
  adjoint representation". Eight hits include LieAlgebra.ad, dual-number lifts and scalar
  extension of Lie algebras; no affine-group scalar-extended tangent/adjoint statement.
- msearch grep: "adjoint|lieEquivTangent|dualNumber" in Mathlib AlgebraicGeometry/Group:
  no hits. Direct rg in the project's GroupScheme and relevant Sheaf modules locates the
  existing tangent, Lie and matrix-group APIs, all reused; no general affine-group
  scalar-extension plus adjoint theorem. Search for this node id in WeilConjectures and
  for the new namespace in WeilConjectures, Sheaf and dag/lean_names_upstream gives no match.
- Exact-source inspection found and reused `DualNumber.scale`, `DualNumber.mapRingHom`,
  `GrpObj.tangentPoint`, `GrpObj.differential`, `lieIdentityTangentEquiv` and the existing GL
  scheme. These searches prevented private replacements of the canonical constructions.

There are no new notion nodes and no dependency repairs. The two added stmt_deps are
already landed definition nodes exposing the Lie module and general linear scheme. The natural-language statement, proof and proof_deps are unchanged.

Validation: server scompile passed both its sandbox check and actual library-module check,
with no errors or warnings. All delivered lines are at most 100 characters. The only sorry
is the named main theorem, with its complete twelve-step proof docstring.

## Repair of returned delivery dab04fad0a04

H2: replaced `lem-ag-lie-identity-tangent-equiv` in stmt_deps with the owning landed
definition node `def-wf-lie-algebra-derivation`, and retained `def-sc-general-linear-group`.
Read the owner's full current Lean record and the definitions of `GrpObj.Lie`, its
base-ring module, and `tangentGroup` in Lie.Basic and Lie.Ring, imported through
Lie.Differential and its public Lie.Bracket import. These are the objects actually used.
Removed exactly the public import of LieIdentityTangentEquiv. The rest of the Lean file
is byte-for-byte unchanged from the retained returned delivery, including all signatures,
proof docstrings and its single sorry. The Lie/tangent bridge remains mentioned only as
mathematical explanation; it is not a Lean dependency. The advisory about unowned
points/tangentPoint/differential records requires no declaration or node changes.

Compared with current main: the item still has no Lean record and the original ten
stmt_deps. The repaired node changes only lean and adds the two specified landed
definition nodes. The delivery wrapper rebases those edits on current main.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
