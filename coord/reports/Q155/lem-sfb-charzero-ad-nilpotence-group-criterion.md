## Worker report

The module `Sheaf.AlgebraicGeometry.CharZeroAdNilpotenceGroupCriterion` states
`AlgebraicGeometry.charZero_nilpotent_of_ad_nilpotent`. Its only theorem proof is
`sorry`. No definitions, auxiliary statements, or node corrections were needed;
the copied node changes only in `lean` and the addition of the landed owning
node `def-wf-lie-algebra-derivation` to `stmt_deps`.

Hypotheses and clauses, checked against the node:

- A field k: `(k : Type u) [Field k]`. Characteristic zero: `[CharZero k]`.
- The fixed algebraic closure: `(kbar : Type v) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]`. It is only background data in this criterion; neither
  the premise nor the conclusion requires scalar extension. Its universe v is
  independent of u, and k is not assumed algebraically closed.
- A k-group scheme: `G : Grp (Over (Spec (.of k)))`. This packages precisely an
  object over Spec k with `CategoryTheory.GrpObj`, not a commutative group object.
- Affine: `haff : IsAffine G.X.left`.
- Smooth: `hsm : Smooth G.X.hom`.
- Connected: `hconn : ConnectedSpace G.X.left`, including nonemptiness.
- Finite type: `hft : LocallyOfFiniteType G.X.hom` and
  `hqc : QuasiCompact G.X.hom`, exactly the recorded dependency's convention.
- The identity tangent space with its canonical commutator bracket is
  `GrpObj.Lie G.X`. This is the existing cotangent-dual realization, not an
  arbitrary Lie algebra placed on the tangent space. The landed owning node
  `def-wf-lie-algebra-derivation`, now in `stmt_deps`, records `GrpObj.Lie`,
  `GrpObj.lieEquivTangent` and its canonical Lie structures.
  `GrpObj.lieEquivTangent` realizes its vectors as dual-number points at the
  identity. `GrpObj.instBracketLie` constructs the
  bracket as the mixed term of the group commutator over k[epsilon][delta].
- The adjoint Lie operator is `LieAlgebra.ad k (GrpObj.Lie G.X) X`;
  `LieAlgebra.ad_apply` identifies its value on Y with the canonical bracket.
  The introductory description of Ad does not impose an additional hypothesis
  or ask for the choice of an arbitrary representation; no such choice occurs
  in the formal statement.
- The nilpotence premise is `had : ∀ X, ∃ m : ℕ, 1 ≤ m ∧ (ad ... X)^m = 0`.
  Each X has its own positive exponent; there is no uniform-exponent assumption.
- Nilpotence of G is stated in full: `∃ c C i`, with
  `C : Fin (c+1) → Grp (Over (Spec (.of k)))` and `i j : C j ⟶ G`.
  These are actual group schemes and group-scheme homomorphisms.
- Every term is closed and normal in G:
  `∀ j, IsClosedSubgroupScheme (i j).hom.hom ∧
  IsNormalSubgroupScheme (i j).hom.hom`. The existing classes supply pointwise
  injectivity, the closed immersion, and normality on all algebra-valued points.
- G_0 = G as subgroups is `IsIso (i 0)`: its inclusion has full image.
  G_c = 1 is `Nonempty (C (Fin.last c) ≅ Grp.trivial _)`.
  These are the invariant categorical forms of equality of subgroup schemes,
  with no arbitrary identification required as extra input.
- Descent `G_(j+1) ⊆ G_j` is witnessed by
  `∃ l : C j.succ ⟶ C j.castSucc, l ≫ i j.castSucc = i j.succ`.
  Since both ambient inclusions are closed immersions and injective, this
  factorization really is the inclusion of the indicated closed subgroups.
- The index range is `j : Fin c`; the two terms are `j.castSucc` and `j.succ`.
  For every `(A : Type u) [CommRing A] [Algebra k A]`, g is a morphism
  `Spec A ⟶ G` over k and h is a morphism `Spec A ⟶ C_j` over k. Membership
  of their commutator in C_(j+1)(A) is the existence of z with
  `z ≫ i_(j+1) = g * (h ≫ i_j) * g⁻¹ * (h ≫ i_j)⁻¹`.
  In particular this includes i = c-1, with target the trivial subgroup.
  No assumption of reducedness, nontriviality, or finite type on A is made.
  A lives in the scheme/field universe u as in the recorded subgroup-scheme
  definitions, never in an independent smaller universe.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`. The latter represents
  the arbitrary fixed closure in the statement.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and the bundled
  `CategoryTheory.Grp` for objects of `Over (Spec (.of k))`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`:
  `AlgebraicGeometry.schemeTangentSpace`, its canonical additive and module
  instances, and `schemeTangentMap`; the latter is not needed in this criterion.
  These tangent-space declarations were read for comparison, but are not
  used in the formal signature and their separate bridge module is not imported.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic`: `GrpObj.Lie`;
  `.Lie.Bracket`: `GrpObj.lieEquivTangent`, `GrpObj.lie_def`,
  `GrpObj.instBracketLie`, `GrpObj.instLieRingLie`, `GrpObj.instLieAlgebraLie`.
  All structures are the existing canonical constructions owned by the landed
  `def-wf-lie-algebra-derivation` record. Its complete statement, declaration
  record, and the defining upstream signatures/docstrings were reread for repair.
- `Mathlib.Algebra.Lie.Basic`: `LieRing`, `LieAlgebra`;
  `Mathlib.Algebra.Lie.OfAssociative`: `LieAlgebra.ad`, `LieAlgebra.ad_apply`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme`.
- Proof dependency `lem-sfb-noetherian-lie-engel-criterion` has the exact Mathlib
  match `LieAlgebra.isNilpotent_iff_forall` in `Mathlib.Algebra.Lie.Engel`.
  Per the return, its unused private import is removed for this statement-only
  delivery; the natural-language proof still records its use.
  The other two proof dependencies currently have no Lean records
  or Mathlib matches and thus no module to import. Their intended use is
  documented step by step in the theorem docstring, following all five DAG
  proof steps. Neither is needed to type this theorem's statement.

Edge cases checked before writing:

- c = 0: Fin 1 has only one term. The first inclusion is an isomorphism and that
  term is trivial, so this case describes exactly a trivial ambient group;
  the transition and commutator clauses have empty index sets.
- c = 1: the commutator clause requires every commutator to be trivial and
  consequently describes a commutative ambient group.
- Lie(G) = 0: the premise still has a positive exponent (take m = 1);
  no positive-dimension hypothesis is present. The proof's J = 0 construction
  gives a valid series, including when G is a nontrivial commutative group.
- The trivial group is permitted, as are nontrivial tori: their adjoint Lie
  operators vanish, and their central series can have length one.
- Nonreduced and zero test algebras are included by `[CommRing A]` with no
  `IsReduced` or `Nontrivial A` hypothesis. No commutativity is assumed on G.
- Characteristic zero and connectedness are retained: disconnected finite
  nonnilpotent groups have zero Lie algebra and must not be included.

Searches for existing statements and notions:

- msearch leansearch, query "A connected algebraic group in characteristic zero
  is nilpotent when every adjoint Lie endomorphism is nilpotent": 8 results,
  including `LieAlgebra.isNilpotent_iff_forall` and
  `LieAlgebra.isNilpotent_range_ad_iff`; these concern Lie algebras, not
  integration to a central series of group schemes.
- msearch leanfinder, query "Smooth connected affine algebraic group characteristic
  zero nilpotent if adjoint Lie endomorphisms nilpotent": 8 results, led by
  `LieAlgebra.nilpotent_ad_of_nilpotent_algebra` and the Engel criterion;
  no group-scheme criterion.
- msearch loogle, query `LieAlgebra.ad, IsNilpotent`: 8 results, including the
  Engel criterion and associative adjoint nilpotence; no group-scheme conclusion.
- msearch grep, query `nilpotent.*Lie|Lie.*nilpotent`, Mathlib AlgebraicGeometry:
  no hits.
- rg in `lean/WeilConjectures/AlgebraicGeometry/GroupScheme` and
  `lean/Sheaf/AlgebraicGeometry` for Lie algebra, tangent, nilpotence, and
  central-series names found the canonical Lie API and the related statements
  `nilpotent_connected_central_series` and `central_maximal_torus_nilpotent`.
  Their full signatures were read: the former starts from a supplied series;
  the latter assumes a central maximal torus and an algebraically closed base.
  Neither is this criterion. The central-series encoding is consistent with
  these existing consumers; it does not introduce another definition.
- rg for the item ID in `lean/WeilConjectures` found no existing statement.
  rg for the proposed declaration name in Mathlib, both project roots and
  `dag/lean_names_upstream.json` found no collision.
- DAG searches for identity tangent Lie algebras found `sk-d-tangent` and the
  existing tangent-transport nodes; no new copy of that notion is introduced.

Source check: read the local Milne PDF at Proposition 17.80 and Proposition
17.74, the Lie-detection Proposition 10.15, and the descending central-series
Proposition 6.38. The node is explicitly an intermediate agent-supplied criterion,
not a numbered assertion attributed verbatim to Milne. No disputed statement
or node fault was found.

Validation: scompile.py compiled the sandbox file and its library-module form
cleanly after repair (49.8 seconds for the sandbox and 10.0 seconds for the
library-module form). All variables/universes are explicitly bound and
`autoImplicit` is false. The theorem proof remains `sorry`, as required.

## Repair of returned head 53c1a2da9542

- H2: added the already landed `def-wf-lie-algebra-derivation` to the item’s
  `stmt_deps`, as explicitly authorized by the return and brief §1. Its existing
  Lean record owns `GrpObj.Lie`, the bracket, and the `LieAlgebra k` instance
  used in the premise. No dependency node is changed or duplicated.
- H9: removed both unused imports: `Mathlib.Algebra.Lie.Engel` and
  `WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv`.
  The module documentation now refers to the retained `lieEquivTangent` API.
- Compared the retained delivery with current main: before repair, only the
  item’s `lean` record differed. Reconstructed the node copy from current main,
  retained that signature verbatim, and added exactly the owning dependency.
  The theorem statement, all hypotheses and clauses, and the five-step proof
  docstring are preserved. Delivery is rebased by the prescribed wrapper.

## Second reading by Q155

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
