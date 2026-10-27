## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupLieTangentCalculus` states
`AlgebraicGeometry.GrpObj.affine_group_lie_tangent_calculus`, with one `sorry`
and no new definitions. The node statement, source and split are unchanged.
The seven original statement dependencies are retained, and the returned delivery
is repaired by adding the landed `def-wf-lie-algebra-derivation` statement dependency.

Hypotheses and clauses:

- Any field k: `(k : Type u) [Field k]`. Every extension K/k is `(K : Type u)
  [Field K] [Algebra k K]`. The common universe accommodates any particular pair
  by raising its universe; it imposes no cardinality bound or field restriction.
- Group schemes with the specified identities: `G : Over (Spec (.of k))` and
  `[GrpObj G]`, and likewise H and J. `unitSection` supplies the identity; the
  ordinary group-object laws, not additional hypotheses, fix its value.
- Affine and finite type: `[IsAffine G.left] [LocallyOfFiniteType G.hom]
  [QuasiCompact G.hom]`, repeated for each quantified group.
- The identity tangent vector space is the EXISTING `GrpObj.Lie G`, identified
  with the dependency's `schemeTangentSpace k G.left G.hom x` by the existing
  `lieIdentityTangentEquiv G`, at `x = unitSection G (IsLocalRing.closedPoint k)`.
  The latter restricts the residue-field action along the structural map k → κ(x).
  Its full signature and implementation were read. Thus this uses precisely the
  node's tangent space, through its already established linear identification.
- Finite dimension: the first conjunct is `FiniteDimensional k (Lie G)` for every
  group. H is another value of the same universal quantifier.
- Canonical brackets: the existing `LieRing` and `LieAlgebra k (Lie G)` instances
  in `GroupScheme.Lie.Bracket` are used throughout, without choosing any structures.
  Their bracket is the mixed coefficient of the commutator on dual-number points.
- Homomorphisms: `(f : G ⟶ H) [IsMonHom f]` and `(g : H ⟶ J) [IsMonHom g]`.
  `differential f : Lie G →ₗ⁅k⁆ Lie H` is already k-linear; the second conjunct
  gives its bracket equation and `differential (f ≫ g) =
  (differential g).comp (differential f)`. Quantification over J and g expresses
  the node's “whenever another such homomorphism is given.”
- Tangent-point kernel identification: the third conjunct is `Set.BijOn
  tangentPoint Set.univ (tangentGroup G : Set _)`. `tangentGroup G` is literally
  the kernel of `G(k[ε]) → G(k)`, with the reduction map `fstHom`.
- GL tangent point: the fourth conjunct evaluates the existing inverse matrix
  equivalence at A and says its point, under `homMulEquiv`, is
  `1 + A.map TrivSqZeroExt.inr`. `inr a = ε*a` in dual numbers.
- GL bracket: the same conjunct sends the bracket of the inverse images of A,B
  to `A * B - B * A` by `GeneralLinearGroup.toMatrix`. The explicit
  `@LieEquiv.toLinearEquiv ... LieRing.ofAssociativeRing ...` supplies the exact
  associative commutator structure used by the upstream equivalence, with no
  file-local instances. This was necessary because that structure is deliberately
  not a global instance in Mathlib.
- Representation formula: for `r : GeneralLinearGroup.RationalHom G n`
  `[IsMonHom r]`, the fifth conjunct says the matrix of `r.points _ (tangentPoint x)`
  is `1 + (GeneralLinearGroup.toMatrix n k (differential r x)).map inr`.
  The coefficient is exactly upstream `RationalHom.differential`, definitionally.
- Scalar extension: the final conjunct supplies a family `Φ G :
  K ⊗[k] Lie G ≃ₗ⁅K⁆ Lie ((Over.pullback (Spec.map (algebraMap k K))).obj G)`.
  The target is the actual scheme fibre product; its group structure is the
  canonical image under the monoidal pullback functor, using the standard scoped
  `CategoryTheory.Obj` instance. No arbitrary group or isomorphism is assumed.
- Canonical normalization: the first property of Φ says that the tangent point
  of `Φ G (1 ⊗ x)`, projected by `pullback.fst`, is the point of x precomposed
  with `Spec.map (DualNumber.mapRingHom (algebraMap k K))`. This fixes Φ on pure
  tensors by K-linearity and hence everywhere. Thus the existential asserts the
  canonical isomorphism, not just an unnormalized abstract isomorphism.
- Naturality: the second property equates `Φ H (a ⊗ differential f x)` with
  `differential ((Over.pullback _).map f) (Φ G (a ⊗ x))`. Equality on pure tensors
  is equivalent to equality of the K-linear composites, since they span.
- Tensor bracket: the source `K ⊗[k] Lie G` uses Mathlib's canonical
  scalar-extension Lie structure, whose defining equation is
  `LieAlgebra.ExtendScalars.bracket_tmul`. As requested in the return, its
  universally true formula is no longer repeated as a separate conjunct.
- Entrywise GL extension: the last property evaluates the dual-number ring map
  of the Φ tangent point, composed with the pullback projection, at the existing
  coordinate function `Matrix.GeneralLinearGroup.coord n k i j`. Its value is
  `δ_ij + inr (a * algebraMap k K (A i j))`. The coordinate functions characterize
  GL matrix points, so this states exactly entrywise extension for the canonical
  GL base-change identification, without introducing another comparison map.
- No perfectness, smoothness, reducedness, characteristic, connectedness or
  algebraic-closedness assumption occurs anywhere in the signature.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; group schemes
  and `IsMonHom` follow the recorded `GroupScheme.Defs` interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`:
  `schemeTangentSpace`, its additive and module instances, and `schemeTangentMap`.
  Imported for the tangent-space comparison through the plain proof import
  `GroupScheme.LieIdentityTangentEquiv`, whose existing bridge
  `lieIdentityTangentEquiv` justifies using the group-specific tangent-space model.
- `Mathlib.Algebra.Lie.Basic`: `LieRing`, `LieAlgebra`, `LieHom`, `LieEquiv`.
- `Mathlib.Algebra.DualNumber`: `DualNumber`, `DualNumber.eps`; the actual ring
  and reduction used in `tangentGroup` are these, not a second quotient model.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`: the dependency module is imported;
  its docstring explicitly delegates GL and its points to the upstream
  `GeneralLinearGroup`, `homMulEquiv` constructions used here. Its recorded primary
  declaration is specialLinear, but its public GL import supplies exactly the GL
  part needed, so no dependency-record repair is necessary.
- `def-wf-lie-algebra-derivation`, now explicitly included in `stmt_deps`, owns
  the following existing group-specific declarations through its `lean` record
  and `lean_audit.slopmaster2.decls`. Its primary recorded module is
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` and its declaration
  is `AlgebraicGeometry.GrpObj.lieEquivTangent`. The published definitions apply
  over an arbitrary field, as used here; no characteristic-zero or algebraic
  closedness restriction is imposed by these declarations.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.{Basic,Ring,Bracket,Differential}`:
  `Lie`, `unitSection`, `tangentPoint`, `differential`; and
  `GroupScheme.GeneralLinear.Lie`: `lieAlgebraEquivMatrix`, `toMatrix`,
  `RationalHom.points`, `RationalHom.differential`. Full signatures/docstrings read.
- `Mathlib.Algebra.Lie.BaseChange`: the canonical tensor Lie instances.
- Proof imports: `Sheaf.RingTheory.BialgebraDistributionTangentCalculus`
  (`finiteOrderConvolutionAndTangentDerivations`, read in full),
  `Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`
  (`affine_finiteType_algebra_of_field`), `Mathlib.RingTheory.Flat.Basic` and
  `Mathlib.LinearAlgebra.TensorProduct.RightExactness`. Other recorded Mathlib
  proof dependencies (Spec, affine fibre products, basis/free modules) are already
  available through the public dependency imports. The eight-step proof is included
  in the theorem docstring, including the exact tensor normalization.

Edge cases: zero tangent dimension, the trivial group, n = 0 (empty matrices),
n = 1, positive characteristic including two, nonperfect fields, nonreduced
finite groups such as α_p and μ_p, and K = k. Nothing requires an embedding into
GL or a faithful representation, so non-smooth cases are retained. Empty schemes
cannot be group schemes over a field because the unit section exists. For K = k,
the tangent-point normalization forces the usual unit tensor identification.

Searches:

- `msearch.py ... leanfinder 'Lie algebra tangent space affine group scheme scalar
  extension field canonical bracket'`: eight manifold GroupLieAlgebra results,
  requiring a nontrivially normed field; no scheme or field-extension theorem.
- `msearch.py ... loogle '"LieAlgebra" "TensorProduct"'`: malformed pattern,
  zero hits; reran with `LieAlgebra.ExtendScalars.map`, yielding `map` and
  `map_apply_tmul` in Mathlib.Algebra.Lie.BaseChange. These only extend a given Lie
  algebra map and do not compare tangent Lie algebras of group schemes.
- `msearch.py ... grep 'Lie.*baseChange|baseChange.*Lie|lieAlgebraEquivMatrix'
  Algebra`: 15 abstract Lie-base-change references, no group-scheme comparison.
- `rg` in Mathlib group/affine and Lie files found the canonical pullback group
  structure and tensor bracket, used here. `rg` in WeilConjectures/GroupScheme
  found all existing Lie constructions and matrix formulas, used here; searches
  for baseChange/Lie and scalar extension found no matching full statement.
- `rg` in `lean/Sheaf` and `lean/WeilConjectures` for the item id and proposed
  declaration name found no existing declaration; concept searches found related
  tangent/cotangent comparison modules, not scalar-extension naturality.
- Read Milne locally with `pdftotext`: 10.6--10.7 kernel and matrix identification,
  10.11 tangent point, 10.19 scalar extension and equation (59), and 10.23 bracket.

No statement dispute, correction, new node or dependency repair is needed.

## Second reading by ND

This is the dispatcher's single-worker workflow: no other agent was started.
The maintainer performs the independent reading after delivery. I reread the
node and final signature against the clause list above. The initial elaboration
required making the pre-existing associative matrix Lie structure explicit in
`LieEquiv.toLinearEquiv`; this fixed an instance inference failure without changing
any mathematical statement or introducing a local instance. I checked that Φ is
normalized, its naturality uses the actual pullback homomorphism, its GL formula
uses actual coordinate pullback, and none of the non-smooth cases is excluded.
The only postponed proof is the displayed node theorem.

## Repair of return 25c0c580cdba

H2: added `def-wf-lie-algebra-derivation` to `stmt_deps`, retaining all seven
original dependencies. Read its current `existing: true` record in
`GroupScheme.Lie.Bracket` and its audit declarations: it owns `GrpObj.Lie`, the
canonical Lie instances, `tangentGroup`, `lieAlgebraEquivMatrix`, `RationalHom`
and its differential. The earlier appeal to the general scheme tangent-space
node did not account for these concrete objects. This is a dependency addition
explicitly requested by the maintainer, not a change to the mathematical statement.
The sandbox node was rebased from the current read-only main node before applying
this addition and the Lean binding; the comparison showed that the earlier
sandbox differed from current main only in `lean`.

Also applied both optional cleanups: removed the separate tensor-bracket conjunct
because it restated `ExtendScalars.bracket_tmul`, while retaining that exact
canonical tensor bracket in the Lie-equivalence source; changed the unused public
`LieIdentityTangentEquiv` import to a plain import for the proof's tangent-space
comparison. Updated `lean.statement` verbatim. No definitions, canonical
normalizations, naturality equations, matrix formulas or field cases changed.
The parallel returned Q44 delivery is not used or modified by this packet.
