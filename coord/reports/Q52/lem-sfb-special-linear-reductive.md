## Worker report

The module `Sheaf.AlgebraicGeometry.SpecialLinearReductive` states
`AlgebraicGeometry.LinearGroupSchemes.specialLinear_reductive`, with `sorry` as its whole
proof. The two real helper definitions `specialLinearBasis` and `specialLinearPointsOn`
identify the already recorded coordinate scheme with the determinant-one automorphism
functor of the arbitrary vector space in the node. They introduce no second group scheme,
no second unipotence predicate, and no second reductivity predicate.

Clause-by-clause correspondence:

- The field k is `(k : Type u) [Field k]`; the arbitrary vector space is `(E : Type v)
  [AddCommGroup E] [Module k E] [FiniteDimensional k E]`. The universes u and v are
  independent. The integer r is encoded by its determined value `Module.finrank k E`;
  `(hr : 1 ≤ Module.finrank k E)` is exactly r >= 1 and dim(E) = r. This does not fix
  a basis as a hypothesis or restrict E to a coordinate vector space.
- The group scheme G = SL(E) is the recorded
  `specialLinear k (Module.finrank k E)`, with `specialGroup` as its group structure,
  bundled by `Grp.mk`. Its coordinate ring is exactly the quotient by det - 1 from
  def-sc-general-linear-group. The helper `specialLinearPointsOn` is the actual
  multiplicative equivalence from its R-points to
  `SpecialLinearGroup R (R ⊗[k] E)`. It is constructed by composing `specialPoints`
  with `Matrix.SpecialLinearGroup.toLin_equiv` for the scalar extension of one
  chosen basis of E. This is not a choice from an uncharacterized existence theorem.
  Mathlib writes base extension as R tensor E; tensor symmetry canonically identifies
  this with E tensor R in the node.
- Representing the displayed functor is rendered by that explicit group equivalence
  and the final universally quantified equation. For every commutative k-algebra map
  φ:R -> S and every point x, the equation evaluates the scalar-change square on
  `1 ⊗ v` for every v:E. These vectors generate as an S-module, so it expresses
  precisely naturality of the point equivalence. `TensorProduct.map φ.toLinearMap
  LinearMap.id` is the canonical coefficient-change map, not a variable map.
- Smoothness, affineness and finite type occur in the first conjunct
  `ReductiveTorusCentralizer.IsReductive (Grp.mk ...)`. Its body contains
  `Smooth G.X.hom` and `SolvableGroupStructure.IsAlgebraic G`; the latter is exactly
  `IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom`.
- Geometric connectedness is the `ConnectedSpace` clause of the same predicate,
  on the underlying scheme of `MultiplicativeType.baseChange` to `AlgebraicClosure k`.
  `ConnectedSpace` includes nonemptiness. Thus no empty-space convention is changed.
- Reductivity is its universal quantification over bundled group schemes U over
  `AlgebraicClosure k` and homomorphisms j:U -> G over that field, with
  `IsClosedSubgroupScheme j.hom.hom`, `IsNormalSubgroupScheme j.hom.hom`,
  `ConnectedSpace U.X.left`, and `SolvableGroupStructure.IsUnipotent U`.
  The latter gives smoothness and a faithful finite-dimensional closed matrix
  representation, with `(matrix - 1)^N = 0` for N > 0 at every geometric point.
  Its `IsAlgebraic U` premise is automatic for a closed subgroup of this affine
  finite-type G; it does not restrict the subgroups in the node. Its conclusion
  `Nonempty (U ≅ Grp.trivial _)` is triviality as a group scheme. A homomorphism
  from the trivial group scheme necessarily has identity image, so this is also
  triviality of the subgroup, including its embedding.
- There is no characteristic, perfectness, or algebraic-closedness hypothesis on k.
  Algebraic closure appears only in the conclusion's geometric tests.

Dependency declarations read and used:

- def-weil-field: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- def-sc-general-linear-group: `Sheaf.AlgebraicGeometry.LinearGroupSchemes`,
  `LinearGroupSchemes.specialLinear`, `specialGroup`, `Index`, and `specialPoints`.
  The full module was read, including its quotient, fixed Hopf maps, unique group
  structure and natural point equivalence. The current blueprint definition was
  read in `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/`.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- def-sc-group-scheme: `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`
  and `CategoryTheory.Grp`; bundled with the recorded specialGroup instance.
- def-weil-connected-scheme: `Mathlib.Topology.Connected.Basic`, `ConnectedSpace`.
- def-sc-group-scheme-subgroup:
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` (all full signatures and
  docstrings read). Their tests are on all commutative k-algebras, not just fields.
- Added already-landed statement dependency
  def-sfb-reductive-torus-centralizer-terminology:
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`,
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`. Its complete body and
  dependency node were read; it uses the already recorded `IsAlgebraic`,
  `IsUnipotent`, `MultiplicativeType.baseChange`, and Mathlib `AlgebraicClosure`.
- Mathlib's `Module.finBasis`, `Module.Basis.reindex`, `Module.Basis.baseChange`,
  `SpecialLinearGroup`, `Matrix.SpecialLinearGroup.toLin_equiv` and
  `TensorProduct.map` give the point identification and coefficient-change equation.

The proof docstring reproduces all eight steps of the accepted split, including
scheme-theoretic triviality via reduced finite-type affine vanishing. Already stated
proof prerequisites are imported privately: finite presentation, pullbackSpecIso,
tensor pushout maps, Smooth.geometricallyReduced, and the affine Nullstellensatz.
The general-linear reductivity and unipotent rational fixed-vector nodes have no
recorded Lean declaration at this stage; no speculative import is used for them.
The quotient/polynomial, affine-spectrum, subgroup and field definitions are available
through the public statement imports. No import cycle was introduced.

Source checked directly in the local Milne PDF: Section 2.42 (printed p.53),
Lemma 19.16, Corollary 19.18 and Example 19.19 (printed p.401). The proof is unchanged.
No statement correction, new independent notion, or dependency repair is needed.

Edge cases checked before writing and again against the finished file:

- r = 1 gives the trivial group; positivity includes it. r = 0 is outside the node,
  so hr excludes precisely the missing case.
- Characteristic two and positive characteristic dividing r are included. No
  determinant division by r, characteristic, or transvection coefficient is assumed.
- Nonreduced finite subgroups such as mu_p do not invalidate reductivity: smoothness
  of the tested U is required, and the conclusion is scheme-level triviality.
- The trivial U is allowed, and the faithful representation dimension may be zero
  only for the trivial group; this does not remove it from the test.
- Empty schemes are not declared connected; identity sections provide nonemptiness.
- Nonreduced test algebras and the zero k-algebra are allowed in the point equivalence
  and its naturality. No field or reducedness hypothesis was added to R or S.
- E may live in a universe independent of k. Its finite basis has the lifted index
  type already used by the coordinate-scheme dependency. Algebra and matrix test
  universes are the same as the recorded group-scheme API, never independently lower.

Searches for existing statements and notions:

- `msearch.py`, leanfinder: "The special linear group scheme is smooth geometrically
  connected affine of finite type and reductive". Eight hits: abstract
  `SpecialLinearGroup`, `Matrix.SpecialLinearGroup`, their instances and PSL;
  none asserts the algebraic-geometric properties.
- `msearch.py`, loogle: `"SpecialLinearGroup", "reductive"`. Zero hits.
- `msearch.py`, grep:
  `SpecialLinear.*[Rr]educt|[Rr]educt.*SpecialLinear|[Uu]nipotent|IsReductive`.
  Eight hits, abstract unipotent biproduct matrices and the PSL line stabilizer;
  none states reductivity of the group scheme.
- `msearch.py`, leansearch: "The special linear group scheme over any field is
  reductive". Eight hits, abstract SL definitions and basic instances only.
- Project `rg` in both WeilConjectures and Sheaf for special/reductive/unipotent:
  found the existing `SolvableGroupStructure.IsUnipotent` and
  `ReductiveTorusCentralizer.IsReductive`; both are reused. No SL reductivity theorem.
  Exact item-id search of WeilConjectures returned no match.
- Exact-name searches in Mathlib, WeilConjectures, Sheaf and upstream declaration
  records for specialLinear_reductive, specialLinearBasis and specialLinearPointsOn
  returned no conflicts. DAG searches located the existing terminology nodes; the
  already-landed reductivity node is added to stmt_deps, without copying or editing it.

Validation: the complete delivered module passed `scompile.py` in both sandbox and
library module modes, with no errors or warnings. The statement and both helper
constructions have explicitly bound variables and universes; autoImplicit is disabled.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
