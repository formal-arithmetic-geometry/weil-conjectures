## Worker report

The module `Sheaf.CategoryTheory.InfinityCoreCylinderRestriction` states
`SSet.Enhanced.precompositionCylinder_core_restriction`, with its sole proof `sorry`.
It adds no definitions and changes only the item's `lean` record. The existing dependency
interfaces suffice, without statement correction or extra nodes.

Sources read: [Kerodon Theorem the project server](https://kerodon.net/tag/01DK), the pointwise
criterion for a natural transformation to be an equivalence, and
[Construction the project server](https://kerodon.net/tag/0060), the internal functor simplicial set
and evaluation. The node's five-step proof is included in the declaration docstring,
including the explicit mixed-edge square and triangle and the homotopy-category
criterion used to compose equivalences.

Hypotheses and clauses, matched to Lean:

- Small quasicategories `K` and `C` are `(K C : SSet.{u}) [Quasicategory K]
  [Quasicategory C]`. The universe `u` is explicitly declared and arbitrary, following
  `def-cbc-enhanced-diagrams-cones` and its fixed-universe internal hom. No dimension,
  finiteness, nonemptiness, or vertex-distinctness assumption is introduced.
- The simplicial homotopy is `(η : K ⊗ Δ[1] ⟶ K)`. The monoidal product of simplicial
  sets is the degreewise product from Mathlib's `SSet.Monoidal`.
- The track condition is `hη : ∀ k : K _⦋0⦌, IsEquivalenceEdge K
  (η.app _ (K.σ 0 k, stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)))`. Here `K.σ 0 k` is the
  constant edge at `k` and `stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)` is the identity edge
  of the interval. Their image is exactly the track at `k`, with its orientation from
  zero to one. It does not assume that all edges of `K` are equivalences.
- The functor simplicial set is the existing `(ihom K).obj C`; its core is the existing
  `core ((ihom K).obj C)`. The cylinder is the dependency's explicit
  `precompositionCylinder η C`, without an arbitrary map parameter.
- “Every edge of the core times the interval is sent to an equivalence” is the first
  conjunct: `∀ e : ((core ((ihom K).obj C)).toSSet ⊗ Δ[1]) _⦋1⦌, ...` with
  `IsEquivalenceEdge ((ihom K).obj C)` applied to the image under
  `((core ((ihom K).obj C)).ι ▷ Δ[1]) ≫ precompositionCylinder η C`.
  This quantifier includes all three parameter edges and in particular the mixed case.
- “Restricts to a simplicial homotopy” is the second conjunct's existential
  `H : (core ((ihom K).obj C)).toSSet ⊗ Δ[1] ⟶
  (core ((ihom K).obj C)).toSSet`, together with
  `H ≫ (core ((ihom K).obj C)).ι =
  ((core ((ihom K).obj C)).ι ▷ Δ[1]) ≫ precompositionCylinder η C`.
  Equality after the monic core inclusion forces `H` to be the restriction of the
  specified cylinder, rather than some unrelated homotopy.
- “Between the induced precomposition maps on cores” is expressed by the last two
  equations. At zero, `SSet.ι₀ ≫ H ≫ core.ι` equals
  `core.ι ≫ (MonoidalClosed.pre (SSet.ι₀ ≫ η)).app C`; at one the equation uses
  `ι₁` instead. These formulas specify exactly the induced precomposition maps after
  their core inclusions. Since the inclusion is monic, the equations determine the
  endpoint maps on the core. The endpoint maps of `η` are used directly, so no extra
  endpoint maps or endpoint hypotheses are required.

Dependency declarations read in full and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsEquivalenceEdge`, `SSet.Enhanced.core` (the statement), and
  `SSet.Enhanced.diagramVertex`, `SSet.Enhanced.evaluation` (pointwise proof interface).
  Its Mathlib imports give `Quasicategory`, `(ihom K).obj C`, `SSet.ι₀`, and `SSet.ι₁`.
- `Sheaf.CategoryTheory.InfinityPrecompositionCylinder`:
  `SSet.Enhanced.precompositionCylinder` and
  `SSet.Enhanced.precompositionCylinder_endpoints_natural`. The actual curry/evaluation
  definition and complete endpoint/naturality signature were read.
- Proof-only import `Sheaf.CategoryTheory.PointwiseEquivalences`:
  `SSet.Enhanced.pointwise_equivalences`, read with its endpoint equations and proof
  docstring, supplies the componentwise equivalence criterion.
- Proof-only import `Sheaf.AlgebraicTopology.HomotopyCategoryTriangleCalculus`:
  `SSet.homotopyCategory_triangle_calculus`, read with its edge-representative and
  exact-boundary triangle clauses and proof docstring, supplies the triangle calculus.

Edge cases checked mathematically before writing: empty `K` has no track conditions;
its functor simplicial set is terminal, so the conclusion remains correct. Empty `C`
and nonempty `K` can give an empty functor simplicial set; the edge clause is vacuous
and the restricted map has empty domain. Empty `K` and empty `C` together still give
one diagram, not an empty functor simplicial set. Identity and constant parameter
edges are covered by the edge quantifier, as are degenerate edges. No assumption
excludes the identity homotopy, repeated vertices, or a discrete quasicategory. The
track hypothesis is substantive: a general homotopy can have noninvertible tracks.
All expressions live in the same arbitrary input universe as the dependency interfaces.

Searches for an existing statement (all on 2026-10-17):

- `msearch.py ... leanfinder`, query “A whiskering cylinder on an internal functor
  simplicial set restricts to its core when the homotopy has equivalence tracks”:
  eight hits on ordinary hypercover cylinders and model-category cylinders; no match.
- `msearch.py ... loogle`, query `"SSet", "core"`: twelve hits on truncated skeleta
  and strict Segal cores; no equivalence-edge core cylinder theorem.
- `msearch.py ... leansearch`, query “A simplicial homotopy acting by precomposition
  restricts to a homotopy of functor cores when all its tracks are equivalences”:
  eight hits on relative simplicial-map homotopy precomposition, model-category
  homotopies, and colimits; none is the internal-functor core restriction.
- `msearch.py ... grep`, query
  `core.*cylinder|cylinder.*core|precompositionCylinder`, subdirectory
  `AlgebraicTopology`: zero Mathlib hits.
- `rg` with `core.*[Cc]ylinder|[Cc]ylinder.*core|precompositionCylinder` in the
  upstream `WeilConjectures` and side `lean/Sheaf` trees: the side cylinder dependency
  and a proof-plan mention in `MarkedFlatCategoricalEquivalenceTest`; no statement
  already formalizes this node. The upstream search has no match.
- `grep -rn` for the exact node id in upstream `WeilConjectures`: no match.
- `rg` for the proposed declaration `precompositionCylinder_core_restriction` in
  `dag/lean_names_upstream.json`, Mathlib, upstream, and side sources: no collision.

Validation: `scompile.py Q04 lem-coef-infinity-core-cylinder-restriction` compiled the
file in both sandbox and module contexts, including its required dependency overlay,
with no errors or warnings. `autoImplicit` is explicitly disabled; the sole universe
and all variables are explicitly bound. No lines exceed 100 characters. No node fault
or disputed statement was found.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
