## Worker report

Item: lem-sfb-dg-qis-restriction-equivalence. Group Q79, stage 2, 2026-10-24.
Module: `Sheaf.CategoryTheory.DgQuasiIsoRestrictionEquivalence`.
Main declaration: `CategoryTheory.DgAlgebra.quasiIso_restriction_equivalence`.

The source is Stacks `literature/stacks-project/dga.tex`, Tag 09S6,
`lemma-qis-equivalence`, read with its proof and Example 0BYX. It asserts that
left derived tensor along a quasi-isomorphism is an equivalence with inverse
restriction. The DAG's specialization is over Z; it also spells out the
adjunction and exactness. Its mathematical statement and accepted proof split
are unchanged. The two already-landed definition nodes
`def-sfb-dg-derived-category` and `def-sfb-dg-bimodule-models` are added to
`stmt_deps` to name the actual interfaces used.

The following matches every hypothesis and clause:

- Size convention: explicit `universe u`; `Algebra.{u}` uses cochain complexes
  of `ModuleCat.{u} (ULift.{u} ℤ)`. The larger category universe of the actual
  Gabriel--Zisman localization is inferred from this recorded construction.
  No independent small morphism universe or size equality is imposed.
- Associative unital integer-graded DG algebras over Z: `(A B : Algebra.{u})`,
  the recorded monoid-object definition. Its chain multiplication encodes
  the signed Leibniz rule; its complexes encode square-zero differentials.
  These are not commutative algebras and need not be bounded or countable.
- Right DG modules and their differential rule: `RightModule A` and
  `RightModule B`, the existing module objects in the reversed tensor category.
- The specified derived categories and cone triangles: `Derived A`, `Derived B`
  and `[DerivedStructure A] [DerivedStructure B]`. These are the actual
  localizations and the existing standard structural interface with
  `ShiftComparison`, `ConeComparison`, and `distinguished_iff`. No equivalence,
  flatness, finite-cell condition or generation assumption is added.
- The degree-preserving unital multiplicative differential-compatible map:
  `(φ : A ⟶ B)` in the monoid-object category, whose `φ.hom` is a chain map.
- All induced cohomology maps are isomorphisms: `(hφ : QuasiIso φ.hom)`.
  This is Mathlib's cohomology-based predicate in every integer degree.
- Restriction keeps the complex and every underlying map, and lets a act
  through φ: the existential `G` has `r : ScalarRestrictionModel φ G`.
  `r.underlyingIso` is a natural isomorphism of the actual underlying-complex
  functors. Its action square forces exactly m*a = m*φ(a), not a freely
  supplied action. This coordinate model determines restriction up to
  natural isomorphism. It is structural data in the conclusion, not a
  hypothesis or a choice from an unspecified existence assertion.
- Restriction induces the required functor on the localizations: `R` with
  `ρ : Q B ⋙ R ≅ G ⋙ Q A`. By the localization universal property, such
  a lift is unique up to the corresponding unique natural isomorphism.
  Preservation of quasi-isomorphisms follows from the unchanged complex;
  it is not assumed separately.
- Exact restriction: `_sR : R.CommShift ℤ` and `R.IsTriangulated` give
  compatible shifts and preservation of distinguished mapping-cone triangles.
  The last conjunct pins the degree-one shift comparison through `ρ` and
  the unchanged underlying-complex shift; its first equality uses
  `r.underlyingIso` to specify the ordinary restriction comparison.
- The bimodule for tensor is B with a*b = φ(a)b and its usual right action:
  `N` with `_b : AlgebraMapBimoduleModel φ N`. Its complex is explicitly
  isomorphic to `B.X`, and both chain actions are fixed by multiplication
  and φ in `left_action` and `right_action`. No arbitrary bimodule is substituted.
- The inverse is the specified derived tensor: `t : BalancedTensorModel N F`
  fixes ordinary tensor by its balanced coequalizer and induced right action;
  `α : Q A ⋙ L ⟶ F ⋙ Q B` and `L.IsRightKanExtension α` specify its
  total left derived functor. The right Kan direction is precisely the
  direction of a total left derived comparison, as in the recorded
  bimodule-derived-adjunction theorem.
- Its exactness and canonical shift comparison: `_sL : L.CommShift ℤ`,
  `L.IsTriangulated`, and the penultimate conjunct with `IsTensorShift`.
  The latter pins shifts to the sign-free shift on the tensor's first factor.
- It is left adjoint to restriction: `(adj : L ⊣ R)`; its unit and counit
  include the adjunction triangle identities by the Mathlib definition.
- Unit id → RL and counit LR → id are natural isomorphisms:
  `IsIso adj.unit ∧ IsIso adj.counit`.
- Both functors are equivalences: `L.IsEquivalence ∧ R.IsEquivalence`.
  Together with the adjunction's invertible unit and counit, these assert
  the exact quasi-inverse conclusion for these very functors.
- Shift compatibility of unit and counit: `adj.CommShift ℤ`. Degree-one
  normalization suffices to determine the coherent integer shift structure;
  no unsupported coherence axiom on arbitrary higher-degree
  `DerivedStructure.shiftIso` fields is silently assumed. This follows the
  reviewed degree-one interface of the bimodule adjunction dependency.

Dependencies read and used:

- `def-weil-size-convention` is explicitly recorded as a metatheoretic
  convention, without a Lean object or module; explicit universes implement it.
- `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`:
  `CategoryTheory.DgAlgebra.Algebra`, `RightModule`, `underlying`, `Derived`, `Q`,
  `ShiftComparison`, and `DerivedStructure` (including `shiftIso`).
- `Sheaf.CategoryTheory.DgBimoduleModels`:
  `rightAction`, `BalancedTensorModel`, and `IsTensorShift`, together with
  Mathlib's actual `CategoryTheory.Bimod`. Full node statements, records,
  declaration signatures and docstrings were read.
- `Mathlib.CategoryTheory.Triangulated.Adjunction` supplies Mathlib's exact
  functors and shift-compatible adjunction; Kan extension notions are from
  `Mathlib.CategoryTheory.Functor.KanExtension.Basic`, already public through
  the recorded models module.
- Plain proof import `Sheaf.CategoryTheory.DgBimoduleDerivedAdjunction`:
  `CategoryTheory.DgAlgebra.bimodule_derived_tensor_hom_adjunction`, with its
  full signature, docstring and review note read. This is the only recorded
  proof dependency with a Lean module at inspection. The finite-cell compactness,
  free-module Hom/cohomology, compact-bimodule full-faithfulness and exact-adjoint
  zero-kernel nodes have no Lean attachment; their names and roles remain in
  the complete five-step proof docstring, with no fabricated declaration.

The two small structures are helpers for the canonical scalar-map construction
already in this node, authorized as owning-module helpers by brief-stage2 §1.
They introduce no new independent mathematical notion. All their fields are
explicit mathematical data and laws. They do not construct data with `sorry`.
Only the named main theorem is postponed, and the matching DAG node and its
complete proof plan accompany it. No additional definition node, dependency
repair, statement correction, or disputed statement is needed.

Edge cases checked mathematically before writing: φ = id gives the identity
restriction and the usual tensor-unit equivalence; strict DG algebra isomorphisms
are covered; the zero DG algebra and acyclic algebras are permitted without a
nontriviality assumption; all integer shifts, including negative and zero shifts,
are covered by `CommShift ℤ`; zero modules are permitted; ordinary rings concentrated
in degree zero give the usual restriction along a ring isomorphism when φ is a
quasi-isomorphism. No flatness of B over A, boundedness, characteristic, commutativity
or countability restriction occurs. A map Z → Z/2 in degree zero fails the
quasi-isomorphism hypothesis, correctly preventing the false unrestricted conclusion.
The restriction action has no extra Koszul sign, matching the node's right-module
convention. The shift squares were checked for composability from their domains
and codomains, including the orientation of `ρ` and `α`.

Searches (all via the prescribed tooling or read-only repository searches):

- `msearch.py ... leanfinder "A quasi-isomorphism of differential graded algebras
  induces an equivalence on derived categories by restriction of scalars"`:
  8 results, headed by `DerivedCategory.isIso_Q_map_iff_quasiIso`; none is a
  restriction equivalence of DG module categories.
- `msearch.py ... loogle "DGAlgebra, DGModule"`: 0 results, unknown DGAlgebra.
- `msearch.py ... grep "DGAlgebra|DGModule|DifferentialGraded"`: 0 results.
- `msearch.py ... leansearch "Restriction along a quasi-isomorphism of differential
  graded algebras is an equivalence of derived categories"`: 8 ordinary derived
  localization/cohomology results; no DG scalar restriction theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for DGAlgebra, DGModule,
  DgAlgebra, DgModule, differential graded, and restriction/equivalence wording:
  located and reused the actual DgAlgebraDerivedCategory and DgBimoduleModels
  interfaces. Ordinary ring restriction results and small DG-category results
  have different objects and do not state this node.
- The exact node id in `lean/WeilConjectures`: no result.
- Proposed helper and theorem names in both source roots and
  `dag/lean_names_upstream.json`: no existing declaration.
- Read-only DAG search and `tools/blueprint_refs.py search 'restriction of scalars'`:
  existing ordinary/commutative sheaf coefficient-change nodes do not define
  restriction for this associative DG algebra setting. The existing DG definition
  nodes supply precisely the interfaces reused above.

Validation: prescribed `scompile.py` compiled the initial module in module mode
both as sandbox and as library module (19.1 s and 9.0 s), with no diagnostics.
The final delivery is additionally checked by the prescribed server dry run.

## Second reading by Q79

A second pass reopened the node, full Lean file, recorded definitions and Tag 09S6.
The worker was explicitly instructed not to start other agents, so this section
records a worker self-check; the maintainer supplies the independent review.
The comparison above was checked against the actual signature, rather than only
its name. In particular, it verified the following possible mismatches:
restriction cannot be an arbitrary functor (the natural underlying identification
and action equation fix it); tensor cannot use an arbitrary bimodule (both actions
and its complex are fixed); the derived tensor must be universal (the right Kan
extension clause is present); an objectwise isomorphism is insufficient (the actual
adjunction unit/counit are isomorphisms); and arbitrary shifts must not acquire
incoherent extra constraints (normalization is only at degree one, followed by
coherent `CommShift ℤ`). All these conditions occur in the delivered signature.
The explicit direct import of the landed derived-category definition module was
added during this pass. No mathematical mismatch or statement correction was found.
