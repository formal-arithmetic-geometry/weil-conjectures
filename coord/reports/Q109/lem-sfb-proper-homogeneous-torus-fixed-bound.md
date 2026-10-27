## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ProperHomogeneousTorusFixedBound`
states `AlgebraicGeometry.proper_homogeneous_torus_fixed_bound`, with its sole proof
`sorry`. No definitions, helper theorems or new nodes are introduced. The item's
statement is unchanged. Its `stmt_deps` gains the already landed
`def-sfb-tori-multiplicative-type`, whose split torus is needed to express the
explicit rank-r torus hypothesis without a second definition.

Source read: Milne, Algebraic Groups (2017), printed pp.410--411 (PDF pp.422--423),
Proposition 20.11, its proof, Corollary 20.12 and its proof. The corollary is exactly
the dimension-plus-one estimate for a torus in a smooth connected group with
complete homogeneous quotient. The module docstring contains all seven DAG proof
steps, including the ambient-dimension induction, nonreduced hyperplane intersection,
polynomial affine-chart limit, and the arbitrary-algebra fixing condition.

Hypothesis-by-hypothesis and clause-by-clause translation:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The F-group schemes are `G H : Over (Spec (.of F))` with `[GrpObj G]` and
  `[GrpObj H]`. Affineness, smoothness, connectedness and finite type of G are
  `[IsAffine G.left] [Smooth G.hom] [ConnectedSpace G.left]`, and
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, respectively.
- The closed subgroup is `iH : H ⟶ G` with `[IsClosedSubgroupScheme iH]`.
  No smoothness, connectedness or normality of H is assumed. Affineness and
  finite type of H follow from its closed immersion into this finite-type affine G;
  they are not imposed as additional assumptions.
- The scheme X and its canonical quotient map are `X : Over (Spec (.of F))`
  and `q : G ⟶ X`. Right cosets are the presheaf coequalizer of `fst G H` and
  `lift (fst G H) (snd G H ≫ iH) ≫ μ[G]`. The arrow `ηq`, the generator equation
  `hηq`, and the universal bijection `hquot` express that the represented presheaf
  is its fppf sheafification, exactly as the recorded quotient dependency does.
  Representable presheaves are fppf sheaves; no arbitrary quotient map or pointwise
  orbit surrogate replaces this universal property.
- Properness is `[IsProper X.hom]`. Its parents give separatedness and locally
  finite type; universal closedness gives quasi-compactness, so the node's separated
  finite-type requirement on X is included without redundant hypotheses.
- The torus is `S : Grp (Over (Spec (.of F)))`, with closed subgroup inclusion
  `iS : S.X ⟶ G` and `[IsClosedSubgroupScheme iS]`. The hypothesis `hsplit` says
  `∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r)`. The isomorphism is
  in group schemes, not merely schemes; this is exactly the stated product of G_m.
- The left action is `[ModObj S.X X]`. Its equation `haction` says that acting on
  `q(g)` by s gives `q(iS(s)g)`, as an equality of morphisms S × G → X. Thus the
  action is the specified induced action, not an unrestricted action on X.
- `∃ (d : ℕ) ... , topologicalKrullDim X.left = (d : WithBot ℕ∞) ∧ ...`
  records the actual dimension as a finite integer. It does not truncate infinite
  dimensions or use a natural-cardinality convention for an infinite fixed set.
- `x : Fin (d + 1) → (𝟙_ (Over (Spec (.of F))) ⟶ X)` and `Function.Injective x`
  give at least d+1 distinct F-rational points. No finiteness instance on the whole
  fixed set is used.
- For every j and every `A : Type u` with `[CommRing A] [Algebra F A]`, and every
  `s : StandardGroupSchemes.affine F A ⟶ S.X`, the final equality says
  `s • x_A = x_A`, where `x_A = toUnit ... ≫ x j`. It includes nonreduced and
  zero algebras and is precisely scheme-theoretic fixedness.
- Rank zero is allowed by `r : ℕ`, and G=H is allowed throughout. No maximality
  condition on S is present.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraic-closure
  node's recorded match explicitly names this algebraically-closed predicate).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and `Grp`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme` (including its subgroup and
  multiplication compatibility and its closed-immersion parent).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry`:
  `AlgebraicGeometry.exists_homogeneous_fppf_quotient` and
  `AlgebraicGeometry.exists_orbit_stabilizer_quotient_iso`. Both signatures and
  docstrings were read. The quotient's pointwise coequalizer/sheafification
  presentation is used directly in the statement; no private quotient definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `AlgebraicGeometry.StandardGroupSchemes.affine`, `.multiplicative`, and
  `.multiplicativeGroup` (the Laurent Hopf group law).
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`; its recursive construction
  uses the preceding G_m, with the tensor unit in rank zero.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: `CategoryTheory.Hom.smul`
  supplies the actual morphism-valued action, given by pairing then the action map.

All stated proof dependencies are imported. The currently unstated Chevalley line
stabilizer, Hilbert-polynomial dimension, split-torus weight decomposition and
projective fixed-weight-scheme nodes have no module to import. These omissions do
not affect the statement interface or create substitute assumptions.

Edge cases checked against the source and types: G=H gives d=0 and one rational
point; r=0 gives the trivial torus and all points are fixed; a positive-dimensional
fixed locus is allowed because an injective finite list, not `Nat.card`, expresses
the bound; H may be nonreduced in positive characteristic; A may be nonreduced or
the zero ring; no independent algebra universe makes the quantifier vacuous.
There is no statement dispute or correction.

Searches run (2026-10-24):

- `msearch.py ... leanfinder "A torus acting on a proper homogeneous scheme has
  at least dimension plus one fixed points"`: successful, eight results, concerning
  fixed subfields and abstract group actions; no scheme-theoretic estimate.
- `msearch.py ... loogle '"fixedPoints"'`: successful, twelve results, principally
  `MulAction.fixedPoints` and its additive variants and fixed subgroups; no match.
- `msearch.py ... grep 'torus|Torus|fixedPoints' AlgebraicGeometry`: successful,
  zero Mathlib hits.
- `msearch.py ... leansearch "Torus fixed points on a proper homogeneous space
  have cardinality greater than its dimension"`: successful, eight abstract
  group-action results; no algebraic-geometric dimension estimate.
- `rg` in `lean/WeilConjectures` for the item id, torus/fixed-point terminology
  and the proposed declaration: no statement of this estimate; fixed-field and
  discrete-representation results have different objects.
- `rg` in `lean/Sheaf` and `lean/Sheaf/AlgebraicGeometry/GroupScheme` for torus,
  fixed-point and homogeneous-quotient terminology found the recorded quotient
  module and the already landed split-torus definition, which are reused.
  `rg 'def splitTorus'` located `ToriMultiplicativeType.lean` and a separate
  ring-base interface; the field-base declaration is the one used here.
- `rg -l 'Sheaf.AlgebraicGeometry.ToriMultiplicativeType' dag/nodes` identified
  its owning node `def-sfb-tori-multiplicative-type`. No new node was needed.
- The proposed declaration name was searched in Mathlib, WeilConjectures and
  Sheaf before writing: no collision.

Validation: `scompile.py Q109 lem-sfb-proper-homogeneous-torus-fixed-bound` compiled
this file in sandbox and library module modes successfully, without errors or
unexpected warnings. Both `autoImplicit` and `relaxedAutoImplicit` are false.

## Second reading by Q109

A separate rereading pass by the same dispatcher worker compared the final file
with the node and with Milne pp.410--411. No other agent was started, as required
by the dispatcher brief. This is not a claim of an independent-agent review; the
maintainer's independent review remains the delivery review.

The comparison checked every hypothesis and clause listed above. In particular,
`hquot` is the sheafification universal property, not surjectivity on F-points;
`hηq` ties it to the actual quotient map. The orientation of `haction` was checked
on (s,g): its left side is s·q(g), and its right side is q(iS(s)g), giving left
multiplication on right cosets. The final quantifier uses the action of S(A), not
only S(F), and the rational points are morphisms from the tensor unit over F.
The dimension equality is included in the conclusion rather than assumed, so an
incorrect dimension cannot make the bound vacuous. Properness includes all
required finiteness and separatedness conditions on X. The closed-subgroup
hypotheses constrain neither normality nor smoothness of H; `hsplit` includes
r=0. The injective list permits an infinite fixed locus. No mismatch was found
and no correction to the node's statement was necessary.
