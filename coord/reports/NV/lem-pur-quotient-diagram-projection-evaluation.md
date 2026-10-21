## Worker report

Item: `lem-pur-quotient-diagram-projection-evaluation`; group NV, stage 2.
The module `Sheaf.Paper.QuotientDiagramProjectionEvaluation` states
`SheafOfModules.QuotientDiagramProjection.quotientDiagramProjectionEvaluation`.
Its sole postponed proof is that theorem. All helper definitions have real data;
no extra axiom, arbitrary chosen map, or data definition with sorry is introduced.
The item statement, proof and proof dependencies are unchanged. Six already
landed interface nodes are added to stmt_deps, as permitted by brief-stage2 §5.
There are no new nodes or dependency repairs.

### Hypotheses and objects

- The commutative Noetherian ring is `(A : Type (max c v r)) [CommRing A]
  [IsNoetherianRing A]`, with `(I : Ideal A)`. The source small-site convention is
  expressed by `{C X : Type c} [Category.{v} C] [Category.{v} X]` and
  `[EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} X]`.
  Site object and morphism universes remain independent; neither is equated to
  the other. The module universe dominates both and the independent ring bound r.
- The two arbitrary sites are `J : GrothendieckTopology C` and
  `K : GrothendieckTopology X`. Here Lean J denotes the Y-site topology; the
  node's indexing category J is the existing coefficient sequence site instead.
- The topos morphism is `uInv`, `uPush`, `(adj : uInv ⊣ uPush)`, and
  `[PreservesFiniteLimits uInv]`. No scheme, point, geometric morphism of sites,
  or exactness of products is assumed.
- `constant J A` is transparently Mathlib `constantSheaf` applied to
  `CommRingCat.of A`; `ringSheafify` supplies the standard small-model
  sheafification. `finite J A I n` is `constant J (A ⧸ I^(n+1))`.
  Index n=0 means the first positive quotient, not A/I^0.
  `quotientMap` is induced by `Ideal.Quotient.mk`; `quotientTransition` is
  induced by `Ideal.Quotient.factorPow I (Nat.le_succ (n+1))`.
- Ordinary categories are the existing `SemilinearSections.Mod` and `Systems`,
  with `D` and `DS` their ordinary unbounded derived localizations. In particular
  DS is not the functor category into the derived category. Systems are modules
  over the genuine system ring on `coefficientSequenceTopology`.
- `Presentation.geometry` uses `RingedCoefficientProjection.Geometry` for the
  ordinary inverse-image ring and module functors. The X coefficient sheaf is
  its inverse image of the constant A sheaf, canonically the constant A sheaf on
  X. `qX_underlying` fixes every pulled quotient map by the underlying-set
  square, and `qX_transition` fixes their genuine successive quotient behavior.
  `Presentation.quotient` is the existing `SemilinearSections.Geometry`, whose
  coefficient transitions and geometric inverse images are normalized on the
  actual ordinary rings/modules. Thus no independent ringed structure is chosen.
- `geometry.left`, `.right`, `.adjunction` are the canonical ambient derived
  adjunction. The quotient counterpart is `quotient.adjunction`, and its
  finite counterpart is `quotient.derivedLevelAdjunction`. The imported
  Geometry interfaces normalize these as the derived adjunctions of the actual
  module adjunctions, including K-injective transpose formulas. They are not
  unconstrained adjunctions between abstract equivalent categories.

### Clause-by-clause conclusion

The statement existentially produces a canonical presentation and its laws;
it does not assume existence of a presentation or any of the desired equations.
The presentations use the already landed notion of a normalized scalar/tensor
model, and all new maps are helpers belonging to this item.

1. `Reduction` presents R = S Delta on the ordinary strict-system category.
   `ordinaryEvaluation` identifies its ordinary component with the actual scalar
   extension `levels n : ScalarData (q n)`. `transition_unit` says that actual
   m-to-n transitions carry the scalar-insertion unit to the scalar-insertion
   unit for every n≤m and every local section. This fixes ordinary reduction on
   the actual quotient system, not just independent evaluated objects.
   `Reduction.insertion` is its ordinary quotient augmentation. The constant
   tower, restriction U, i on complexes, and unused Rlim context do not occur
   in the final finite evaluation equation: reduction is specified directly
   by this ordinary model and its total left derived functor.
2. `Reduction.functor`, `.epsilon`, `.universal` and `.computes` give the universal
   total left derived functor of that ordinary construction, computed on K-flat
   representatives. `evaluation` identifies its finite value with `levels n.T`;
   `evaluation_model` specifies this identification on all complexes through
   the actual localization factors. This is exactly the derived reduction
   R_T=S_T Delta and its finite scalar evaluation, without derived-object-level
   choices. `Presentation.y` and `.x` supply the two sites.
3. Ordinary tensor is the existing `ordinaryTensor`; its unbounded derived tensor
   is the existing `Closed`/`Models` presentation. `TensorReduction.balance` is
   the displayed global scalar-extension tensor identification, and
   `.finiteBalance` is the finite scalar-extension tensor identification.
   `.finiteModel` imposes the existing scalar pure-tensor normalization.
   `.ordinary_evaluation`, `.summand`, and `.representative` fix the global map
   on ordinary sections and total K-flat representatives, including every
   whole-system transition. Thus the tensor isomorphisms cannot be unrelated
   arbitrary natural isomorphisms.
4. `Presentation.ordinaryPull` is the ordinary inverse-image/scalar square.
   `.ordinaryPull_insertion` fixes it by scalar insertion and the canonical
   ordinary geometric comparison. `.ordinaryPullComplex_component` fixes its
   complex extension. `.pull_representative` fixes the derived comparison on
   flat-term K-flat representatives. This supplies exactly the scalar/pullback
   identification used in the transpose of h and in the target balance.
5. `coefficientMate p H` is defined by `quotient.adjunction.homEquiv` applied to
   `p.pull.hom.app (P.obj H) ≫ p.x.functor.map (ambient counit H)`.
   Hence its transpose is R_X(epsilon_H), with the specified scalar/pullback
   comparison, exactly as required for h_H.
6. `targetBalance p H L` combines `tensorX.balance` with the inverse of
   `p.pull.app L`, giving R_X N ≅ R_X H tensor G_B R_Y L.
   `arrow p H L` is the single composite
   tensorY.balance, tensor(h_H,1), quotient.tensorProjection, and
   P_B(targetBalance.inv). Its source is R_Y(PH tensor L) and target
   P_B R_X(H tensor u*L). The imported `tensorProjection` is defined as the
   transpose of the quotient counit tensored with identity, preceded by the
   canonical pullback tensor comparison.
7. `finiteMate p n H` is evaluation of that very coefficientMate, followed by
   `quotient.pushEvaluation` and the finite scalar identification; its source
   is `(p.y.levels n).T.obj (P.obj H)` and target is P_n of H_n.
   `finitePull` is the finite pullback/scalar comparison induced by the same
   global square. `Laws.coefficient_counit` explicitly states
   u_n*(h_H,n) followed by epsilon_n equals scalar reduction of epsilon_H
   preceded by finitePull. This fixes the finite coefficient mate.
8. `finiteTargetBalance` gives N_n ≅ H_n tensor u_n* K_n, using
   `tensorX.finiteBalance` and `finitePull.symm`. The source balance is
   `tensorY.finiteBalance` on (PH,L).
   `Laws.evaluation` states the desired equation with all these source/target
   isomorphisms written in order: evaluation of arrow, pushEvaluation,
   and P_n of (x.evaluation followed by finiteTargetBalance), equals
   y.evaluation, source finiteBalance, tensor(finiteMate,1), and
   `quotient.levelTensorProjection`.
   The latter is literally the adjunct of the specified finite counit tensored
   with identity and the canonical finite pullback tensor comparison.
9. `quotient.counit_evaluation` and `.unit_evaluation`, contained in the
   produced Geometry, identify the actual quotient diagram adjunction with
   the finite module-induced derived adjunctions, including counits. The
   imported normalization retains the ordinary and derived transpose data;
   no preservation of K-injectives by varying-ring evaluation is required.
10. `Laws.naturality` quantifies over arbitrary H,H',L,L' and arbitrary h,k.
    The reduction and tensor comparisons themselves are natural isomorphisms.
    `Laws.transition` and `.pullTransition` are the existing restriction-form
    equations for every n≤m, using actual system transitions and the canonical
    coefficient/direct-image mate. Together with the single system arrow,
    normalized ordinary transitions, and finite comparison equations, they
    give transition compatibility of the evaluation formula.
11. H and L are arbitrary derived objects in all definitions and equations.
    No boundedness, perfectness, completeness, flat quotient hypothesis,
    projection-isomorphism hypothesis or evaluation-preserves-K-injectives
    assumption is present. K-flat and flat-term conditions appear only in
    representative normalizations of the canonical operations, not on H,L.

### Dependency declarations and sources

Original dependency declarations were read with their docstrings and signatures:
`IsNoetherianRing` (Mathlib.RingTheory.Noetherian.Defs),
`CategoryTheory.constantSheaf` (Mathlib.CategoryTheory.Sites.ConstantSheaf),
`CategoryTheory.ringedSiteModules` (Sheaf.CategoryTheory.RingedSiteModules),
`DerivedCategory`/`HasDerivedCategory` (Mathlib.Algebra.Homology.DerivedCategory.Basic),
`SheafOfModules.ringedProjectionMateExact` (Sheaf.Paper.ProjectionMateExact),
`CategoryTheory.exists_diagramSite_realization`
(Sheaf.CategoryTheory.DiagramSiteRealization),
`CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`
(Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients),
and `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
(Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses).
The size convention is metatheoretic and supplies no declaration.
The tower limit and general diagram realization are context/proof interfaces;
no unused derived limit is added as a hypothesis of the finite formula.

Added already landed dependencies:

- `def-pur-ringed-coefficient-projection-data`,
  Sheaf.Paper.RingedCoefficientProjectionData:
  `SheafOfModules.RingedCoefficientProjection.Geometry`, `.left`, `.right`,
  `.adjunction` (the node's primary declaration is `.Assertion`).
- `def-coef-semilinear-system-models`, Sheaf.Paper.SemilinearSystemModels:
  `WeilConjectures.SemilinearSections.Mod`, `D`, `Systems`, `DS`, `systemRing`,
  `evaluation`, `e`, `transition`, `ScalarData`, `Closed`, `Models`,
  `ordinaryTensor`, `ordinaryTensorHom`, `totalTensor`, `tensorSummand`,
  `tensorModelIso`, `flatTerms`, `ScalarTensorComparisonModel`.
- `def-coef-semilinear-derived-calculus`, Sheaf.Paper.SemilinearDerivedCalculus:
  `WeilConjectures.SemilinearSections.Data`, `underlying`, `ordinaryEvaluationTensor`.
- `def-coef-semilinear-geometry-base`, Sheaf.Paper.SemilinearGeometryCore:
  `WeilConjectures.SemilinearSections.GeometryBase` and its module-induced
  adjunction/transition data.
- `def-coef-semilinear-geometry-derived`, Sheaf.Paper.SemilinearGeometryDerived:
  `WeilConjectures.SemilinearSections.Geometry` and its exact-evaluation,
  counit, ordinary tensor and representative normalizations.
- `def-coef-semilinear-geometry-ops`, Sheaf.Paper.SemilinearGeometryOps:
  `WeilConjectures.SemilinearSections.Geometry.tensorProjection`,
  `levelTensorProjection`, `TransitionFormula`, `PullTransitionFormula`.

The plain import `Sheaf.Paper.SemilinearDerivedSections` supplies
`WeilConjectures.SemilinearSections.semilinearDerivedSections` for the eventual
existence proof. It is not a statement dependency: all types and operations used
in the statement belong to the six definition interfaces listed above.

Every recorded proof-dependency module that exists is imported for stage 3.
Sources checked: local Stacks sites-cohomology.tex, Tags 0B56
(equation-projection-formula-map), 07A4 (lemma-pullback-tensor-product),
07A6 (lemma-adjoint); the node also cites Zheng Construction 4.1, printed p.21.
The main theorem docstring gives the node's nine-step proof plan, including
singleton left extensions, counit tracking, tensor balancing and transitions.

### Edge cases

Checked n=0 (exponent one), n=m in all transition equations (identity);
I=0 (constant A system), I=top (zero quotient ring and zero quotient module
categories), u=id (coefficient mate and counit normalizations become identity),
H=0 or L=0, the zero ring, and arbitrary torsion such as A=Z,I=(2).
The latter explicitly needs derived scalar extension and derived balanced tensor;
no ordinary-flat simplification is made. Empty sites are allowed. There is no
empty indexing category because the positive-integer sequence is fixed.
No statement dispute or source correction is needed.

### Searches for an existing statement

The launcher msearch commands used group NV and this item. Results are recorded
verbatim by the wrapper in searches.jsonl in the sandbox:

- leanfinder, "Evaluation of the derived quotient coefficient diagram projection
  formula mate agrees with the finite coefficient projection formula": eight
  hits concerning Nobeling projections, algebraic presentations, tilt,
  Diophantine projection and adic completion; no matching statement.
- loogle, "CategoryTheory.Adjunction.derived_counit": the generic derived
  adjunction counit theorem only, with no quotient-system tensor evaluation.
- grep, "projection.*[Ee]val|[Ee]val.*[Pp]rojection", Mathlib CategoryTheory:
  Pi/Basic.lean only; unrelated to the varying-ring derived statement.
- leansearch, "Evaluation of derived quotient coefficient systems commutes with
  the counit projection formula": generic comonad and evaluation counits,
  polynomial evaluation, coalgebra counits and Adjuction.derivedε; no match.
- rg/grep of the item id and projection/evaluation patterns in the prescribed
  WeilConjectures and Sheaf source directories: the existing
  SemilinearSections.Geometry.ProjectionEvaluation is relevant and reused via
  its projection words and Geometry interface, but lacks this item's reduction
  of arbitrary ambient H,L, scalar coefficient mate, and balanced source/target.
  The quotient reduction presentation and its normalized scalar square are
  therefore supplied as owning-item helpers; no existing notion is duplicated.

Validation: scompile.py compiled the complete file both as a sandbox module and
at its final library module name, cleanly (28.5 s and 33.5 s respectively).
The final import/docstring adjustment is validated again by delivery preflight.

## Second reading by NV

The dispatcher explicitly prohibits starting other agents. This section records
NV's separate second pass over the node and complete module, not a claimed
independent reader. The maintainer's review of the delivery supplies that
independent review.

Checked both directions of each comparison, the transpose for h, the final
P_B map of targetBalance.inv, the source balance, and the finite target balance.
The evaluation equation compares arrows with precisely the same balanced source
and target. The geometric derived adjunctions are tied to the ordinary module
adjunctions, not just arbitrary Hom equivalences. The transition equations
quantify over every n≤m; the same system morphism is evaluated at all levels.
No new input condition on H or L appears. Corrected implementation issues during
this pass: ambiguous inverse-image/constant-sheaf universes, qualified evaluation
names, and the explicitly selected small-model sheafification instance. These
were elaboration repairs only; the mathematical node is unchanged. Every helper
is listed in lean.declarations with source and blueprint documentation.

## Returned-delivery repair (2026-10-21)

Repaired H2 from independent review of immutable head `a345d1d02a3b`:
removed `lem-coef-semilinear-derived-sections` from the added `stmt_deps` and
changed `public import Sheaf.Paper.SemilinearDerivedSections` to a plain import.
This theorem supplies existence for the proof; its declarations do not occur in
the statement. The six added definition dependencies remain. No declaration,
signature, mathematical statement, proof plan, proof dependency, or dependency
record changed. The initial saved-packet dry run passed at `d42831d5742`; the
returned H2 repair is nevertheless applied before redelivery.

Self-check: compared the saved packet to the current read-only base; only the
item's `lean` and permitted added `stmt_deps` differ. Compared the repaired Lean
file with the saved packet: only the import visibility changes, and the recorded
theorem signature is unchanged. The independent reviewer accepted every clause
and the edge cases; this repair preserves all of them.

Repair validation: `scompile.py` compiled the repaired file cleanly as
`Sheaf.Stage2.Sandbox0` (28.7 s) and at its final module name (29.2 s).
