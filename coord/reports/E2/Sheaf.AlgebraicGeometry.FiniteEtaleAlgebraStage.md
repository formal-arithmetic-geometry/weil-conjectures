## What changed

Proved `AlgebraicGeometry.Scheme.exists_finiteEtale_algebra_stage` in
`lean/Sheaf/AlgebraicGeometry/FiniteEtaleAlgebraStage.lean`, preserving its full signature
and existing docstring. Uses the three existing proof-only imports:
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
`Sheaf.AlgebraicGeometry.DescendFinite`, and
`Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`.

The proof constructs the filtered diagram of finitely generated A-subalgebras and proves
its colimit universal property using `Subalgebra.iSupLift`. Spec and cartesian projection
squares construct the inverse limit of the base changes of Y. A proved private helper
spreads out the finite-presentation cover, applies the two existing property-descent
statements, and takes a common upper stage. It explicitly proves preservation at the
upper stage and cancels the right pullback square. The final witnesses have the required
projection equations and the isomorphism in Over. No definition or public statement changed.
Updated the item's DAG proof and proof origin to describe these implementations.

## Proved and sorry left

Proved the module's sole original sorry:
`AlgebraicGeometry.Scheme.exists_finiteEtale_algebra_stage`
(node `lem-weil-pbc-finite-etale-algebra-stage`). No sorry remains in the delivered module,
and none is added elsewhere. All private helpers are proved.

This is a stage-3 proof from existing declarations, not a claim that the transitive target
closure is sorry-free. In particular it uses
`AlgebraicGeometry.Etale.exists_stage_of_inverseLimit`
(node `lem-weil-pbc-descend-etale`, module
`Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`), whose current repository version is proved from its chart-descent dependencies.
Finiteness uses `AlgebraicGeometry.exists_isFinite_baseChange_stage`
(node `lem-weil-pbc-descend-finite`), which still depends on the existing
`exists_isFinite_morphismRestrict_baseChange_affine_open` sorry
(node `lem-weil-pbc-descend-finite-affine-open`). Object spreading uses
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`.

Local single-file compilation validates the unchanged theorem and all helper proofs.
The required delivery dry run additionally checks the server compilation and axiom probe.
The directed system remains nonempty for zero rings, via its bottom subalgebra; singleton
adjoining covers every element without an injectivity assumption on A→B. Empty covers and
empty schemes require no point or nonemptiness witness. No new statement needs an edge-case
exclusion.

## No longer needed

During the first proof pass, removed the redundant added proof import
`WeilConjectures.Mathlib.RingTheory.Adjoin.FG` after checking that `AffineTransitionLimit` already publicly supplies it through
`WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`. No mathematical
node or module of the original route is pruned. None of the original public imports
or mathematical dependencies is pruned. All three
steps of the original argument remain. The implementation uses the general Mathlib lemma
`isLimitOfIsPullbackOfIsConnected` for base change of limits rather than the particular
`isLimitBaseChangeCone` construction. It applies both property-descent declarations directly
to the inverse system Y_R, avoiding an additional reformulation over Spec R. These are
implementation simplifications, not omitted mathematical steps or removed unit steps.

## Where the brief, the DAG or earlier work was wrong

The `thm-pd-spreading-out` Lean record lists only the morphism/equality descent declarations
`exists_pullback_hom_of_isLimit` and `exists_pullback_fst_comp_eq_of_isLimit`, although
part (1) of the node is object descent. The same recorded source module also proves
`exists_isPullback_of_finitePresentation`, which is the declaration used here.
Its source and signature were read directly; no duplicate spreading-out theorem was stated.

The source ring-colimit helper `CommRingCat.fgSubalgebraCoconeOf` assumes a field. The item
allows an arbitrary Noetherian commutative ring, so that helper cannot be specialized.
The same colimit construction is implemented privately for commutative rings and completely
proved, using the existing directed-poset and subalgebra universal-property declarations.
LeanFinder found ring-theoretic étale descent but no direct scheme result; Loogle returned
no matching finite-presentation/subalgebra result. Direct source searches found the
spreading theorem and the filtered-subalgebra constructions used above.

The item is below the unit's realized statements and steps; no `sk-thm-p1` statement or step
is bypassed. No mathematical error or disputed statement was found.


## Second reading by E2

1. Interface: PASS. Diffed the sole delivered Lean module against the current repository
   version. Compared the existing theorem signature byte for byte through `:= by`;
   it is identical, as is its docstring. No public definition, target, or hypothesis
   changes, and no change record is required. All added helpers are private.
2. Proof and trust: PASS. The sole module compiles locally without warnings (4.4 s).
   A scratch copy with `#print axioms` for all seven declarations also compiles.
   The ring diagram, cocone, colimit proof, and two property helpers use only
   `propext`, `Classical.choice`, and `Quot.sound`. The stage-descent helper and
   original theorem additionally use `sorryAx` from existing open dependencies.
   No delivered declaration contains `sorry`, and no forbidden implementation or
   axiom escape occurs. Neither private definition is hollow. The proof transports
   properties through the pullback isomorphism, takes a common upper stage, proves
   stability there, and constructs the required isomorphism over the original base.
3. Split statements: PASS, none. No new public statement, module, or node, and no
   restatement with `sorry` was introduced. Independently checked that singleton
   adjoining covers every B element even for noninjective A→B, that the bottom
   subalgebra makes the index nonempty for zero rings, and that no step requires
   points of the cover or a nonempty scheme. The private limit-stage helper needs
   only the qcqs and affine-transition assumptions it explicitly supplies.
4. Route and pruning: PASS. Read the spreading theorem and both property-descent
   declarations and their hypotheses. Read the Stacks sources online: [0GS2]
   (https://stacks.math.columbia.edu/tag/0GS2), [01ZM]
   (https://stacks.math.columbia.edu/tag/01ZM), [01ZO]
   (https://stacks.math.columbia.edu/tag/01ZO), and [07RP]
   (https://stacks.math.columbia.edu/tag/07RP); the local literature text is absent
   on this machine. The Noetherian assumption supplies finite presentation of
   the final finite-type A-subalgebra; properness supplies qcqs base-change stages.
   Independent LeanFinder search for finite étale objects over an inverse limit
   found no direct stage-descent theorem. Loogle confirmed `Subalgebra.iSupLift`
   and its inclusion lemmas; source searches confirmed the upstream subalgebra
   colimit helper assumes a field and cannot replace this arbitrary-ring proof.
   All proof-only imports are used; all public imports supply signature notions.
   Checked every old `proof_deps` entry against the implemented mathematical steps:
   none is pruned. The general cartesian-limit lemma realizes base change of limits
   without bypassing a unit. Read `dag/units/sk-thm-p1.json` and its `realized`:
   this item is below its fixed steps, which are preserved. Read the existing
   import-change records affecting both descent modules; no adaptation is needed.
5. DAG: PASS. The only node differs in `proof` and `proof_origin`; its statement,
   Lean signature record, and proof dependencies remain unchanged. Its three proof
   steps accurately describe the directed ring colimit, cover spreading and
   property descent over E, and the final projections and Over isomorphism.
   The spreading-out node's incomplete declaration list is correctly reported;
   its source module contains the object-spreading theorem used here. No new node
   fields need verification.

Second-reading changes: corrected the report to distinguish retained repository
imports from imports added during proof development, and to reflect the current
proved étale descent wrapper. Added this independent reading and its axiom results.
The Lean proof and DAG implementation needed no repair.
