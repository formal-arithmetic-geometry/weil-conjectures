## What changed

The item now proves `AlgebraicGeometry.Etale.exists_affineSpaceTopTrace` from the
normalized projective-line theorem and two separate geometric results from its source
proof: the normalized localization triangle and the open-counit exchange square. The original statement and all existing public signatures are preserved.

Moved the unchanged trace constructions to `AffineTraceConstruction`, re-exported by
the item, so the intermediate modules use the actual maps without an import cycle.
Refactored the ordered adjunction and exchange towers through generic category lemmas;
the component formulas and the equality with Mathlib adjunction composition are proved.
The line and tower adjunctions use the proved-equal explicit-component composite
adjunction. The tower adjunction is irreducible. The short one-line composites,
adjunction and right comparison are abbreviations, so the kernel unfolds these
aliases before the large scheme and derived-functor definitions.
The line-left functor is the definitionally equal explicit open/proper composite.
The actual open adjunction is recorded once with ordinaryFinitePullback as its right
functor, avoiding repeated comparison of the large derived-category instances.

Proved the right-functor Tate normal form, including dimension zero and boundedness on
the constant input. The induction is over a general coefficient category and then
specialized to ModuleCat. This avoids comparing different elaborations of the large
concrete derived monoidal instances. The affine-line counit deduction uses a morphism
to a split distinguished triangle, preceded by a triangular coordinate change.
The canonical right base-change isomorphism now stores its two components explicitly.
The generic equality affineTraceRightSquareIso_eq proves that this is the original
square component followed by inverse image of the projective comparison. Together with the short aliases, this is intended to repair
the kernel timeout in comparing its hom: profiling showed thousands of reductions
of scheme pullback limits in the nested Iso.app/mapIso presentation.
The right comparison interface retains the composite right functors, with a proved
equality to the component comparison. The generic one-coordinate proof takes the
exchange natural transformation before specializing its components. These avoid
repeated conversion between inverse-image objects over different source categories.
The complete coordinate base-change induction and the final counit naturality square
are also proved.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.exists_affineSpaceTopTrace`.
The item has zero sorries. This is a decomposition of one hole into two separate
geometric statements, not a net hole reduction.

Also proved, with no local holes:

- `AlgebraicGeometry.Etale.affineTraceRight_normalForm`.
- `AlgebraicGeometry.Etale.affineTraceTowerCounit_baseChange`.
- `AlgebraicGeometry.Etale.affineTraceLineCounit_baseChange`, by counit naturality
  and the two input squares.
- `AlgebraicGeometry.Etale.affineTraceLineCounit_isIso`, from the localization result.
- The construction module's generic tower counit, isomorphism induction, exchange
  recurrence and comparison with Mathlib composition.

Exactly two holes are added, each a named public theorem in its own module:

- `AlgebraicGeometry.Etale.affineTraceLine_localization`
  (lem-amb-affine-trace-line-localization): source steps 2, 3 and 6, retaining the
  actual open counit and the normalized projective counit. Only restriction of the
  first summand must be identity; the other restriction component is unrestricted.
- `AlgebraicGeometry.Etale.affineTraceLineExchange_openCounit`
  (lem-amb-affine-trace-line-open-counit-base-change): source step 8, comparing the actual
  open/proper compactification exchange with the open counit, before the projective trace.
  This statement has no Tate datum, normalized trace or Noetherian hypothesis.

No definition or private declaration contains a sorry. Both remaining statements
are independent geometric steps, strictly smaller than the existence assertion
with its normal-form, boundedness, arbitrary-dimensional trace and base-change parts.
They have complete source proofs in their docstrings and matching DAG nodes.

## No longer needed

The proof does not need the Chern class to restrict to zero at infinity.
If restriction in the two projective coordinates is (1,q), replace the coordinates
by (x,y)↦(x-qy,y). This makes restriction first projection and leaves trace second
projection. Consequently the localization result does not need lem-amb-kummer-any-base
as a separate proof input. The normalized projective-line datum still retains its
original Kummer specification.

The localization node uses the already proved unbounded source theorem
exists_distTriang_openClosed (lem-fin-module-open-closed-triangle), replacing
the bounded-below-only lem-cbc-open-closed-recollement input.

The direct triangle-isomorphism argument replaces the cohomology argument, so
lem-sf-derived-homology-long-exact and
lem-weil-pbc-unbounded-derived-iso-cohomology are not needed in this proof.
The existing derived open tensor comparison replaces any new stalk calculation;
removed the obsolete top-level tool_uses entries lem-pod-etale-stalk-tensor-scalar,
lem-weil-pbc-extension-by-zero-stalks and lemma-weil-pbc-geometric-stalk-conservative.
These removals concern this item's argument, not other uses elsewhere in the library.

The following former direct proof imports were removed from the item. Some remain
needed in the normal-form module or in the two retained geometric obligations, so
they are not all claimed as pruned from the target import closure:

- WeilConjectures.AlgebraicGeometry.ProjectiveSpace
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
- Mathlib.AlgebraicGeometry.Morphisms.Proper
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- WeilConjectures.Compactification.ProjectiveSpace
- Sheaf.AlgebraicGeometry.OpenClosedRecollement
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
- WeilConjectures.SixFunctors.Finite.Exact
- Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
- Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
- Sheaf.Paper.RingedTopoiDerivedTensorPullback
- WeilConjectures.AlgebraicGeometry.Sites.Kummer
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
- Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- Sheaf.AlgebraicGeometry.ProperProjectionFormula
- Mathlib.AlgebraicGeometry.Noetherian
- Mathlib.Topology.Defs.Filter
- Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
- WeilConjectures.SixFunctors.Etale.Derived.Tensor
- Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
- Sheaf.AlgebraicGeometry.ExactUnboundedExchange
- Sheaf.AlgebraicGeometry.ProjectiveLineTrace
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection


## Where the brief, the DAG or earlier work was wrong

The previous report claimed three compiling holes but the retained working files
included unfinished proof attempts. It also incorrectly claimed that infer_instance
proved the affine-line counit; no such instance exists. This packet replaces those
claims with the checked deductions and the two explicitly named geometric holes.
The original nine-step plan unnecessarily proved vanishing of the second restriction
component and then used cohomology; the triangular coordinate argument removes both.

A resumed dispatch reset the reference clock: the earlier recorded start was
1792425806.316522, while the current .budget start is 1792429725.806053. The worker did
not edit .budget. Proof work continued across the provider interruptions; no delivery
was pushed by those interrupted attempts. The earlier report's queue-wait and consumer
validation claims are superseded by the checks reported with this packet.

There are eight delivery modules. All eight compile in dependency order without
warnings (normal form 38.1 seconds, main theorem 6.8 seconds). The dry run passed
at commit 2884726482, review class CODEX. Its post-success temporary-worktree cleanup
timed out; nothing was pushed by the dry run.

The initial seventeen-consumer snapshot yielded thirteen successful compiles.
During checks, FiniteExceptionalSystemAdjunction was withdrawn upstream and the
linear-action consumers were refactored. Current checks also passed
AffineLinearTraceAction, AffineLinearUniversalAction, AmbientAffineTranslationTrace,
VectorBundleIntegration, FiniteCoefficientSmoothPurity, FiniteUniversalSmoothTrace,
FiniteSmoothAdjunctionGeneralBase, Paper.VectorBundlePurity,
PurityDncCoefficientTransport and Targets.VectorBundlePurity. Other checks hit either
the existing sixty-second limit or a missing new-module artifact. The current
AmbientDiagonalPurityBaseChange, FiniteRingSectionDeformation and FiniteGeneralRing
checks report an import conflict between the Sheaf and WeilConjectures versions of
HomCoverGluing, both declaring SheafOfModules.existsUnique_hom_of_cover. Baseline
checks against the original library reproduce that same HomCoverGluing conflict
in all four checked consumers, including PurityDiagonalDualizingObject. The complete
six-module linear-action chain compiles against this packet: action, exchange
coherence, universal action, family, rigidity and linear invariance. No consumer
source was changed. ReductionExceptional and FiniteDualizing timed out on the latest
recheck; both had passed earlier checks.
No target statement changed and no forced consumer adaptations have been made.

## New nodes

`def-amb-affine-trace-construction`: the existing actual trace functors, adjunctions,
comparisons and exchanges, factored out and refactored with proved component equations.

`lem-amb-affine-trace-line-localization`: the separate geometric localization triangle,
with only the first restriction component normalized and the projective trace retained.

`lem-amb-affine-trace-line-counit-iso`: the proved categorical deduction from that
triangle, using a triangular coordinate change and a morphism to the split triangle.

`lem-amb-affine-trace-line-open-counit-base-change`: the separate open counit square
for the actual standard-compactification exchange, without any projective trace.

`lem-amb-affine-trace-line-counit-base-change`: the proved one-coordinate deduction
from that open square and the projective counit square.

`lem-amb-affine-trace-tower-counit-base-change`: the proved generic ordered pasting
induction, specialized to the affine coordinate tower.

`lem-amb-affine-trace-right-normal-form`: the proved Tate tensor, shift and pullback
induction and boundedness assertion.

Change record: coord/changes/G1-affine-trace-construction.md.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
