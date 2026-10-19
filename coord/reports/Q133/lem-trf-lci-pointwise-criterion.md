## Worker report

The module `Sheaf.TraceFormula.LciPointwiseCriterion` states the node's three-way
scheme criterion and the finite-type affine algebra criterion.  The first scheme
conjunct renders clause (1) as an affine cover by `Spec (C i)` with `Algebra k`
and `Algebra.FiniteType k` witnesses, open-immersion and structural-map equations,
point coverage, and `Algebra.IsLocalCompleteIntersection`; its right side renders
clause (3) by an explicit essentially-finite-type regular-local quotient presentation
of every stalk, including the induced `k`-algebra equivalence.  The second scheme
conjunct renders clause (2) by principal affine global-complete-intersection
neighbourhoods and equates it with the same stalk condition.  The final conjunct
renders the affine algebra equivalence for every finitely generated `k`-algebra and
prime localization.  All variables and universes are explicit; empty covers and zero
rings are permitted by the imported definition.

Dependencies used in the module are:

* `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.LocallyOfFiniteType` from Mathlib;
* `Algebra.IsLocalCompleteIntersection` from `Sheaf.RingTheory.CompleteIntersectionOverField`;
* `IsRegularLocalRing`, `RingTheory.Sequence.IsRegular`, `Algebra.EssFiniteType`, and
  `Localization.AtPrime` from Mathlib;
* the proof-plan modules `Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence`,
  `Sheaf.RingTheory.LCIRegularSequenceGlobalCompleteIntersection`,
  `Sheaf.TraceFormula.EssentiallyFiniteTypeCIKernelInvariance`, and affine scheme APIs.

Edge cases checked: the empty scheme gives vacuous pointwise clauses; the zero ring has
no prime ideals and is allowed by `IsGlobalCompleteIntersection`; the regular sequence
may be empty; arbitrary characteristic fields and arbitrary finite index types are
retained; no nonemptiness or perfectness hypothesis was introduced.

Searches made:

* `msearch.py ... leanfinder "scheme locally finite type over field local complete intersection every local ring complete intersection"`: only finite-type and smoothness declarations, no criterion.
* `msearch.py ... loogle "IsGlobalCompleteIntersection, IsLocalCompleteIntersection, IsRegularLocalRing"`: no hits (the project names are not in Mathlib).
* `msearch.py ... grep "CompleteIntersection|complete.intersection|regular.sequence" RingTheory`: only generic regular-sequence and presentation documentation, no criterion.
* `rg` over `WeilConjectures/` and project `lean/Sheaf`: no existing declaration of this node; the related definitions and affine-locality theorem are distinct statements.

No statement correction or `STATEMENT-DISPUTED` flag is needed.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
