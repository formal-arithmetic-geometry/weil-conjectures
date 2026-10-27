## Worker report

This repaired packet states `WeilConjectures.ExceptionalRefinement.exceptional_refinement_mates`
with its retained four-stage coefficient interface. The item theorem and helper data
are unchanged from returned head 6aa171c49706. The only Lean change in the item module
is removal of its unused proof import of OpenImmersionLocalizing.

Hypotheses and clauses, individually:

- The prime and its distinction from the geometric characteristic are `l`, `[Fact l.Prime]`,
  `D : FiniteFieldDatum`, and `hl : l ≠ D.p`. `D.k` is its fixed algebraic closure.
- `Ω : Type v`, Field, Algebra and IsAlgClosure describe the coefficient closure, independently
  of the scheme size. The schemes and the finite coefficient fields use `max u v`; neither
  independent universe is identified with the other.
- X and Y have Over structures, locally finite-type and quasi-compact structure morphisms
  to Spec D.k. The morphism f has IsOver, IsSeparated, LocallyOfFiniteType and QuasiCompact.
  These are exactly finite-type k-schemes and a separated finite-type k-morphism. There is
  no separatedness assumption on either structure morphism.
- `c d : Compactification f` and `r : c.Refinement d` give the two compactifications and
  the proper refinement. Properness follows from the existing Refinement instance; there
  is no Cartesian-square hypothesis.
- `Stage.finite E n`, with n : ℕ+, supplies every positive coefficient quotient;
  Stage.integral, Stage.rational and Stage.closed give the remaining coefficient kinds.
  `C` is the published finite-Tor full category at ring stages, raw localization at E,
  and the actual common-stage category at Ω.
- `A B : Transport` retain the given exact adjunctions, not newly selected ones.
  Operation stores F, G, adjunction, exactness and the supplied shifts. `left` identifies
  F with the canonical ambient compact-support construction at finite/integral stages.
  `integralNormalized` fixes that identification through sfQcqsCompactSupportRealization;
  `rational`, localizationNormalized and commonNormalized give the exact rational/common
  representatives. Arbitrary naturally identified presentations are allowed, but all maps
  and shift structures are normalized through those identifications.
- `Mates.comparison s` is the pair of natural isomorphisms alpha : A.F ≅ B.F and
  rho : B.G ≅ A.G. RefinementComparison.counit and .unit are exactly the two displayed
  node equations, in Lean's left-to-right composition convention. Its leftShift and
  rightShift give both shift squares at every stage.
- `Mates.normalized` is RingRefinementNormalized for finite and integral stages. That
  published predicate fixes the inverse open-unit proper/open map and proper compositor
  under the supplied ambient realizations, including their coefficient/site maps.
- `Mates.transpose` is homEquiv applied to alpha at B.G followed by B's counit;
  `inverseTranspose` is the corresponding transpose of inverse alpha under B's adjunction.
- `SystemRealization.alpha` is a natural system isomorphism. Its `word` fixes alpha.inv
  as SystemProjectionFormula.refinement on the actual reduced input BEFORE taking limit.
  No faithfulness of evaluation is asserted. `inputGood` and `openGood` are output
  conclusions, so they impose no extra input bound or constructibility assumption.
- `SystemRealization.realizationNormalized` pins the endpoint realization to proper
  realization, open realization and the inverse reduction unit. `integralMap` is the
  total-limit realization equality with the SAME A.left and B.left; `shift` and
  `realizationShift` give the termwise and Roos-limit comparison with the canonical shifts.
- `Mates.rationalLeft` and rationalRight are the localized integral alpha/rho, conjugated
  by the fixed localization comparisons. `commonLeft` is exactly the displayed q^d,
  J(alpha), inverse q^c formula; commonRight is its right-mate counterpart. All formulas
  use the same A.operation and B.operation. Naturality is part of every NatIso.
- The theorem returns one P : Mates satisfying all these clauses simultaneously and,
  for every finite coefficient field, a SystemRealization of that SAME P. `o` and `R`
  are the supplied simultaneous geometric system model and its canonical realizations.
  The structure does not require a common Tor/cohomological bound across arbitrary inputs.

Recorded dependency declarations reused:

- Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing;
  the existing Padic coefficient ring, uniformizer and finite extension constructions.
- def-weil-scheme-morphism-properties is a convention record: use Mathlib Over, IsOver,
  IsSeparated, LocallyOfFiniteType and QuasiCompact, not another property definition.
- WeilConjectures.Compactification.RefinementCategory: AlgebraicGeometry.Compactification.Refinement.
- Sheaf.Paper.SfIntegralConstructible: sfIntegralConstructible and its full category.
- Sheaf.Paper.SfRationalizationKaroubi: sfRationalConstructibleCategory,
  sfRationalConstructibleLocalization, sfRationalLocalizationCommShift.
- Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients: its actual pair category and inclusion,
  including GeneralAlgebraicallyClosedCoefficients.inclusionCommShift.
- Sheaf.Paper.QcqsCompactSupportRealization: sfQcqsCompactSupportRealization.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData: C, Operation, RingStage,
  RingStage.inclusion, LeftRealization, FieldComparison, RefinementComparison,
  RingRefinementNormalized, rationalization and commonInclusion.
- Sheaf.SixFunctors.IntegralCompactificationSystemRealization: Operations, Realizations,
  CanonicalBridge and ProperOpenCoherence; IntegralOperationShiftData supplies the fixed
  reduction/open/proper/limit shifts. SystemProjectionFormulaCoherence supplies the actual
  support, refinement and inverseOnDomain constructions, reused without a private copy.
- Mathlib.CategoryTheory.Adjunction.Mates and Mathlib.CategoryTheory.Shift.Adjunction
  supply the generic mate and adjoint-shift notions. Other proof-only imports are the
  existing declarations of the node's proof dependencies.

Edge cases checked: empty X or Y and the zero complex require no nonemptiness or nonzero
hypothesis; identity refinements are included; positive quotient levels exclude only the
unintended level-zero ring; every integer shift, including zero and negative shifts, occurs.
Non-Cartesian refinements and schemes nonseparated over k remain in scope. Finite-Tor
inclusions preserve exactly the underlying representative and map. Raw localization
introduces no new objects, and the common-field formulas permit arbitrary finite stages.
No hollow definition, new axiom, independent-universe equality or arbitrary-map replacement
is used. There is no STATEMENT-DISPUTED flag or source correction.

Search record retained from the earlier attempt: msearch.py leanfinder query
"Proper open unit normalized compactification refinement comparison of exceptional
adjunctions at finite integral rational and algebraically closed coefficients" returned
eight unrelated Proj/normalization results. Loogle query
"CategoryTheory.conjugateIsoEquiv, CategoryTheory.conjugateEquiv" returned generic conjugacy
projection lemmas. Mathlib grep query
"refinement.*adjunction|RingRefinementNormalized|refinementRational" returned no specialized
result. Project rg found RefinementComparison, RingRefinementNormalized and the parent
CoefficientConstructionRefinements, which cannot supply this child's proof without a cycle.
The upstream node-id search had no match. This retry read the exact mate/shift/normalization
interfaces and retained these existing definitions. The returned dependency detour is removed: the existing upstream performance repairs suffice.

## Source-fidelity and Transport normalization review

This retry read the item statement, the dependency signatures and docstrings, the current
blueprint tensor-Hom statement and exceptional inverse-image paragraph, the retained
Q154 construction steps 20--21, and Zheng PDF pages 34--37. Zheng supplies the ordinary
system constructions (5.13--5.15) and the adjoint normalization route (5.22--5.24);
the exact pro-etale realization equations are the retained DAG synthesis, not statements
quoted verbatim from Zheng. The current blueprint's condensed Brown construction does
not replace or identify the fixed normalized-system adjunctions in this retained item.

The normalization review requested by the route note is complete for the retained item:

- At ring stages, LeftRealization is an isomorphism to the actual ambient proper/open
  functor. Transport.leftShift uses the inherited inclusion shifts (ringInclusionShift),
  fixing the operation's left shifts through that realization. Operation.unitShift and
  counitShift tie the right shifts to this same adjunction. RingRefinementNormalized
  records the open-unit equation and proper compositor, with the inverse open comparison
  in the orientation giving F^c to F^d; it does not accept an arbitrary refinement map.
- integralNormalized identifies the chosen integral-left realization with the prescribed
  sfQcqsCompactSupportRealization. localizationNormalized then determines q on these
  same representatives. localizationShiftX/Y identify every component at every integer
  with the published raw localization shift after the finite-Tor inclusion. The raw
  localization has the integral representatives as objects, so no rational object is
  omitted by stating the map equation on integral K.
- commonNormalized fixes q to the identity representative at every finite coefficient
  field. commonShiftX/Y equal the published inclusionCommShift structures, which are
  themselves normalized by shifted pairs. Every closed-stage object has a finite-stage
  representative. Thus the common equations cover the entire common-field category.
- The counit equation of each FieldComparison determines its b as the right mate of q.
  The right maps in the output are also explicitly fixed in both directions by
  transpose and inverseTranspose. The two equations of RefinementComparison are exactly
  the node's two displayed adjunction equations, read using Lean's composition order.
  rationalLeft/Right and commonLeft/Right use the same fixed q/b, with the required
  inverse at the source and forward comparison at the target.
- SystemRealization.word equates alpha.inv to the canonical system refinement before
  any evaluation or total limit. realizationComponent uses the supplied proper
  realization, the normalized open realization and the inverse reconstruction unit.
  Realizations.openNormalization and its canonicalBridge/properOpen fields fix these
  primitive comparisons. integralMap compares its total limit with the SAME output P
  and the SAME A.left/B.left. shift and realizationShift retain the prescribed termwise
  and limitShift structures. The goodness assertions are outputs of the theorem.

No item statement correction or universe identification is justified by this review.
The saved Lean signature equals lean.statement verbatim. The item has exactly one sorry,
its named theorem; helper data are actual constructions. Every item line is at most
100 characters. The maintainer independently accepted the item statement at returned
head 6aa171c49706; the present repair does not alter that statement or its definitions.

## Repair of returned head 6aa171c49706

1. H6/H13: restored `lean/Sheaf/Paper/OpenImmersionLocalizing.lean` and
   `dag/nodes/sec-six-functors/det-proper-image-localizing-open.json` byte for byte
   from the current live read clone. The proved private
   `openImmersionLowerShriek_tor` and the ProjectionFormula import are restored;
   the packet introduces no new sorry in that dependency. The earlier support-route
   replacement was unnecessary after maintenance commits 7c37f35db6e and 71d0a58cb2a.
   The old report is retained only as historical scratch material.
2. H7/b: restored the item's proof_deps exactly to the current base, removing the
   added det-proper-image-localizing-open edge. Removed the unused
   `import Sheaf.Paper.OpenImmersionLocalizing` from ExceptionalRefinementMates.
   Rebased all other node fields onto the current read clone; only lean differs.
   Removed the obsolete dependency-repair claim from lean.note. No statement,
   statement dependency, proof step, theorem signature or helper data is changed.

## Validation

Byte equality of both restored dependency files, equality of item proof_deps with
base, the sole import-line change in the item module, and verbatim lean.statement
were checked before compilation. Current compile, dry-run and delivery results
will be recorded below. All compiles use the prescribed wrappers.

The explicit paired scompile.py check exited 0 with no warnings: the restored
OpenImmersionLocalizing checked in library mode in 36.4 seconds, and the item
checked in library mode in 40.4 seconds. Both sandbox checks also passed
(56.4 and 12.9 seconds). No proof was replaced or new sorry introduced.

The prescribed ordinary dry run exited 0:
`OK (dry run): commit 9f159cd2778 passes the preflight and compiles; nothing pushed`.
Its staged paths are only the item module, item node and report. Neither restored
dependency file appears in the commit, confirming both requested dependency
restorations are byte-identical to the fetched delivery base. Both returned
points are repaired; normal delivery follows with these same Lean/node files.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
