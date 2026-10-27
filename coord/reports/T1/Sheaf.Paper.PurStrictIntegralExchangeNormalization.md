## What changed

Proved the original purStrictIntegralExchangeNormalization from five strictly
smaller intermediate statements and the existing proved strict proper-mate and
completed-unit equations. The geometric proof explicitly cancels the chosen H,
identifies towerV prime with the actual ringed strict mate, derives the completed
proper equation, and derives the completed open equation from its published unit
law. Only the final total proper/open square is supplied by a new intermediate
statement; the proof assembles all these parts in Lean.

Moved all 25 existing constructions/predicates verbatim to
Sheaf.Paper.PurStrictIntegralExchangeData, publicly reexported by the original
module. This avoids import cycles between intermediate modules and the aggregate
theorem. Every original body and signature is unchanged. The extraction has been
checked textually after stripping comments. All original public imports remain
through the reexport. Five downstream modules were checked; none requires
adaptation. The current active consumer claims are U2 on
SemilinearExchangeReindexing and U3 on IntegralScalarIsomorphismExchange.

Change record: coord/changes/T1-pur-strict-integral-exchange-data.md.

## Proved and sorry left

Original hole closed: AlgebraicGeometry.Scheme.purStrictIntegralExchangeNormalization
(node lem-pur-isomorphism-strict-integral-exchange-normalization). The original
module contains zero sorry. Its private reindexingProperNormalization and
reindexingSupportNormalization helpers are proved. The proper helper uses only
the two invertible units; the support helper uses the geometric input facts and
the final total unit equation.

This is a decomposition, not a net proof: one original hole is replaced by five
strictly smaller, non-equivalent parts (net holes closed minus added = -4).
The delivery adds these five public theorem holes, one per new module:

- AlgebraicGeometry.Scheme.purIntegralGeometricInputNormalization
  (lem-pur-integral-geometric-input-normalization): only the three completion units
  and identification of the ordinary open map, with no proper or total equation.
- AlgebraicGeometry.Scheme.purIntegralStrictCalculus
  (lem-pur-integral-strict-calculus): the strict mate, horizontal and vertical laws,
  with no quotient reduction or completed equation.
- AlgebraicGeometry.Scheme.purIntegralStrictReduction
  (lem-pur-integral-strict-reduction): fixed reduction squares for the actual
  exchange/composition maps, with all specified finite corners.
- AlgebraicGeometry.Scheme.purIntegralCompletedCoherence
  (lem-pur-integral-completed-coherence): only completed identity and pasting laws,
  retaining origins for vertical inversion.
- AlgebraicGeometry.Scheme.purIntegralTotalUnitEquation
  (lem-pur-integral-total-unit-equation): only the last total completion-unit
  square, assuming the ordinary open beta identification. It does not assert
  the proper strict identities, invertible units, or any coherence law.

Each remaining theorem has its source, complete proof in words, exact Lean
signature and a new DAG node. No definition contains sorry. All geometric
hypotheses, fixed corner maps and finite-etale-origin domains are retained.
Zero objects, empty schemes, identity base changes, n=0 (quotient exponent 1),
and empty generating tuples were checked against the stated constructions.

## No longer needed

No module is withdrawn or claimed globally unnecessary. All original public
prerequisites are retained in the reexported data module. The aggregate proof
reuses the existing completedExchange_mate helper via private import all, rather
than reproving its diagram-site tensor rectangle.

Removed original proof-only imports (the definitions do not need them):

- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.ProjectionMateExact
- Sheaf.Paper.CondensedAmbientExchange
- Sheaf.Paper.RingedExchangeTensorCoherence
- Sheaf.SixFunctors.OpenTensorNormalization
- Sheaf.Paper.RingedOpenStrictReduction
- Sheaf.Paper.RingedOpenScalarLimitCoherence
- Sheaf.Paper.ConstantCompletionEquivalence
- Sheaf.Paper.BasicOperationsCoefficientReduction
- Sheaf.CategoryTheory.FlatRingedDiagramRestriction
- Sheaf.Paper.FlatScalarDirectImageLimitCoherence
- Mathlib.CategoryTheory.Adjunction.Mates

The following original proof dependencies are not direct dependencies of the
aggregate proof anymore. Their remaining arguments are retained in the split-off
statements. This is dependency relocation, not global pruning:

- def-weil-pbc-adjunction-mate
- def-weil-pbc-ambient-ringed-exchange
- lem-cbc-compactifiable-compatible-tower
- lem-cbc-complete-proetale-composition-pasting-coherence
- lem-cbc-completed-open-strict-mate-identification
- lem-cbc-completed-ring-strict-finite-exchange
- lem-cbc-flat-scalar-direct-image-limit-coherence
- lem-cbc-ringed-open-scalar-limit-coherence
- lem-cbc-ringed-open-strict-reduction
- lem-cbc-strict-tower-proper-open-calculus
- lem-fix-operation-reduction
- lem-pur-isomorphism-completed-reduction-reindexing
- lem-sf-open-tensor-normalization
- lem-weil-pbc-constant-completion-equivalence
- lem-weil-pbc-flat-ringed-diagram-restriction
- lem-weil-pbc-mate-pasting
- lem-weil-pbc-profinite-coefficient-inverse-image
- lem-weil-pbc-ringed-exchange-tensor-coherence
- lem-weil-pbc-ringed-projection-mate-exact
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- prop-weil-pbc-direct-image-limits
- prop-weil-pbc-rlim-functoriality

The existing strict mate helper and completed-unit equations supply the shorter
proper/open route. The original node has no tool_uses entries to remove.

## Where the brief, the DAG or earlier work was wrong

The original DAG described a fresh ringed tensor/coherence proof for proper
normalization. The library already contains the proved private
completedExchange_mate helper and the proper/open completed unit equations.
Reuse avoids duplicating those arguments. The remaining laws are real work and
are not represented as completed progress.

The stale attribute removing WeilConjectures.IntegralHom.derivedCategory is not
valid with statement-only imports: the compiler reports that constant unknown.
Removing the attribute command changes no declaration.

The final total square was written categorically and its tactics completed, but
kernel verification took 76--102 seconds and hit the deterministic timeout.
Profiling isolated the cost to definitional comparisons across the pbc and
ordinary derived-category presentations and composite natural transformations.
Trials using explicit component equations, direct equality composition, sharing
coefficient-limit expressions, and equivalent component/predicate presentations
did not remove that cost. All definition trials are reverted. The final total
square is therefore a separate named step, with the complete algebraic argument
in its docstring; no expensive proof is claimed verified. The proper/open
assembly with that step postponed compiled in 13 seconds during diagnosis.

No target statement or source-library declaration is changed.

## New nodes

- def-pur-strict-integral-exchange-data: the 25 unchanged constructions and
  predicates, extracted to a publicly reexported data module. Change record:
  coord/changes/T1-pur-strict-integral-exchange-data.md.
- lem-pur-integral-geometric-input-normalization: original steps 1 and 5--8;
  completion-unit invertibility and the ordinary open-unit identification.
- lem-pur-integral-strict-calculus: original steps 7, 10--12 and 14; strict mate
  normalization, horizontal/vertical equations and retained-origin inversion.
- lem-pur-integral-strict-reduction: original steps 2--3, 7--8 and 13--14;
  strict and finite reduction squares with prescribed corners.
- lem-pur-integral-completed-coherence: original steps 5--6, 9--12 and 15;
  applying derived limit with the specified reconstruction comparisons.
- lem-pur-integral-total-unit-equation: original step 9; paste the two unit squares
  to obtain only the final total equation.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
