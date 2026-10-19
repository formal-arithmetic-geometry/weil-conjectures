## Worker report

Q15, 2026-10-18. The saved packet is retained and completed. Its old report,
which described earlier incomplete import experiments, is preserved separately in
report-history-before-final-repair.md. The required initial deliver2.py --no-push
was run before repair. This report describes the delivered declarations.

IntegralRealizationShiftCoherence states the shift square for the supplied actual
Realizations.comparison and the shift equations for every canonical map and finite
expression context. Its theorem has sorry as its only proof. The original natural
statement is unchanged; only lean and additional statement dependencies change.

Hypotheses and clauses, read against the node:

- The algebraic closure of a finite field and characteristic p are FiniteFieldDatum D.
  The common variables l, Fact l.Prime, E, Field E, Algebra Q_[l] E and
  FiniteDimensional Q_[l] E, with _hl : l ≠ D.p, give precisely the coefficient
  setting. Quotient rings, completed coefficient sheaves, strict semilinear systems,
  reduction and total limit are the existing System, Integral, calculus.reduction,
  inputReduction and coefficientSequenceLimit, with no replacement construction.
- W and every variable scheme are Over (Spec (.of D.k)). e.val.geometric recursively
  requires finite-type schemes and the stated separated finite-type pullback/support
  maps. The expression constructors retain properness, quasi-compact openness and
  the specified compactifications. The finite inductive tree and Finite I express
  the finite well-typed expression.
- K : (e.val.domain l E o).FullSubcategory requires every input to satisfy
  sfIntegralConstructible and Good after reduction, and e.admissible requires Good
  at every intermediate system (including the open stage of compact support).
  Good is normalization, LevelBounds and compatible Origins; LevelBounds includes
  ordered common cohomological and Tor intervals at every positive coefficient level.
  These predicates are imported unchanged, not replaced by assumptions about endpoints.
- IndependentExpression requires the occurrence-to-label map to be bijective.
  Expression.independentInputs supplies this presentation for every original tree.
  Thus repeated object values are allowed, while their leaf slots remain independent.
  Function.update K.obj i ((K.obj i)[r]) changes exactly the designated input occurrence.
- R : Realizations l E D o is the supplied canonical family, including its actual
  reconstruction-unit, pullback, tensor, proper, open, compact-support and completion
  normalizations. RealizationShiftSquare uses its comparison at the original and
  updated input, rather than selecting an endpoint isomorphism. Its existential h
  asserts preservation of the full domain after the shift. The equation is
  c_new followed by the integral shift = the source shift followed by c_old[r].
- IndependentExpression.sourceShift is reduction's adjunction-mate shift, followed
  by the actual selected system context and total limit's right-derived shift.
  integralShift uses the identical selected integral context. TensorShifts fixes
  coefficient 1 in the first total-tensor slot and (-1)^(r*i) in the second slot,
  on every K-flat representative, with the corresponding descent equations.
- restrictedTower is the actual coefficientSequenceRestriction applied degreewise
  to a strict system complex. limitShift_roos equates the chosen limit shift with
  the specified product and shifted-cone map (diagonal 1, (-1)^r and the final [-1])
  through every normalized integralComparisonRoosBridge. Applying it to a simultaneous
  representative of S_p J_j R(K) uses that same tower, including its transitions.
  integralInterpretation.compactSupport is the recorded completed open/proper functor;
  R.compactSupport and sfQcqsCompactSupportRealization fix its finite projections
  and identify it with the recorded integral compact-support action. No arbitrary
  replacement tower, cone map, or shift defined by conjugation through c is used.
- Naturality in every input is provided by sourceShiftIso and integralShiftIso;
  shift_naturality states both equations on all morphisms of input families. The
  original R.comparison is already a natural isomorphism on the full domain.
- The second theorem conjunct quantifies every CanonicalPair at the original family.
  CanonicalMapShiftCoherence asserts existence of its synchronized shifted evaluation
  and the two shift equations for every such evaluation. SynchronizedIso/Basic/Pair
  retain the same constructor and geometric data at the two families, not two
  unrelated arrows. They cover compositors, tensor associativity and pull/tensor,
  open base change, clopen and support expansion, open projection, proper/open,
  units/counits, exchange, proper projection and compactification exchange/projection.
  Their identity, composition, pull, push, open, compact-support and tensor closures
  give arbitrary finite whiskering contexts. The target expression has its own
  geometric and domain witnesses, as required to compare the same canonical map.

Dependency declarations used: Sheaf.SixFunctors.IntegralCompactificationSystemRealization
(WeilConjectures.IntegralSystemRealization.Realizations, CanonicalPair and its existing
canonical generators); Sheaf.Paper.QcqsCompactSupportRealization
(WeilConjectures.sfQcqsCompactSupportRealization); Sheaf.Paper.SfIntegralConstructible
(WeilConjectures.sfIntegralConstructible); Sheaf.Paper.FiniteTorAmplitude
(WeilConjectures.finiteTorConstructibleIntegral and finite-level/field variants);
Mathlib.CategoryTheory.Triangulated.Pretriangulated (CategoryTheory.Pretriangulated).
The new modules directly build on the existing Expression and Interpretation of
Sheaf.SixFunctors.IntegralSystemExpressionDomain. Tensor normalization also reuses
Sheaf.SixFunctors.CompletedTensorShiftRight, and the existing field pullback shifts
and IntegralComparisonRealizationModels Roos bridge. Stated proof dependencies are
imported in the main module. Unstated proof nodes are not invented or assumed.

Edge cases checked: a singleton variable; repeated equal objects in different tensor
slots; both sides of tensor nesting; identity, positive and negative integer shifts;
zero objects; empty opens; and empty original label sets (there is then no tree built
from variables, so no independent input to shift). Positive levels are indexed n+1,
never quotient level zero. The only finite-label assumption concerns the independent
leaves of a finite tree; unused labels in an original presentation are not excluded
by the occurrence construction. Site object, morphism and coefficient universes are
not equated by this delivery.

Retained searches: msearch.py LeanFinder, query canonical realization isomorphisms of
strict coefficient systems commute with shifts in each input occurrence: eight
generic shift results, no match. Loogle, query CategoryTheory.NatTrans.CommShift,
CategoryTheory.Functor.CommShift: twelve generic results, including CommShift.comp.
Mathlib grep, query commShiftIso|shiftFunctor in CategoryTheory/Shift: twenty-five
generic shift hits. Upstream WeilConjectures and shared lean/Sheaf rg searches for
the item id and realization/shift combinations found no matching realization theorem.
The new-node search results are recorded individually in their mathlib_searches;
LeanSearch, LeanFinder/Loogle, Mathlib grep, upstream/shared rg, DAG grep and
blueprint_refs searches found no occurrence indexing or two-family synchronization
of this existing Expression, or the complete representative-normalized shift package.
Generic Pi/product-category functors and the published completed right shift are reused.
No STATEMENT-DISPUTED issue or natural-statement correction is claimed.

## New nodes

`def-pur-integral-expression-occurrences` supplies leaf occurrence indexing, independent
relabelling, repeated input families, single-slot contexts, explicit context search,
and the input-family shift endofunctor. These are real recursive constructions on
Expression, not a second geometric expression type. The helper evaluation identities
and naturality endpoints have named sorry theorems with induction proofs in docstrings.
Its source is the independent-slot convention of adic Step 2. Searches in its record
found only generic PFunctor/Tree and Pi tools, not these operations on Expression.

`def-pur-integral-operation-shift-data` supplies the normalized tensor-shift package,
primitive system/integral shifts, selected-context comparison, natural expression
shift isomorphisms and the strict-tower Roos equality. Tensor data is chosen only from
a theorem asserting uniqueness under the full representative characterizations;
no data is chosen from mere existence. Its source is adic Step 2 and the explicit
cochain tensor, mapping-cone and derived-limit conventions. Searches in its record
found generic bifunctor total shifts and Tor tools, not this normalization package.

`def-pur-synchronized-canonical-maps` refines the existing generator relations to
retain the same constructor, parameters and contexts at two input families. Its
projection and diagonal theorems state that it uses exactly the existing maps.
Its source is adic Step 2 and the maps-used sentence of fix-prop-coherence. Searches
in its record found generic relation/evaluation tools, not this project-specific
refinement. There is no arbitrary-arrow constructor or duplicate canonical operation.

## Second reading by Q15

Self-check of the retained packet by the current dispatched worker; no independent
reviewer or sub-agent was started. The maintainer's independent review is still
required, as specified in this worker brief. I read the node, all five statement
dependencies and their recorded declarations, the three new nodes and their modules,
the repaired dependency interfaces, and both blueprint passages. The clause-by-clause
check is above. I found that the report described an obsolete incomplete module,
that CanonicalMapShiftCoherence used forbidden local let bindings in a proposition,
and that the operation-shift record incorrectly listed inputShift/inputShift_obj,
which belong to the occurrence module. These are repaired. The proposition now
spells out the updated family and synchronized relation directly. Named helper
proofs remain sorry and definitions contain actual data. Validation results follow.

The initial dry run compiled its six submitted checks cleanly and then waited for
the shared repository refresh; its local process no longer exists after the provider
interruption, and no push was requested. The final packet removes the now-published
semilinear repair and is rerun through the prescribed dry run.

## Resumed packet validation

The required initial dry run compiled all five submitted Lean checks without
errors or warnings, then reported three stale blueprint.from.via paths. Updated
the three new nodes to include lem-pur-adic-purity-scalar-naturality, the final
link required by the current item ancestry. No Lean declaration changed.

## Returned-delivery repair

Removed the dependency node file for def-weil-finite-tor-amplitude and its
Dependency modules section, as required by return H13/H2 on head 629de211ff8c.
The current shared DAG retains NW's existing FiniteTorAmplitudeSites binding.
The delivery no longer changes that dependency record. The four accepted Lean
modules and their statements are unchanged. The item retains its original
finite-Tor dependency, and all three new definition nodes remain in the packet.

Self-check: compared the saved node copies with the current shared DAG; the
item changes only lean and the three added statement dependencies. Checked that
the remaining four modules each belong to exactly one delivered node, and that
no finiteTor declaration is used directly in any delivered module. The report
continues to identify the original integral predicates actually used through
the expression-domain interfaces. No additional mathematical correction is made.
