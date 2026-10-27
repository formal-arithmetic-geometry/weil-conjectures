## What changed

The assigned signature and public import are unchanged. Its proof now obtains the finite
scalar evaluation square, transfers finite cohomological support along its input scalar
isomorphism, applies the finite-ring compact scalar theorem, and cancels the two invertible
endpoint factors. It imports CompactSupportScalarEvaluationSquare privately.

FiniteCompactScalarConstructible defines the specified intrinsic compact scalar mate as the
transpose of sfCompactSupportRestriction. It proves its invertibility for arbitrary finite
rings when the input is bounded constructible and its scalar extension has finite
cohomological support. The proof uses finiteRing_constructibleDerived_origin, the normalized
siteScalarIso, interval reflection, intrinsicCompactScalarIsoOfOrigin_hom, and naturality.
The scalar extension need not be constructible, and no finite quotient map is assumed flat.

CompactSupportScalarEvaluationSquare constructs systemCompactEvaluation on arbitrary systems
from the existing proper and open evaluation mates. Its remaining theorem states the
unconditional equality between evaluation of the actual system scalar word and the finite
intrinsic scalar transpose, with all endpoint isomorphisms displayed. It has no boundedness,
constructibility, Noetherian, completeness or cartesian-system hypotheses. The main proof
eliminates its existential comparison isomorphisms inside a proposition; it defines no data
by selecting an arbitrary witness from an unproved existence theorem.

Validation: lcompile.py --all compiled all three final files without warnings. The finite-ring
profiling check took 9.3 s (313 ms elaboration, 557 ms instance synthesis, 271 ms kernel
checking); no declaration bottleneck appeared. The corrected square compiled separately in
7.1 s. The final batch reported 63.7/71.1/73.8 s wall times, so the required declaration probes
in deliver3 remain the per-file delivery check. All profiler settings have been removed.

## Proved and sorry left

Closed the original hole in
WeilConjectures.FrobeniusExchange.systemCompactScalar_evaluation_isIso
(node lem-sf-compact-support-system-scalar-finite-invertible) by a complete proof from the
new finite-ring theorem and the evaluation square.

Also proved
AlgebraicGeometry.Scheme.FiniteCompactScalar.intrinsicCompactScalar_isIso_of_constructible
(node lem-sf-finite-compact-scalar-constructible), including the antecedent construction,
reflection of scalar bounds, the prescribed transpose formula, and naturality transport.
FiniteCompactScalarConstructible has zero sorry.

Added one hole:
WeilConjectures.FrobeniusExchange.systemCompactScalar_evaluation_square
(node lem-sf-compact-scalar-evaluation-square). Its proof is exactly `by sorry` in its own
module, with the source and complete proof in words. This isolates the third step of the
assigned plan; it is an equality for arbitrary systems and asserts no invertibility.

The assigned module has zero remaining holes. One original hole was closed and one new hole
was added: this delivery is a decomposition, with net hole change zero, rather than a claim
that the entire obligation is proved without further dependencies.

## No longer needed

No existing import was removed and no existing module was withdrawn; no global module pruning
is claimed. The assigned node's six former direct proof dependencies are replaced by the
finite-ring specialization and the unconditional evaluation square. The finite-ring origin
and finite compact scalar transport results remain used by the proved specialization;
SemilinearSections and the system-operation realization remain dependencies of the square.

The standalone classical-sheaf exactness result det-pe-classical-sheaves-modules is no longer
needed as a separate direct step: the proved interval clause of
finiteRing_constructibleDerived_origin already reflects the required cohomological bounds.
The general ringed-topoi tensor/pullback lemma
lem-weil-pbc-ringed-topoi-derived-tensor-pullback is likewise not separately invoked: the
specified siteScalarIso supplies the exact scalar/site comparison used in the proof.
These are the modules Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules and
Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses. Their modules and declarations
are retained, including any uses through other APIs.

## Where the brief, the DAG or earlier work was wrong

No statement was corrected and no unit route was changed. The old plan's first two steps can
be proved together for general finite rings using the already proved finite comparison and
transport APIs. The old third step still requires a specialization of the generic
semilinear evaluation calculus to the actual fixed cochain scalar models and the specified
proper/open mates; merely applying the generic evaluation_mate theorem does not supply its
comparison isomorphisms and normalization hypotheses.

Edge cases checked in the finite-ring proof are empty cohomological support (the lower and
upper bounds use min/max), zero complexes, zero finite rings, empty schemes, and identity
coefficient maps. None requires nontriviality or a flat coefficient map. The unconditional
square includes n=0 and arbitrary unbounded systems and is strictly the map-computation
step, independent of the finite-ring invertibility theorem.

## New nodes

lem-sf-finite-compact-scalar-constructible records the proved finite-ring specialization in
lean/Sheaf/Paper/FiniteCompactScalarConstructible.lean. Its source is Stacks 0GL6/09AL and the
compact-support paragraph of lem-fix-operation-reduction. It has a complete Lean proof and
introduces no new hole.

lem-sf-compact-scalar-evaluation-square records the unconditional proper/open word evaluation
in lean/Sheaf/Paper/CompactSupportScalarEvaluationSquare.lean. Its source is the original
third proof step, Zheng 4.1/4.10 and Stacks 0941/06YY/07A6. The scalar evaluation isomorphisms
come from the generic ScalarSystems comparison after transport between normalized universal
cochain models; mate evaluation and pasting give the stated equality. This is the one
split-off theorem.

For both nodes, LeanSearch, LeanFinder, Loogle, Mathlib grep, project searches and a search
of the entire imported blueprint found generic scalar or natural-isomorphism calculus,
but no existing statement of these specializations. There are no change records because no
existing declaration interface or definition was changed outside the assigned proof.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
