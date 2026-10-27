## What changed

Proved `ordinaryFiniteP1_diagonal_unit` using the two supported-diagonal scalar
integrals, the coordinate trace contractions and the prescribed counit base-change
square. Its statement and trace counit are unchanged. The section, coefficient, scalar-square and triangle calculations have complete
proofs from their declared dependencies. Chart exchange uses one new local
construction-identification lemma described below.

The lower import interfaces are `ProjectiveLineDiagonalMaps` and
`OrdinaryFiniteP1DiagonalComponents`; the historical modules re-export their
original declarations. The returned packet is reconciled with current sheaf-dag:
F1's complete component formula, its supported Ext/realization/arrow interfaces,
chart transport, private helpers and proof imports are moved together
into Components. The supported-map and chart-map bodies are exactly F1's current
bodies. The formula node keeps F1's statement, proof steps and proof dependencies. A proved
comparison expands cached Alpha to the pair of supported units before
F1's original factorization argument. The comparison is proved in
`ProjectiveLineDiagonalAlphaUnits` so its kernel check is separate from the
component theorem; both modules compile within the limit and no proof obligation
is added. The unused local irreducibility attribute on the higher-layer `projectiveLineTraceTransport` is removed, since that constant
is intentionally not imported below the item.

`FiniteP1DiagonalPicard` now imports the lower Maps module instead of Data. The
current source has a complete proof of `finiteP1_diagonal_picard`; that proof is
retained verbatim. This breaks the former path through Trace and Adjunction back
to the item. Alpha retains F1's declaration-local instance section and specializes
`constantSingleSectionUnits`. Chart exchange uses a named identification of F1's chart transport with the
generic chart construction. The proof of this narrow comparison remains open:
its four factors are identical by the recorded constructor equations, but the
remaining functor-alias conversion repeatedly exceeded the compile limit.
It is separated from the fully checked exchange-pasting argument. The triangle assembly now uses the
named supported realization directly.

X7's three pullback comparison equations, its local attributes and its single-iso
`ordinaryFiniteUnitPullback` body are retained. Only the shifted-line construction
specializes the identical generic constructor. Its twisted-unit consumer
`FiniteP1TwistedUnitBaseChange` needs no change (reviewer: the unchanged module compiles
against the new body). All transparency checks remain enabled.
The proved construction and normalization lemmas are separated into modules to
keep their individual kernel checks within the compile limit; no obligations are
introduced by this separation.

The repaired TwistComposition and its ChartExchange and TraceCoordinates consumers
compile together (32.6, 30.8 and 50.2 seconds respectively). The existing positive
modulus binder in TraceCoordinates is retained, although the reused square does
not require it.

Validation: all 46 delivered Lean modules compile in import order across the
foundation, independent assembly and final assembly checks. The unit theorem
compiled in 44.3 seconds. All nine unchanged X7/F1 consumer modules compiled
against the repaired artifacts; their temporary source copies were removed.
The overlaid project import graph is acyclic. The delivery command below runs
its own complete checks before pushing.

The latest landing return identified a duplicate shifted-line square. The local
copy is removed from `OrdinaryFiniteTwistComposition`; its three composition
lemmas remain for chart exchange. Trace coordinates now privately imports
`FiniteShiftedLineSquare` and applies the existing stronger theorem without a
positivity argument. Its DAG edge points to the existing square node. The unchanged square module
compiles against the repaired pullback construction in 10.6 seconds; no forced
adaptation to that module is needed.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.ordinaryFiniteP1_diagonal_unit`: 1 of 1 assigned
holes, by decomposition. Added 1 hole and split off 1 obligation:
`AlgebraicGeometry.Etale.ordinaryFiniteDiagonalChartMap_eq_generic`, in the new
`OrdinaryFiniteDiagonalChartExchangeAux` module. This identifies the recorded
chart transport with the generic chart transport; it asserts no exchange, trace,
integral, triangle, or adjunction result. There is 1 `sorry` occurrence in the
delivered Lean files. The net hole reduction is zero. F1's complete proofs of
`ordinaryFiniteP1_diagonal_kummer_component_formula` and
`finiteP1_diagonal_picard` are preserved; their proofs are not claimed as Z8 work.
The imported library's remaining holes are existing dependencies.

## No longer needed

No library module is withdrawn. The duplicate local
`ordinaryFiniteShiftedLinePullback_square` and its proof are removed; the existing
`FiniteShiftedLineSquare` declaration is reused directly. TraceCoordinates no
longer imports `OrdinaryFiniteTwistComposition`; ChartExchange still needs its
composition theorem.
 The direct dependency
`lem-asd-ordinary-finite-class-comparison`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteClassComparison`) is not used: the existing
component formula supplies the normalized ordinary Kummer class and its two
components. Its library module remains for other consumers.

The item privately imports only its triangle and base-change assemblies, besides
its original public statement imports. Proof imports are placed with the supporting
calculations that use them. Unused draft APIs and three redundant generic
single-comparison composition wrappers were removed; X7's existing exact comparison
API supplies their role. `SectionProjectionUnit` and `EtaleTensorTraceBaseChange`
are not direct proof imports of `EtaleDiagonalTriangles`; their declarations remain
needed by supporting constructions. The component construction no longer imports
`EtaleChartExchangePasting`; only the chart-exchange proof uses its generic API.
Its unused public `OrdinaryFiniteP1KummerMaps` import is removed; the Integral and
ChartExchange statement modules import that interface directly where needed.
The historical formula's proof imports move to Components and remain needed;
this includes the coefficient records, ordinary Kummer and Chern pullback/first
Chern APIs, supported normalization/system, and constant-unit composition. No
geometric dependency of F1's proved component formula is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier packet was based before F1's completed component formula and could not
be merged without losing that proof. This repair takes the current complete proof
and its interfaces as the source, preserving its node statement, proof steps and
proof dependencies. The return described the Picard theorem as a hole; current
sheaf-dag has since proved it, so its complete proof is preserved as well.

The higher public import layer previously formed a cycle when the formula was
needed below the item. Changing only Picard's import to the lower projection/chart
interface removes that cycle. No statement is weakened and no completed proof is
replaced by a hole.

Return A1's X7 repair remains intact. The constant-object construction-cache record
correctly identifies the single-iso ordinary unit body; `genericConstantIso` occurs
only inside the separate generic comparison API. The original costly tensor and
counit checks are handled by proved generic comparisons and module separation.
No profiling options or disabled transparency checks remain.

Preflight's first run found that the formula node still listed the higher
`lem-amb-p1-diagonal-integrals` as a statement dependency, which led back through
Trace and Adjunction to this item. Its Lean statement uses only the relocated
canonical target and maps. That obsolete statement edge is replaced by
`def-z8-ordinary-finite-p1-diagonal-components`. F1's formula statement, proof
steps and proof dependencies remain unchanged. No Lean source change is needed
for this DAG correction.

## Forced adaptations

`FiniteP1DiagonalKummerComponentFormula` (F1) re-exports the current declarations
from Components via its original integral import, retaining both original public
imports. Keeping its original local declarations would give duplicate-declaration
errors for the relocated supported Ext/realization/arrow interfaces, target,
supported/chart maps and component theorem. The current F1 signatures, attributes,
map bodies and complete theorem proof are retained in Components.

`FiniteP1DiagonalPicard` (F1's current proved source; explicitly requested by the
return) changes only its public import from Data to Maps. With the original import,
the formula's lower relocation creates the cycle Components -> Picard -> Data ->
Trace -> Adjunction -> DiagonalUnit -> Triangles -> Integral -> Components. The
new import supplies exactly the chart used by the original proof.

`ProjectiveLineDiagonalData` (unclaimed) publicly imports Components and uses its
canonical target in the two direct-image signatures. Projection, chart and Alpha
are publicly re-exported from Maps. Alpha's local F1 instance attributes move with
its declaration. The trace definitions and factorization proof are retained.

`FiniteP1DiagonalAlpha` (unclaimed) changes its unfold list to expose the identical
`constantSingleSectionUnits` body; the original `unfold supportedDerivedUnit` fails
because that name no longer occurs after unfolding Alpha. Its public signature,
visibility and attributes are unchanged.

`FiniteP1TwistedUnitBaseChange` (unclaimed) is not adapted. The reviewer compiled the
unchanged module against the delivered `OrdinaryFiniteP1Arrows`: `unfold
ordinaryFiniteShiftedLinePullback` followed by `exact shiftedSingle_eq` closes by
definitional unfolding of the generic constructor. The edit was withdrawn.

`OrdinaryFiniteDiagonalChartExchange` and `OrdinaryFiniteP1DiagonalTriangles`
(Z8) adapt their unfolding calculations to F1's named chart transport and supported
realization. No public signatures change. Change records list the consumers and
exact constructions.

## New nodes

`def-z8-projective-line-diagonal-alpha` (`Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalMaps`): Use exactly the existing pullback projections and projective-space pullback chart isomorphisms. Define alpha as the composite of the two already specified supported derived units. The projections and charts are moved verbatim; the pair of source units specializes its identical generic construction, with no choice or change of meaning.

`lem-z8-adjunction-unit-transport` (`Sheaf.CategoryTheory.AdjunctionUnitTransport`): Construct the adjunction with the given unit and counit from their two triangles. Transport its right adjoint along the given natural isomorphism. The assumed equation for the prescribed counit and inverse-isomorphism cancellation identify the transported counit with it. The transported adjunction's two triangles finish the proof.

`lem-z8-etale-canonical-tensor-comparison` (`Sheaf.AlgebraicGeometry.EtaleCanonicalTensorComparison`): Give the existing canonical pullback tensor comparison its expanded curried-tensor type once. Its equation is definitional. Rewrite by this equation to inherit invertibility and identify each component with the oplax monoidal comparison.

`lem-z8-etale-chart-exchange-pasting` (`Sheaf.AlgebraicGeometry.EtaleChartExchangePasting`): Apply associativity of inverse-image compositors to paste the chart morphism with the square comparison. Direct-image composition is the conjugate of its inverse-image compositor. The generic mate chart-pasting identity and bottom naturality therefore identify the pasted exchange with exchange for the outer chart square. Transport along the recorded equalities for named chart morphisms, and use naturality to move a composition-compatible coefficient comparison through the resulting exchange.

`lem-z8-etale-diagonal-section-coherence` (`Sheaf.AlgebraicGeometry.EtaleDiagonalSectionCoherence`): Apply associativity of inverse-image compositors to the diagonal, either projection, and the original morphism. Cancel their common invertible factors to obtain the coordinate comparison after diagonal restriction. Naturality transports this equation through a coefficient isomorphism. The direct-image compositors are conjugates of the inverse-image compositors, so conjugate-equivalence composition gives the direct-image coordinate comparison and the equality of the two pushed section units.

`lem-z8-etale-diagonal-triangles` (`Sheaf.AlgebraicGeometry.EtaleDiagonalTriangles`): For the first triangle, substitute the first coordinate trace contraction. Naturality of the direct-image coordinate comparison moves the diagonal tensor-class map to the first section. The assumed first tensor section integral cancels it. For the second triangle, restrict coordinate interchange to the diagonal and use the common-base tensor coefficient comparison. Projection naturality identifies its diagonal tensor map with the second section tensor map. Substitute the second trace contraction and cancel using the second tensor section integral.

`lem-z8-etale-exact-exchange-comparison` (`Sheaf.AlgebraicGeometry.EtaleExactExchangeComparison`): The exact and total-derived inverse-image comparisons agree under the canonical exact-to-derived isomorphism. Expand the exchange as the mate of the square comparison followed by the counit, and apply the derived adjunction compatibility. Naturality of the comparison identifies the two exchange maps.

`lem-z8-etale-ordered-projection-comparison` (`Sheaf.AlgebraicGeometry.EtaleOrderedProjectionComparison`): The derived tensor comparison preserves the symmetry. Substitute this symmetry equation in the adjunction projection formula for the flipped tensor. Naturality of the tensor symmetry identifies it with the symmetry-conjugated ordered projection used by the ordinary finite-coefficient interface.

`lem-z8-etale-section-unit-normalization` (`Sheaf.AlgebraicGeometry.EtaleSectionUnitNormalization`): Tensor compatibility and the unit law identify the section inverse-image comparison on the monoidal unit. The single-complex unit comparison and the canonical constant-sheaf pullback comparison identify the same equation on the constant complex. Expand the named supported derived units and paste them using adjunction-unit naturality; the section comparison identifies their composite with the conjugate section isomorphism.

`lem-z8-etale-supported-diagonal-unit` (`Sheaf.AlgebraicGeometry.EtaleSupportedDiagonalUnit`): Define the diagonal tensor comparison using the ordered projection and the canonical section pullback identification, followed by the constant-complex unitor. Proper projection makes it invertible. Define the source comparison as the conjugate section isomorphism. Invert the diagonal tensor comparison, tensor the supported class, then apply the proper exchange/projection coordinate comparison; this constructs the natural unit. The generic section integral calculation proves its tensor contraction equation.

`lem-z8-etale-tensor-trace-base-change` (`Sheaf.AlgebraicGeometry.EtaleTensorTraceBaseChange`): The inverse-image compositor's tensor coherence and its identity law give tensor compatibility of a section comparison. The generic section projection identities then tensor any scalar section integral. For base change, transpose exchange and projection using the adjunctions, apply the square tensor coherence and counit identity, and cancel the proper projection maps. Naturality and the supplied scalar trace square give the evaluation square with the specified constant-complex unitors.

`lem-z8-ordinary-finite-counit-coefficient` (`Sheaf.AlgebraicGeometry.OrdinaryFiniteCounitCoefficient`): Naturality of the adjunction projection map in its coefficient, together with the ordered-projection identification, gives the coefficient projection square. Precompose the claimed counit transport equation with this invertible projection. The prescribed trace-counit projection equation reduces both sides to tensor of the same scalar trace composite.

`lem-z8-ordinary-finite-diagonal-chart-exchange` (`Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchange`): The projective-space pullback chart has the recorded selected projection and the other coordinate equal to the projective-line map. Apply chart exchange pasting with those two equalities. The normalized shifted-line composition law moves its coefficient comparison through the chart, giving the displayed exchange equation for each coordinate.

`lem-z8-ordinary-finite-diagonal-trace-coordinates` (`Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalTraceCoordinates`): Define the coefficient identification by the two normalized shifted-line pullbacks. Naturality of self-exchange moves the first coefficient comparison through exchange. The chart exchange identity and the Kummer scalar trace base-change square then identify the chart trace with pullback of the original trace. The constant-unit normalization gives the required monoidal unitor. The twist square law identifies the two common-base coefficient maps.

`lem-z8-ordinary-finite-p1-diagonal-base-change` (`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalBaseChange`): Precompose the inverse-biproduct trace square with the original splitting. Functoriality and inverse-isomorphism cancellation reduce it to the given Kummer decomposition square and its second-projection identity. Apply the prescribed trace-counit base-change theorem to this scalar trace square, obtaining the actual counit equation on every unbounded complex.

`lem-z8-ordinary-finite-p1-diagonal-integral` (`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalIntegral`): Invert the Kummer decomposition base-change square and apply the second biproduct projection to obtain scalar trace base change. For the diagonal integral, use the existing supported Cartier component formula. The second projection of its two Chern components is identity by the Kummer-normalized splitting and biproduct identities. This yields both scalar diagonal integrals for the existing source unit and chart maps.

`lem-z8-ordinary-finite-p1-diagonal-triangles` (`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalTriangles`): Use the supported diagonal component formula to obtain the two normalized scalar integrals. Normalize the shifted coefficient line along both projections and use the chart trace exchange equations in the existing even-line coordinate trace contractions. Tensor the first scalar section integral by the generic section projection calculation, and use the second scalar integral directly. The generic two-triangle assembly gives a unit for the common-base coefficient. Transport that coefficient along the specified normalized twist pullback; projection naturality identifies its counit with the prescribed Kummer trace counit.

`lem-z8-ordinary-finite-trace-base-change` (`Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceBaseChange`): Identify the ordinary projective-line exchange with the canonical derived exchange. Express the prescribed counits as inverse ordered projection followed by tensor of their scalar trace and the single-unit unitor. The constant-complex evaluation base-change theorem applies to the assumed scalar trace square. The canonical finite-twist evaluation pullback identity supplies the unitor square, and the recorded right-adjoint comparison is exactly the tensor square coefficient map.

`lem-z8-ordinary-finite-twist-composition` (`Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistComposition`): The normalization on roots and pure tensors makes the specified twist transport equal to the canonical normalized transport. Its composition law therefore gives the sheaf-line composition equation. Reuse X7's existing exact degree-zero composition calculation. Shift that equation using `shifted_composite_comparison`, then transport it through the exact-to-derived isomorphisms using naturality and inverse cancellation. The square equation is reused from the existing `FiniteShiftedLineSquare` module; this node attaches only the three composition lemmas.

`lem-z8-section-conjugate-comparison` (`Sheaf.CategoryTheory.SectionConjugateComparison`): Apply the conjugate-equivalence composition law to the two section isomorphisms and the square comparison. The assumed equality after restriction makes the two transposes identical. The conjugate equivalence is injective, giving the direct-image comparison equation.

`lem-z8-section-projection-unit` (`Sheaf.CategoryTheory.SectionProjectionUnit`): Expand a projection as the mate of the tensor comparison. Naturality moves each unit and counit past the adjacent map; the adjunction triangles cancel the resulting pairs. Apply the section inverse-image isomorphism and its tensor compatibility to identify the composite projection with identity. Cancel the explicitly assumed projection isomorphisms to tensor the scalar section integral. For chart and bottom naturality, apply the adjunction Hom bijection, substitute the composite counit, and use naturality. All identities retain the specified maps.

`lem-z8-shifted-composite-comparison` (`Sheaf.CategoryTheory.ShiftedCompositeComparison`): Apply the shift functor to the unshifted composition equation. Naturality of the shift-commutation isomorphism moves the coefficient comparison through the shift; the composite-functor commutation law identifies the resulting composite with the shifted compositor.

Change record: `coord/changes/Z8-diagonal-import-layers.md`.

`def-z8-ordinary-finite-p1-diagonal-components`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents`): Separate ownership of the
three canonical target, supported-class map and chart map definitions. Their current
F1 bodies are retained together with the complete component theorem and its supported
Ext/realization/arrow and chart-transport APIs. The trace-data interface names the
canonical target in its public statement.

`lem-z8-etale-single-pullback-comparisons`
(`Sheaf.AlgebraicGeometry.EtaleSinglePullbackComparisons`): Construct the canonical
constant and shifted single-object pullback comparisons before specializing the
coefficient category. The constant component formula is definitional; associativity identifies it with the source constant comparison. The shifted
comparison is shift commutation followed by the shift of the single-object map
and the supplied coefficient isomorphism. These are the original public comparison
constructions, cached without any arbitrary data or additional hypotheses. The shifted constructor also accepts the existing cached degree-zero functors explicitly.

Change record: `coord/changes/Z8-single-pullback-construction-cache.md`.

`lem-z8-ordinary-finite-trace-counit-comparisons`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounitComparisons`): Cancel the mapped
inverse unit isomorphism in the existing finite-twist unit square. Cancel the invertible
ordered projection in the defining trace-counit equation. These are two complete proofs
compiled separately after profiling, with no new sorry.

`lem-z8-ordinary-finite-trace-scalar-square`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceScalarSquare`): Identify the ordinary
ordered projection with the flipped tensor projection, apply the tensor projection
mate square to the scalar trace square, insert the inverse-projection presentations,
and use the supplied unit square. This complete proof is compiled separately from
its projective-line specialization; no new hole is introduced. Its two comparison
imports move out of the specialization module, whose unused public canonical-tensor
comparison import is removed.

`lem-z8-ordinary-finite-unit-pullback-normalization`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization`): Specialize the
canonical constant-complex pullback unit square to the ordinary coefficient interface.
This complete proof uses separately checked component and unit-square specializations to cache the expensive construction conversions;
no new hole is introduced. The ordinary single-iso unit-pullback body and X7 comparison equations are retained; the generic constant constructor is used only within the generic comparison API.

`lem-z8-ordinary-finite-single-unit-normalization`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization`): Cache the canonical single-object unit isomorphism with its ordinary coefficient
endpoints written explicitly and prove its defining equation by reflexivity. Prove
associativity for maps ending in this comparison. The unused draft cancellation
and functoriality wrappers are removed; the proof uses the general category laws directly. These
complete proofs let the concrete assembly use the canonical unit without unfolding
large tensor or exchange constructions while matching a rewrite.

`lem-z8-ordinary-finite-trace-evaluation-normalization`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceEvaluationNormalization`): Precompose
with the ordered projection, use the defining trace-counit equation, cancel the
projection inverse in coordinate evaluation, and identify the tensor trace by
functoriality and the cached unit equation. This self-contained comparison is
compiled separately from the concrete triangle assembly after profiling its
repeated construction conversions.

`lem-z8-etale-diagonal-coefficient-triangles`
(`Sheaf.AlgebraicGeometry.EtaleDiagonalCoefficientTriangles`): Treat the even line,
coefficient comparison, scalar traces, coordinate exchange identities and two scalar
integrals as parameters. Apply coordinate contractions, tensor the first integral,
and apply the generic supported-diagonal triangle calculations. Coefficient naturality
and the proved trace/evaluation comparison identify the transported prescribed counit.
The private first-triangle calculation depends only on the scalar data. The abstract evaluation-family congruence then transports it to the prescribed counit. Transport the resulting unit and its two triangles. This complete assembly separates
the tensor calculation from the large concrete Kummer data; no new hole is introduced.

`lem-z8-etale-diagonal-section-integral`
(`Sheaf.AlgebraicGeometry.EtaleDiagonalSectionIntegral`): Apply the section projection
contraction to the first scalar integral. Use the explicit equality of the cached
unit comparison with the canonical one, identify the diagonal tensor isomorphism,
and cancel the single-complex unitor transport. This gives the exact normalized
tensor integral consumed by the first-triangle theorem, without exposing its
intermediate component-isomorphism construction to the coefficient assembly.


`lem-z8-etale-proper-section-contraction`
(`Sheaf.AlgebraicGeometry.EtaleProperSectionContraction`): Relocate the complete
`properSection_contraction` proof from the supported-unit module after the combined
file exceeded the delivery kernel limit. It identifies the ordered projection mates
in the generic section tensor integral and cancels their inverses. Both the generic diagonal-triangle and diagonal section-integral modules import it directly. No signature changes or holes are added.


`lem-z8-ordinary-finite-diagonal-first-coordinate-exchange`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalFirstCoordinateExchange`): Specialize
scalar chart exchange to the first projection and normalize its canonical unit
comparison. This complete proof is compiled independently after profiling.

`lem-z8-ordinary-finite-diagonal-second-coordinate-exchange`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalSecondCoordinateExchange`): Combine
the pushed coordinate and coefficient comparisons, use their square identity, then
specialize scalar chart exchange to the second projection and normalize its unit.
This complete proof is compiled independently; no hole is added. The unlanded joint
draft interface `ordinaryFiniteDiagonalTrace_coordinate_exchange` is replaced by
these two identities.


`lem-z8-ordinary-finite-unit-pullback-comparison`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison`): Expand the existing
ordinary and generic constant component equations. Their two factors coincide.
This complete comparison is compiled separately before the canonical unit square,
keeping each kernel conversion within the per-file limit. It adds no hole.


`lem-z8-ordinary-finite-constant-pullback-hom`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom`): Specialize the proved
generic component equation to module coefficients. This caches the concrete instance
conversion before identifying the ordinary factorization and applying the unit square.
The proof is complete and adds no obligation.


`lem-z8-ordinary-finite-constant-unit-square`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare`): Specialize the canonical
constant-complex unit square to module coefficients. The ordinary unit theorem
combines it with the ordinary-to-canonical comparison using congrArg and transitivity.
This is a complete proof, separated only to cache the structural conversion.

`lem-z8-projective-line-diagonal-alpha-units`
(`Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits`): Expanding the generic
pair of single-object constant units and the two supported units gives the same
composite. This is a proved defining-equation API used to reconcile the cached
Alpha construction with F1's original component-factorization proof. Profiling
located this conversion's kernel cost, so it is checked in its own module.


`lem-z8-ordinary-finite-diagonal-chart-exchange-aux`
(`Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux`): Identify the
recorded chart map with the generic coefficient transport for exactly the same
chart, projections and shifted-line comparison. Expand both to the four factors
(unit, compositor, equality comparison, coefficient map), replace the recorded
ordinary adjunction by its defining canonical adjunction, and compare the
pullback/direct-image aliases. This strictly local construction identification
is the one new unproved statement. All exchange, trace and triangle arguments
above it are written separately in Lean. Profiling isolates the remaining cost
to the conversion of functor aliases after the constructor equations; no
completed source proof is replaced by this obligation.

The square-reuse repair is recorded in
`coord/changes/Z8-reuse-shifted-line-square.md`.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
