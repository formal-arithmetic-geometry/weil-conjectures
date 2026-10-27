## What changed

Proved `WeilConjectures.FiniteAdjunctionDiagram.structure_isOver` with the canonical
self-algebra-map identity. Reduced `coefficientUnit_mem` to normalization and finite-Tor
constructibility of the actual degree-zero coefficient unit. Reduced
`finiteAdjunctionDiagramRealization` to four genuine steps: common symmetric calculus,
geometric realization (including absolute dualizing objects and integral support),
system duality, and the specified enriched system adjunction. The proof chooses the four
calculus witnesses once, uses the same witnesses in every step, and assembles the original
existential conclusion with no new hypotheses.

Extracted the existing definitions verbatim into `FiniteAdjunctionCoefficientUnitData`
and `FiniteAdjunctionDiagramData`; the original module publicly reexports them. This
allows the new step modules to import the data without an import cycle. No downstream
source module is adapted. Change record:
`coord/changes/H1-finite-adjunction-definition-interfaces.md`.

## Proved and sorry left

Of the three original holes, `structure_isOver` is proved outright.
`coefficientUnit_mem` and `finiteAdjunctionDiagramRealization` have complete combining
proofs but are decompositions, not completed mathematical proofs. Three old holes are
closed as local proof bodies; six strictly smaller named holes are added, so the packet
has six actual holes and a net increase of three before closure pruning. No sorry occurs
inside a definition or a private declaration.

All names below are in `WeilConjectures.FiniteAdjunctionDiagram`:

- `coefficientUnit_normalized` — `lem-sf-coefficient-unit-normalization`.
- `coefficientUnit_finiteTor` — `lem-sf-coefficient-unit-finite-tor`.
- `coefficientSystemSymmetricCalculus` — `lem-sf-coefficient-system-symmetric-calculus`.
- `finiteAdjunctionGeometricRealization` —
  `lem-sf-finite-adjunction-geometric-realization`.
- `finiteAdjunctionSystemDuality` — `lem-sf-finite-adjunction-system-duality`.
- `finiteAdjunctionSystemEnriched` — `lem-sf-finite-adjunction-system-enriched`.

Each has its own module, a source and full proof in words, and a DAG node. The unit split
separates the transition universal property from the levelwise constructibility/Tor
condition. The main split separates the simultaneous tensor model, actual geometric
operations, the dual-formula transpose, and the enriched transpose. Neither new
existence statement is the main theorem under a changed name.

The whole-packet compile passed for all nine modules. Three new lemma signatures had
whitespace warnings; these are corrected before the final delivery validation. The original
main theorem signature remains verbatim. All copied non-proof declaration bodies were
checked against the original text. All seven unchanged direct importers compiled against the delivered overlay. The first
delivery preflight found only two definition-node signature records with bodies included;
these records are corrected using the project signature parser. No Lean error or
consumer adaptation was needed. Delivery preflight supplies the final independent gate.

## No longer needed

No mathematical dependency or module is claimed globally pruned. The unit route is
unchanged. The parent proof now directly uses only the four new main step nodes; its
previous proof dependencies remain needed inside the new step nodes. The following
old direct proof imports are removed from the parent because its proof is now the
explicit assembly; they remain in the split nodes' proof plans wherever used:

- `Sheaf.Paper.SemilinearDerivedSections`.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts`.
- `Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint`.
- `Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint`.
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.
- `Sheaf.AlgebraicGeometry.UnboundedSiteComparison`.
- `Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.OpenExtensionFiniteTor`.
- `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`.
- `Sheaf.Paper.QcqsCompactSupportRealization`.
- `Sheaf.SixFunctors.FiniteExceptional`.
- `Sheaf.Paper.SfPreservationClass`.
- `Sheaf.Paper.NormalizedDVRTower`.
- `WeilConjectures.Compactification.NagataCompactification`.
- `Sheaf.SixFunctors.FiniteDualizing`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`.
- `Sheaf.Paper.WeilVerdierPreservationStrata`.
- `Sheaf.SixFunctors.FiniteCoefficientVerdier`.
- `Sheaf.SixFunctors.FiniteDualitySiteComparison`.
- `Sheaf.Paper.PullbackTorAmplitude`.
- `Sheaf.Paper.FiniteCoefficientTensorCtf`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `WeilConjectures.SixFunctors.Etale.Derived.TensorHom`.
- `Sheaf.SmoothPurity.InternalAdjunctionEvaluation`.
- `Sheaf.Paper.FiniteStageVerdierBiduality`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.

The three old public imports are retained verbatim in the parent in addition to the new
public definition interface. Definition relocation is not mathematical pruning. No Lean or DAG
node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The historical missing FiniteAdjunctionSystemData artifact is repaired in the current
compile environment: the required initial delivery check loaded imports and reached
proof elaboration. It found that the retained structure_isOver proof did not account
for the inferred specOverSpec self-structure. Explicit simplification of the self
algebra map repairs that proof, and a whole-item compile accepted it in 17.2 seconds.

The old parent node grouped helper definitions and two unrelated unit properties with
the full realization theorem. It now retains only the theorem attachment, while two
new definition nodes own the extracted interfaces. The original theorem statement,
finite maps, units/counits, no-common-bound condition, and blueprint unit route stay
unchanged. Edge checks cover identity coefficient quotients, the empty scheme, rank-one
unit in degree zero, identity morphisms, and the shared base calculus for the two
structure maps. No statement is weakened and no integral exceptional operation is assumed.

## New nodes

`def-sf-finite-adjunction-coefficient-unit` owns the two concrete regular-unit constructions.
`def-sf-finite-adjunction-diagram-data` owns the existing mapping, dualizing, duality and
integral-support interfaces, extracted without changing their bodies.

`lem-sf-coefficient-unit-normalization` is the quotient-extension universal property for
the regular system. `lem-sf-coefficient-unit-finite-tor` is its levelwise finite free
constructibility and Tor bound [0,0].

`lem-sf-coefficient-system-symmetric-calculus` requires one common simultaneous calculus
and signed tensor model. `lem-sf-finite-adjunction-geometric-realization` carries original
steps 1--9. `lem-sf-finite-adjunction-system-duality` carries steps 10--13.
`lem-sf-finite-adjunction-system-enriched` carries steps 14--18. All depend on the
extracted definition interfaces, not on the theorem whose proof consumes them.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
