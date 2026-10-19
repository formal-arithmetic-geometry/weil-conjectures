## Worker report

The returned duplicate declaration was repaired by reusing the existing
`Sheaf.AlgebraicGeometry.MultipointedCurveModification` module. The duplicate
`MultipointedStableModification` module and delivery-only definition node were
removed. The item imports the canonical `AlgebraicGeometry.MultipointedCurve.Hom`
and uses its fields `curve`, `marking`, `curve_over`, `marking_over`, and `comm`;
stability is the existing `AlgebraicGeometry.MultipointedCurve.Hom.IsStable`
predicate. The theorem `AlgebraicGeometry.Temkin.stableModificationUniquenessNormal`
remains a statement with `sorry` as its only proof.

The theorem renders the item hypotheses as follows. The base is
`{T : Scheme.{u}} [IsIntegral T] [CompactSpace T] [QuasiSeparatedSpace T]`, and
normality is `hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧
IsIntegrallyClosed (T.presheaf.stalk x)`. The original pair is
`C : MultipointedCurve T`; smoothness and generic etaleness are respectively
`hX : Smooth (pullback.snd C.x T.fromSpecFunctionField)` and
`hD : Etale (pullback.snd C.d T.fromSpecFunctionField)`. The two source pairs
and compatible pair maps are `{C₁ C₂ : MultipointedCurve T}` and
`f₁ : C₁.Hom C`, `f₂ : C₂.Hom C`. Their stable hypotheses are
`hf₁ : f₁.IsStable T.fromSpecFunctionField` and the corresponding `hf₂`.
`IsStable` expands in the canonical dependency to proper pair maps, schematically
dense modification opens, generic-fibre isomorphisms, semistability, and the
absence of contracted projective-line components with at most two special points.

The conclusion is the unique pair of actual isomorphisms
`∃! α : (C₁.X ≅ C₂.X) × (C₁.D ≅ C₂.D)` satisfying, clause by clause,
`α.2.hom ≫ C₂.i = C₁.i ≫ α.1.hom` (marking compatibility),
`α.1.hom ≫ f₂.curve = f₁.curve` (curve comparison), and
`α.2.hom ≫ f₂.marking = f₁.marking` (marking comparison). The generic identity
clause in the source is forced by these equations and the generic isomorphism
fields of `IsStable`; it is not replaced by an extra assumption.

Dependencies used: `Sheaf.TraceFormula.MultipointedCurve`
(`AlgebraicGeometry.MultipointedCurve`),
`Sheaf.AlgebraicGeometry.MultipointedCurveModification`
(`MultipointedCurve.Hom`, `Hom.curveBaseChange`, `Hom.markingBaseChange`,
`MultipointedCurve.markingBaseChange`, `IsSemistable`, `Hom.IsEtaModification`,
`specialPoints`, `Hom.IsStable`), `Sheaf.Paper.OrgogozoInductionData`
(`Orgogozo.geometricPoint`, `Orgogozo.IsOrdinaryDoublePoint`),
`Sheaf.AlgebraicGeometry.PureDimension` (`Scheme.IsPureDimension`), and the
Mathlib/Weil declarations for `Smooth`, `Etale`, `IsProper`, closed immersions,
pullbacks, projective lines, and function fields. The proof plan retains the six
source steps in the node: generic injectivity and separated equalizers;
finite-type normal-model reduction; eta-normality; valuation comparisons;
valuative domination in both directions; and marking factorization/gluing.

Edge cases checked include empty markings, empty fibres, identity modifications,
nonseparated and nonproper original curves, nodal (non-normal) fibres, and infinite
special-point sets (`encard`). No extra Noetherianity, connectedness,
separatedness, or properness hypothesis was added. The canonical dependency's
projective-line and special-point definitions match the item's geometric-fibre
formulation.

Searches recorded in the node and prior packet were checked: LeanFinder and
LeanSearch queries for uniqueness of stable modifications, Loogle queries for
`Scheme`/`Normal`, and Mathlib grep for `multipointed`, `stableModification`, and
`IsStableEtaModification` found no exact theorem. Direct `rg` over the shared Lean
tree found the existing canonical module, which is now imported and reused. No
statement correction or `STATEMENT-DISPUTED` flag is needed.

## Second reading by Q61

I read the current item node and the full canonical dependency module after the
repair. Every base hypothesis is explicit; `MultipointedCurve` supplies the curve,
marking, flat finite-presentation, pure-dimension, and closed-immersion data. The
generic hypotheses use the canonical function-field pullbacks. The source maps are
canonical compatible pair maps, and `IsStable` provides all eta-modification,
semistability, and stability clauses. The three conjuncts under `∃!` exactly render
marking preservation and the two member-map comparisons. The duplicate declarations
are gone: the file imports only `Sheaf.AlgebraicGeometry.MultipointedCurveModification`,
and the node cites `def-trf-multipointed-curve-modification`. There are no new
nodes or dependency modules.

Validation: `scompile.py` and `deliver2.py --no-push` are rerun after this repair;
only the theorem's expected `sorry` warning is permitted.
