## What changed

Repaired the quarantined, zero-hole raw cohomology diagram by exporting the
already proved canonical upstream module through its existing Sheaf path. This
preserves the explicit constructions and every declaration name rather than
loading two declarations with the same fully qualified name. The item itself is
restored; no deleted.txt is used and no quarantined archive is removed.

Made the same canonicalization in HigherDirectImageRawOverNaturality,
HigherDirectImageRawTrianglePullback, HigherDirectImageRawTriangleAdjunct,
HigherDirectImageRawTransitionToHomCore, HigherDirectImageRawTransitionToHom,
ModuleAbelianDerivedDirectImageComparison and AbelianHigherDirectImagePresheaf.
All these companion modules were unclaimed. The rawTriangleSource definition is
exported verbatim from the upstream RawTrianglePullbackExtension. The private moduleAbelianForget_injective_evaluation_acyclic
API is retained with a proof from the upstream theorem, via a private alias.
CartesianHigherImageAffineSectionLocalVanishing changes only its private
import all, so its access to the original defining module's private comparison
proof remains available. No existing public statement changes.

Twelve node attachments point to canonical upstream modules, including
ModuleAbelianCoefficientComparison for moduleAbelianForget, whose declarations
were moved there upstream. Mathematical dependency lists and unit routes stay.
The node that also records rawTriangleSource uses the upstream extension, which
publicly imports the remaining triangle API.
The change record is coord/changes/D2-raw-cohomology-canonical-upstream.md; it
includes the exact old modules, the replacements, and a transitive consumer
audit including quarantined modules.

Searches: msearch leanfinder found the generic Mathlib cohomology and Yoneda
functors, but these do not replace the prescribed derived pullback comparison;
loogle Functor.mapCocone returned no hit; msearch grep returned no hit. Direct rg
and reading found the exact upstream RawDiagram and the proved identity and
composition dependencies. No additional intermediate theorem is needed.

The unchanged quarantined RawModuleScalarPullbackComparison,
RawModuleScalarSourceFactors and RawModuleFreeSourceAcyclic are restored as
consumer checks repaired by these canonical imports; they each have zero holes.

Validation: lcompile.py --all compiled all 24 checked files successfully,
including all active direct consumers, the CartesianHigherImage proof consumer,
and all three restored scalar-comparison consumers. Every compile is below the
60-second single-file limit (the slowest uncached consumer was 52.8 seconds).
The standard delivery dry run passed its compile, axiom and server preflight
checks (review class CODEX). Unchanged validation copies were then removed from
the sandbox; the Lean repair and its consumer adaptations are unchanged.

## Proved and sorry left

The quarantined item has zero sorry bodies. This is a duplicate-definition and
import repair: proved 0 of 0 sorries; 0 holes closed, 0 holes added, 0 split off.
The canonical higherDirectImageRawOverPullback_functorial proof, additive map,
Over functor, diagram and cocone all remain provided by the existing upstream
RawDiagram module, which has zero sorry bodies. No sorry remains in any module
changed or restored by this packet. The private retained acyclicity proof is
complete. No theorem is weakened or replaced by a new assumption.

## No longer needed

The duplicate local proofs and definitions in the eight compatibility modules
are no longer needed: their upstream declarations provide the same API. Their
old proof-only imports are consequently removed from these wrappers; the
upstream proofs still retain whatever dependencies they use. The public imports
now export the canonical upstream counterparts. The CartesianHigherImage
consumer no longer imports all from Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf;
it imports all from the actual upstream defining module instead.

Removed direct imports, by compatibility module (their canonical proof
dependencies remain imported upstream):

- HigherDirectImageRawDiagram:
  `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality`.
  `WeilConjectures.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity`.
  `WeilConjectures.AlgebraicGeometry.HigherDirectImageRawPullbackComposition`.
- HigherDirectImageRawTrianglePullback:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf`.
- HigherDirectImageRawTriangleAdjunct:
  `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback`.
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf`.
  `WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp`.
  `WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift`.
- HigherDirectImageRawTransitionToHomCore:
  `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback`.
  `WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions`.
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf`.
  `Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct`.
  `WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionHomologyShift`.
  `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`.
- HigherDirectImageRawTransitionToHom:
  `WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions`.
  `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback`.
  `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore`.
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`.
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf`.
- HigherDirectImageRawOverNaturality:
  `WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions`.
  `WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverCoefficient`.
  `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback`.
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf`.
  `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom`.
  `WeilConjectures.AlgebraicGeometry.HigherDirectImageOverMapCoefficient`.
- ModuleAbelianDerivedDirectImageComparison:
  `WeilConjectures.SixFunctors.BaseChange.Derived`.
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`.
  `WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget`.
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`.
  `Mathlib.Algebra.Category.Grp.ZModuleEquivalence`.
  `Mathlib.CategoryTheory.Sites.Adjunction`.
  `WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence`.
  `WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax`.
  `WeilConjectures.CategoryTheory.InjectiveModulePresheaf`.
  `Mathlib.Algebra.Homology.ShortComplex.Ab`.
  `WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion`.
  `WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison`.
  `WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf`.
  `WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison`.
- AbelianHigherDirectImagePresheaf:
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`.
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`.
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
  `Mathlib.CategoryTheory.Sites.EpiMono`.

No mathematical node, source-library declaration, unit, or module is withdrawn.
No underlying identity/composition or comparison dependency is claimed pruned:
those proofs remain required in the canonical source library. Compatibility
paths remain available to both active and quarantined consumers.

## Where the brief, the DAG or earlier work was wrong

This assignment is a zero-hole repair, not an unproved functoriality theorem.
The 2026-10-20 source sync introduced the exact canonical RawDiagram proof while
retaining older Sheaf copies. The resulting mixed raw-triangle imports caused
the recorded duplicate-declaration error. The twin-retirement note saying that
moduleAbelianForget was absent from the upstream derived comparison overlooked
its relocation to the publicly imported ModuleAbelianCoefficientComparison.
The report makes no progress claim from the already completed upstream proof.
The source-library boundary is respected: no WeilConjectures file is edited,
no target signature changes, and the existing upstream proof route is retained.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
