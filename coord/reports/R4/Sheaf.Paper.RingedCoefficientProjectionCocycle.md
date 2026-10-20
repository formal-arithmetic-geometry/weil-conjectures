## What changed

The original `ringedCoefficientProjectionCocycle` theorem has a complete Lean proof
from two strictly smaller geometric tensor results. The signature and the meanings
of all original definitions are unchanged. Shared records are relocated verbatim to
`Sheaf.Paper.RingedCoefficientProjectionData` and publicly re-exported by the original
module; the change record lists every downstream consumer. The data module also
exports six proved caches of existing Mathlib sheaf instances, avoiding repeated
site-equivalence inference in consumers without changing any mathematical data.

The categorical proof transposes the cocycle through the target-coefficient
adjunction, uses the defining mate/counit formula and naturality, and applies the
pullback associator equation. It proves the identity law by the same transposition,
and the commuting-square law by cancellation of the source associators and
`eqToHom_naturality`. It proves compatibility of the canonical derived adjunction
unit with shifts through the K-injective localization equivalence, then constructs
the mate's shift compatibility. The second conjunct follows by the same proof on
the actual coefficient sequence sites, before evaluation or inverse limit.

`coefficientScalarUnits` is fully proved: identity restriction, uniqueness of left
adjoints, linearity of the sheafification unit, uniqueness of universal left derived
functors, and naturality of `quotientCompQhIso` give ordinary multiplication and the
exact derived representative formula. The representative formula holds on every
complex, without needing its K-flat hypotheses. Termwise comparison shifts descend
through the homotopy quotient and Qh; the universal counit formula proves that the
constructed derived unit also commutes with normalized scalar shifts.
`coefficientScalarShifts` is fully proved from the existing coherent-shift theorem
for right Kan extensions. `coefficientAssociatorShifts` is fully proved by taking
the universal Kan lift of the composite counit and the termwise balanced comparison.
Kan uniqueness proves the lift's shift equation; invertible K-flat computation maps
and naturality identify that lift with the given scalar associator.
`coefficientPullbackShifts` is fully proved by extending the normalized computation
square from flat-term K-flat representatives to all complexes. Source and target
computation shifts, cancellation on K-flat representatives, and density then prove
the comparison's shift square on every derived object.

The two remaining source results are construction of the normalized inverse-image
comparison, and composition/unit coherence of already constructed comparisons
with balanced scalar tensors. Their modules contain one named public theorem each, with source
and complete proof in words. They do not assert direct-image mate laws. The second
assumes the comparison data constructed by the first; it contains no existence
claim for those data. Canonical scalar units and scalar shifts are supplied by the
proved scalar lemmas, not assumed as new existence holes.

Validation: the server compiled all eight packet modules and the unchanged
direct consumers RingedRefinementData and RingedRefinementClopen. Their public
interface text is identical apart from blueprint references. All four proved
sublemmas have only propext, Classical.choice, and Quot.sound as reported axioms.

## Proved and sorry left

Closed the one original local hole:
- `SheafOfModules.RingedCoefficientProjection.ringedCoefficientProjectionCocycle`
  (`lem-pur-ringed-coefficient-projection-cocycle`).

New fully proved public results:
- `SheafOfModules.RingedCoefficientProjection.coefficientScalarUnits`
  (`lem-pur-coefficient-scalar-units`).
- `SheafOfModules.RingedCoefficientProjection.coefficientScalarShifts`
  (`lem-pur-coefficient-scalar-shifts`).
- `SheafOfModules.RingedCoefficientProjection.coefficientAssociatorShifts`
  (`lem-pur-coefficient-associator-shifts`).
- `SheafOfModules.RingedCoefficientProjection.coefficientPullbackShifts`
  (`lem-pur-coefficient-pullback-shifts`).

Added two holes, and these are every remaining `sorry` in the packet:
- `SheafOfModules.RingedCoefficientProjection.coefficientPullbackComparisons`
  (`lem-pur-coefficient-pullback-comparison`). This constructs ordinary and derived
  comparison isomorphisms with their exact insertion/representative normalization.
- `SheafOfModules.RingedCoefficientProjection.coefficientPullbackCoherence`
  (`lem-pur-coefficient-pullback-coherence`). For existing comparison data and
  multiplication units, this proves their balanced composition/unit equations.

This is a decomposition: one original hole closed, two strictly smaller source
results left, net local holes increased by one. It is not a sorry-free proof of the
original theorem. No hole occurs in a definition or private declaration. The newly
proved scalar and inverse-image shift lemmas have no new proof holes.

## No longer needed

Removed the original proof imports `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
and `Sheaf.Paper.DerivedAdjunctionShift`. The former's bundled small-site system is
not used; the new comparison result uses the balanced-coequalizer/K-flat route
rather than its particular universe-coupled system. The latter's theorem is not
used: the canonical derived adjunction shift property is proved directly using
the source library's normalized K-injective construction. The provisional proof
imports `Mathlib.CategoryTheory.Whiskering` and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift`
were also removed after checking they were unnecessary.

The main node's old proof dependencies are replaced by the actual new geometric
lemmas, proved scalar and inverse-image shift lemmas, and the mate definition. In particular the
main proof does not invoke `lem-weil-pbc-mate-pasting`: it explicitly transposes and
uses counit naturality. It does not invoke the existence theorems
`lem-coef-semilinear-derived-sections`, `lem-weil-pbc-diagram-site-realization`, or
`lem-weil-pbc-ringed-projection-mate-exact`; their definitions still occur in the
public interfaces and their statement dependencies are preserved. The actual
sequence topology supplies the second instance of the uniform assertion.

Removed the corresponding unused main-node `tool_uses` entries, retaining the
adjunction mate definition. No upstream declaration or module is withdrawn. No
whole module is claimed globally pruned: other consumers may still use these
modules, and public statement imports are preserved by the relocation.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. The planned comparison theorem
`RingedDerivedMonoidalComparisons` packages `Site` with a `SmallCategory` and a ring
sheaf in that same universe, whereas this item's sites have independent c,v,r
universes. Its `Lift` data are also not this item's arbitrary scalar presentations.
There is therefore a nontrivial interface/construction gap in applying it verbatim.
The new comparison lemma states precisely the smaller geometric result in this
item's existing interfaces; it neither assumes the projection cocycle nor renames it.
The balanced double-tensor and multiplication calculation is separately isolated
as coherence of a comparison already provided, following the original plan's
steps 2 and 3. Step 7, all the shift compatibility, is proved in this packet.
The unit's route is unchanged.

## New nodes

`def-pur-ringed-coefficient-projection-data` attaches the existing auxiliary public
interfaces to their independent definitions module. No interface is weakened or
strengthened. Change record: `coord/changes/r4-ringed-coefficient-projection-data.md`.

`lem-pur-coefficient-scalar-units` records the fully proved ordinary multiplication
unit, its universal-derived representative formula, and its compatibility with
counit-normalized integer shifts.

`lem-pur-coefficient-scalar-shifts` records the fully proved simultaneous coherent
integer shifts, normalized by the scalar universal counits.

`lem-pur-coefficient-associator-shifts` records the fully proved shift compatibility
of the balanced derived scalar associators in the given normalization.

`lem-pur-coefficient-pullback-shifts` records the fully proved shift equation of
any given normalized inverse-image/scalar comparison, by computation and density.

`lem-pur-coefficient-pullback-comparison` is the unresolved construction part of
Stacks 0D6D/0G7E in the item's independent universes and normalized interfaces.

`lem-pur-coefficient-pullback-coherence` is the unresolved balanced-double-tensor
and multiplication-unit calculation for already given comparison data. It is a proper part of the argument and includes no projection mate statement.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
