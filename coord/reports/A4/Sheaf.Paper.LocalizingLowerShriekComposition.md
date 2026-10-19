## What changed

Proved AlgebraicGeometry.ProEtale.CondensedRing.exists_localizingLowerShriekComposition
with its original signature. A proved single-model lemma constructs the ambient composition
isomorphism using dense compactifications, proper/open interchange, and the open and proper
composition comparisons. The parent lifts this isomorphism to the full localizing target,
conjugates it by the three existing compactification cocycles, and proves the simultaneous
comparison square by naturality and the cocycle laws. The already landed B3 theorem
compactificationRefinementComponent_id identifies the comparisons with the prescribed
refinement components.

The four delivered Lean modules are LocalizingLowerShriekComposition,
LocalizingLowerShriekCompositionModel, LocalizingAdmissibleCoefficients, and
RationalExceptionalRestriction. Added the missing finite-subextension-valued algebraic-closure
case to IsLocalizingAdmissibleCoefficient, retaining every original alternative, including
all continuous maps into the algebraic closure. The only consumer adaptation adds Or.inl
in RationalExceptionalRestriction; its signature and visibility stay identical.
Change record: coord/changes/A4-localizing-admissible-qbar.md.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.ProEtale.CondensedRing.exists_localizingLowerShriekComposition
(lem-sfb-localizing-lower-shriek-composition).

The new theorem
AlgebraicGeometry.ProEtale.CondensedRing.exists_localizingLowerShriekComposition_model
(lem-sfb-localizing-lower-shriek-composition-model) is fully proved. Its normalized
interchange components form a natural transformation by a proved biproduct argument:
the difference of two arrows with equal normalized restrictions gives an off-diagonal
endomorphism of A ⊞ B; uniqueness of the normalized component forces that block to vanish.

Zero holes added; zero holes remain in the four delivered Lean modules. The coefficient
provider has zero holes before and after its actual repair. Existing declared dependencies
retain their own outstanding proofs, as intended by this stage. The identity-refinement
lemma is existing B3 work, not a new node or a theorem delivered by this packet.

## No longer needed

Removed proof imports from the parent:

- WeilConjectures.Compactification.Dense
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
- Sheaf.Paper.CartesianCoefficients
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
- Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
- Sheaf.Paper.DerivedDirectImageOpenCoherence
- Sheaf.Paper.OpenImmersionLocalizing
- Sheaf.Paper.ProEtaleProperOpenInterchange
- Sheaf.Paper.CompactificationRefinementLocalizing
- Sheaf.Compactification.CommonDenseRefinement
- Sheaf.Compactification.DenseRefinementMorphisms
- Sheaf.Paper.InterchangeProperPasting
- Sheaf.Compactification.BoundaryRefinement

The model retains Nagata, open preservation, proper/open interchange and derived
open/direct-image coherence as proof imports. The independent refinement-pasting argument
is unnecessary: the existing cocycles transport one model directly. Thus
lem-sfb-interchange-proper-pasting and Sheaf.Paper.InterchangeProperPasting are pruned
from this route. Other original dependencies remain below the model or existing cocycle,
rather than as direct parent proof dependencies. No unit statement or realized step is
removed; sk-cor-affine-space-rational has empty realized lists.

## Where the brief, the DAG or earlier work was wrong

The original admissible coefficient predicate omitted the finite-subextension-valued
coefficient explicitly required by the assigned theorem. Replacing its continuous-map case
would break the existing RationalExceptionalRestriction proof and change its interface.
This delivery adds the missing case separately and preserves the legacy continuous case.
No identification of the two condensed rings is claimed. The generic admissibility
hypotheses now include the intended coefficient; targets keep their explicit coefficient
objects and unchanged conclusions. The definition repair requires independent review.

The original seven-step route proves more auxiliary-choice normalization than this
existence theorem needs. A single-model construction followed by cocycle transport suffices
for its actual refinement equation. No extra open normalization or associativity is claimed.

The retained report described a fifth delivered module and a second new node for the
identity-refinement law. That result has since landed as B3's
lem-sfb-compactification-refinement-component-id in
Sheaf.Paper.CompactificationRefinementIdentity. This packet imports that existing result
unchanged and adds only the model node.

The resumed downstream scan inventories 372 transitive importers and 27 other direct
predicate consumers in the change record. Newly landed nonrational composition proofs
select unchanged finite/integral branches and need no adaptation. Both the repaired
provider and the adapted consumer are currently unclaimed.

## New nodes

lem-sfb-localizing-lower-shriek-composition-model isolates the source's single-model
construction, with ambient target and no refinement compatibility. It is proved in full.
Empty schemes and identity morphisms are included; the compactification and interchange
hypotheses do not exclude them. This is strictly part of the argument: the parent's
preservation, transport, cocycle and canonical-refinement calculations remain substantive.

## Forced adaptations

The original Sheaf.Paper.RationalExceptionalRestriction fails against the repaired
coefficient provider at its construction of hadmissible: application type mismatch in
Or.inr hQ. The original hQ is an isomorphism to the continuous-map coefficient, while
the last branch now expects the disjunction of the continuous-map and finite-subextension
coefficients. Wrapping hQ in Or.inl selects its unchanged original branch. This is the
only changed proof line; all signatures, visibility, imports and other lines are identical.
The module is unclaimed. The changed consumer compiles in the delivered set.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
