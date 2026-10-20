## What changed

Marked the existing source instance
`AlgebraicGeometry.ProEtale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`
as `STATEMENT-DISPUTED`. The current source lacks the marker described by the earlier G9 report.
Every original declaration, signature, proof body, attribute, and import is preserved.
Updated the existing node's proof and proof origin to record the independent C9 verification.

This is a disputed-statement delivery. The assertion is false; this delivery does not claim
to prove it, repair its mathematical statement, or decompose it into unproved lemmas.

## Proved and sorry left

Holes closed: 0 of 1. Holes added: 0. Split off: 0.
The original hole remains in
`AlgebraicGeometry.ProEtale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`
(node `thm-sfb-finite-proper-pushforward-left-adjoint`).

Independently compiled the following sandbox-only probe, with no warnings.
It proves the negation of the instance's exact conclusion for a positive dimensional
abelian variety, and confirms that its structure morphism satisfies `IsProper`.
Its axiom audit is exactly `[propext, Classical.choice, Quot.sound]`.
The probe is not a delivered library declaration and uses no legacy instance to derive False.

```lean
module

public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

theorem assignedProperAdjointCounterexample (Λ : Type (u + 1)) [Field Λ]
    {k : Type u} [Field k] [IsAlgClosed k]
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ ((E.hom)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.IsLeftAdjoint := by
  intro h
  let := h
  exact not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety Λ E hE
    inferInstance

example (Λ : Type (u + 1)) [Field Λ]
    {k : Type u} [Field k] [IsAlgClosed k]
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E] : IsProper E.hom :=
  inferInstance

#print axioms assignedProperAdjointCounterexample

end AlgebraicGeometry.ProEtale
```

## No longer needed

None. No declaration, module, node, dependency, or import is withdrawn.
Brown representability cannot prove the assigned statement because its required coproduct
preservation fails. The historical F3 withdrawal is not repeated.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the assigned unconditional ambient adjoint assertion is false, as stated
in the current blueprint `sk-rem-sf-fullcd-scope`, "The counterexample and the repair boundary".
The exact negation follows from the existing coproduct counterexample and Mathlib's instance
that left adjoints preserve colimits of every shape. Module categories over fields satisfy
the assigned Grothendieck abelian hypotheses; the probe also checks the geometric hypothesis.

Read the assigned node, its two statement dependencies, the unit record and the active
`Derived.UpperShriek` interface. The node already records the counterexample, and its proof
dependency list is empty. There is no positive proof plan to implement. LeanFinder independently
found `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`; searches of both
library roots confirm the counterexample theorem and the separate constructible adjunction.

The source-library boundary prohibits changing or deleting this instance, and
`coord/upstream-statement-exceptions.tsv` contains no exception for this module. Thus a
corrected positive theorem or retirement requires maintainer resolution. The unit realized
arrays are empty, and no unit step is bypassed.

The counterexample module already transitively imports the assigned source module, as checked
by `tools/import_direction.py may`. Importing it into the assigned module would create a cycle;
the checked probe is therefore reproduced here rather than added as an unused proof import.
No statement, definition, visibility, or import changes, so no change record is required.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
