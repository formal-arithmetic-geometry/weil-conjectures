# AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerStarOfPreserves

## Reason

Restore the quarantined module assigned in coord/rework.tsv, row for
Sheaf.Paper.BoundedConstructiblePushforwardRestriction. The cluster restore removed
its live source, while preserving its complete construction in quarantine and its
Lean attachment on sk-def-sfb-dc-restricted-functors. This delivery restores that
source verbatim. It changes no archived signature, definition, import or attribute.

## Old

The live path lean/Sheaf/Paper/BoundedConstructiblePushforwardRestriction.lean is absent.
The source preserved at quarantine/Sheaf/Paper/BoundedConstructiblePushforwardRestriction.lean
is reproduced verbatim below. No archived declaration is replaced or withdrawn.

## New

Restore lean/Sheaf/Paper/BoundedConstructiblePushforwardRestriction.lean with exactly:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Restricted pushforward under its preservation hypothesis

Source: the blueprint, `sec-six-functors-basics`, restriction paragraph of
`sk-def-sfb-dc-restricted-functors` (blueprint: sk-def-sfb-dc-restricted-functors).

The imported module supplies all the restricted operations and their structural maps for
its named coefficient classes. Here the same restriction and restricted adjunction are
constructed from preservation itself, allowing arbitrary commutative condensed coefficients.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Preservation by every derived pushforward between separated finite-type `k`-schemes.
This is precisely the conditional hypothesis in the blueprint restriction paragraph,
not a restriction to one of its example coefficient rings.
Source: blueprint `sk-def-sfb-dc-restricted-functors`
(blueprint: sk-def-sfb-dc-restricted-functors). -/
def PreservesBoundedConstructiblePushforwards (k : Type u) [Field k] : Prop :=
  ∀ {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (K : ProEtale.BoundedConstructible (condensedRingObj Λ X.left)),
    boundedConstructible (condensedRingObj Λ Y.left) ((R((f.left)_*⟦Λ⟧)).obj K.obj)

variable {k : Type u} [Field k]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (H : PreservesBoundedConstructiblePushforwards Λ k) (f : X ⟶ Y)

/-- Restrict the ambient derived pushforward, using the stated preservation hypothesis.
Its object and morphism data are those of the ambient functor, with only the object property
supplied by `H`. Source: blueprint restriction paragraph
(blueprint: sk-def-sfb-dc-restricted-functors). -/
noncomputable def boundedConstructibleLowerStarOfPreserves :
    ProEtale.BoundedConstructible (condensedRingObj Λ X.left) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ Y.left) :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧))
    (fun K ↦ H f K)

/-- The conditional restriction commutes with the fully faithful inclusions.
Source: blueprint restriction paragraph (blueprint: sk-def-sfb-dc-restricted-functors). -/
noncomputable def boundedConstructibleLowerStarOfPreservesCompatibility :
    boundedConstructibleLowerStarOfPreserves Λ H f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- Restrict the actual ambient derived pullback--pushforward adjunction along the fully
faithful inclusions; thus its unit and counit are the restricted ambient unit and counit.
Source: blueprint adjunction paragraph (blueprint: sk-def-sfb-dc-restricted-functors). -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves :
    boundedConstructibleUpperStar Λ ℓ f ⊣ boundedConstructibleLowerStarOfPreserves Λ H f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (boundedConstructibleLowerStarOfPreservesCompatibility Λ H f).symm

end AlgebraicGeometry.ProEtale.CondensedRing
```

## Users

The source-only downstream.py --allow-missing check reports zero current live
importers and zero live uses of each of the four restored declarations. An rg
check of quarantine additionally finds the consumers below, which must be kept
in the restoration assessment; absence of live importers is not withdrawal evidence.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Archived direct public importer; its unchanged source compiles against the restored module. Unit, square and counit construction retains exactly its former meaning. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Archived consumer of the global preservation predicate; its quantified hypothesis and finiteness-coefficient specializations retain their former meaning. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Archived proof importer; no restored name occurs in its body and no adaptation is required. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Archived proof importer; no restored name occurs in its body and no adaptation is required. |

No consumer is edited or delivered. No target statement or definition is changed;
the restoration preserves the existing node attachment, all dependency edges and
the unit route. Independent review is supplied by the normal delivery workflow.

## Status

landed 20261021T014215-L-2387048 2026-10-21 (merge of deliver/E3/Sheaf.Paper.BoundedConstructiblePushforwardRestriction)
