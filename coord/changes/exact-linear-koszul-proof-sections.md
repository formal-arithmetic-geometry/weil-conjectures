# CategoryTheory.exists_exactLinear_signedKoszulFibre

## Reason

The proof introduces the namespace `SignedKoszulComparisonAux`, private proved helpers,
local section variables, helper universes and section-scoped elaboration options.
The stage-3 static surface check requires a change record for these added commands.
They support the matrix/projection and localization proofs. Every existing public
structure, abbreviation and theorem signature is verbatim unchanged; the target
statements and the definitions they use retain their meanings.

## Old

Immediately after the existing `ExactLinearSignedKoszulFibreComparison` abbreviation,
the file proceeds directly to the docstring and statement of
`exists_exactLinear_signedKoszulFibre`. There are no intervening proof-helper commands.
The old theorem declaration is verbatim:

```lean
theorem exists_exactLinear_signedKoszulFibre
    {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    {J : GrothendieckTopology C} {L : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf L CommRingCat.{v})
    {A : Type z} [CommRing A]
    (ρR : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (ρS : A →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{wR} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    [HasCountableProducts (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasCountableProducts (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    [CountableAB4Star (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [CountableAB4Star (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{v} ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hlinear : ∀ {M N : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (b : A) (f : M ⟶ N),
      F.map (ringedKoszulCoefficientSMul R ρR b f) =
        ringedKoszulCoefficientSMul S ρS b (F.map f))
    (hproduct : ∀ M : ℕ → ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      IsIso (piComparison F M))
    (r : ℕ) (a : Fin r → A) :
    Nonempty (RingedSignedKoszulCompletionModel R ρR a) ∧
    Nonempty (RingedSignedKoszulCompletionModel S ρS a) ∧
    ∀ (MR : RingedSignedKoszulCompletionModel R ρR a)
      (MS : RingedSignedKoszulCompletionModel S ρS a),
    Nonempty (ExactLinearSignedKoszulFibreComparison R S ρR ρS F MR MS) := by
  sorry
```

## New

The intervening proof-helper section begins verbatim:

```lean
namespace SignedKoszulComparisonAux

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe cu cv du dv cw dw

section ChainComparison

variable {E : Type cu} [Category.{cv} E] [Abelian E]
  {D : Type du} [Category.{dv} D] [Abelian D]
  [HasFiniteBiproducts E] [HasFiniteBiproducts D]
variable (F : E ⥤ D) [F.Additive]
```

It contains only private definitions and proved private theorems, with additional
section variables for their parameters. `ChainComparison`, `DerivedComparison`,
the noncomputable section and the namespace all end before the original theorem.
There is no new notation, global instance or public helper declaration. The new
proof imports are private. The theorem's new body constructs both models, compares
finite tensors, products and fibres, and descends the comparison through localization.

The new public theorem signature is verbatim:

```lean
theorem exists_exactLinear_signedKoszulFibre
    {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    {J : GrothendieckTopology C} {L : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf L CommRingCat.{v})
    {A : Type z} [CommRing A]
    (ρR : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (ρS : A →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{wR} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    [HasCountableProducts (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasCountableProducts (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    [CountableAB4Star (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [CountableAB4Star (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{v} ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hlinear : ∀ {M N : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (b : A) (f : M ⟶ N),
      F.map (ringedKoszulCoefficientSMul R ρR b f) =
        ringedKoszulCoefficientSMul S ρS b (F.map f))
    (hproduct : ∀ M : ℕ → ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      IsIso (piComparison F M))
    (r : ℕ) (a : Fin r → A) :
    Nonempty (RingedSignedKoszulCompletionModel R ρR a) ∧
    Nonempty (RingedSignedKoszulCompletionModel S ρS a) ∧
    ∀ (MR : RingedSignedKoszulCompletionModel R ρR a)
      (MS : RingedSignedKoszulCompletionModel S ρS a),
    Nonempty (ExactLinearSignedKoszulFibreComparison R S ρR ρS F MR MS)
```

## Users

A repository-wide Lean search finds no other current module importing this item or
using its three public declarations. `tools/downstream.py` was also run for
`exists_exactLinear_signedKoszulFibre`. Parent DAG proofs may still need this item;
its module and all three public declarations are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ExactLinearKoszulFibre | M1 | Only private proof infrastructure and theorem proof change; all public signatures are unchanged. |

No existing consumer requires adaptation. No other group's module is included.

## Status

landed 20261021T140839-L-2761445 2026-10-21 (merge of deliver/M1/Sheaf.CategoryTheory.ExactLinearKoszulFibre)
