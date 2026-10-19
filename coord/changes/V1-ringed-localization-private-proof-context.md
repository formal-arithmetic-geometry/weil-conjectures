# CategoryTheory.RingedLocalizationComparison

## Reason

The independent-universe module comparison needs a private construction of multiplication
on additive sheafification. Its private helpers use a nested namespace and locally scoped
elaboration options. The interface scanner records the added `variable` and `set_option`
commands even though their enclosing section ends before the existing comparison theorem.
This record documents that command-level change for independent review.

## Old

There was no helper section between `ringedLocalizationRingUnitOfUniverses` and
`ringedLocalizationRing_moduleComparisonOfUniverses`. The existing surrounding variables are:

```lean
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (s : (R.obj ⋙ forget CommRingCat).sections)
```

## New

The old surrounding variables remain verbatim. The new private-helper context begins:

```lean
section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

namespace RingedLocalizationComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {P : Cᵒᵖ ⥤ CommRingCat.{u}} {A : Sheaf J AddCommGrpCat.{u}}
variable (η : (P ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶ A.obj)
variable [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]
```

Before the private module comparison helper it adds:

```lean
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
```

The helper context ends before the existing public comparison theorem:

```lean
end RingedLocalizationComparison

end
```

Every added declaration is private. The public comparison theorem scopes its two
elaboration options inside its proof. The new Mathlib import is proof-only. No public
signature, existing definition body, public import, instance or notation changes.
The private `ring` definition has `instance_reducible` for local instance elaboration;
it is installed only by `letI` within the private constructions.

## Users

`tools/downstream.py Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses --direct`
lists the five direct importers below. Its transitive query lists 911 modules. Each
transitive user receives the same public interface through these importers, so no
consumer adaptation is needed. The scanner's changed-command marker names no declaration
that a consumer can mention. All existing statements retain their meaning, including
the target statements; no target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.LocalizationInverseImageCoherence | C1 | Same public interface; no edit needed. |
| Sheaf.CategoryTheory.RingedPresentationTransport | W5 | Same public interface; no edit needed. |
| Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope | M6 | Same public interface; no edit needed. |
| Sheaf.Paper.RingedDerivedSliceLocalization | Q7 | Same public interface; no edit needed. |
| Sheaf.Paper.SmoothLisseIntegralLattice | unclaimed | Same public interface; no edit needed. |

## Status

landed 20261019T034320-L-420386 2026-10-19 (merge of deliver/V1/Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses)
