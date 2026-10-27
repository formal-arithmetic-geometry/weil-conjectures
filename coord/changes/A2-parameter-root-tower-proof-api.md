# Parameter-root tower proof API

## Reason

Complete the assigned punctured tower theorem by explicit constructions and proved algebraic
lemmas. The new helper modules group the finite monic quotient calculation, compatible-root
colimit, localization, and categorical colimit assembly. The original theorem signature,
four original definition bodies, public imports, and target statements are unchanged.

## Old

The original theorem `AlgebraicGeometry.parameterRoot_punctured_cover_tower` had proof
`:= by sorry`. The five helper modules did not exist. The original module imported the
planned general directed-colimit and universe-transport interfaces privately.

## New

The theorem has a complete proof with explicit transitions and inclusions. New modules are:

- `Sheaf.RingTheory.ParameterRootAlgebra`: reuses the existing `Algebra.pthRootAlgebra`
  through an abbreviation; proves quotient evaluation, decomposition, monomial bases,
  refinement equivalences, faithful flatness and the degree-one/empty cases.
- `Sheaf.RingTheory.ParameterRootColimit`: constructs labelled root inclusions and proves
  the full quotient's colimit property; adds a divisibility-order wrapper and its
  directedness instances, including its universe lift.
- `Sheaf.RingTheory.LocalizationColimit`: constructs localized maps and proves the
  localized universal property directly from the original colimit property.
- `Sheaf.RingTheory.ParameterRootLocalization`: constructs the localization comparison,
  proves finite faithful flatness, and obtains etaleness from the stated unit-binomial lemma.
- `Sheaf.RingTheory.PresentedRingColimit`: constructs categorical diagrams/cocones from
  compatible maps, and uses the adopted source colimit APIs for faithful flatness and
  ind-etaleness, then preservation of limits by spectrum.

Each helper is fully proved. No arbitrary data is chosen from an unproved existence result.
The new definitions are explicit evaluation, quotient descent, localization lifts, inverse
maps checked on generators, and categorical diagrams of those maps. A local elaboration
option `backward.isDefEq.respectTransparency false` supports the definitionally equal
quotient presentations without changing any mathematical interface.

Private proof imports replace unused planned private imports in the assigned module.
The helper's exposed simp/ext lemmas and order instances are new and visible only to
modules that explicitly import those helpers; the assigned module imports them privately.
The same original public imports are retained verbatim.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ParameterRootPuncturedCoverTower
--uses parameterRoot_punctured_cover_tower` finds zero current downstream modules.
The pending DAG parents still need this item and are preserved. No existing module
imports any new helper, so no existing consumer requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ParameterRootPuncturedCoverTower | A2 | Proof completed; identical statement and definitions. |
| Sheaf.RingTheory.ParameterRootAlgebra | A2 new | Fully proved finite-quotient API. |
| Sheaf.RingTheory.ParameterRootColimit | A2 new | Fully proved compatible-root colimit API. |
| Sheaf.RingTheory.LocalizationColimit | A2 new | Fully proved localization colimit API. |
| Sheaf.RingTheory.ParameterRootLocalization | A2 new | Fully proved localized root API. |
| Sheaf.RingTheory.PresentedRingColimit | A2 new | Fully proved categorical colimit API. |

## Status

landed 20261023T134724-L-2738742 2026-10-23 (merge of deliver/A2/Sheaf.AlgebraicGeometry.ParameterRootPuncturedCoverTower)
