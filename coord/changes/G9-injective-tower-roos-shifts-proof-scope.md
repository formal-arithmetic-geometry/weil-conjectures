# CategoryTheory.injectiveTowerRoosShifts

## Reason

The complete proof needs private generic helpers for limits, coherent product and
signed-cocone shifts, injective towers and localization. The static preflight
classifies the added namespace, variable and local-attribute commands as an
interface change, so this record documents their scope. No existing public
signature, definition, public import or attribute is changed. No other module is
modified. In particular the public theorem statement is byte-identical to the
original and all four public constructions retain their original bodies.

The first preflight also identified `baseLimit_additive` as a new global
instance. It is now a proved private lemma registered with `[local instance]`
only inside `section LimitModel`. All other new instance registrations and
irreducibility attributes are likewise local and apply only to new private
helpers. There is no new global instance or attribute on an imported declaration.

## Old

The original proof scope before the four public constructions was:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a b w uC vC r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
```

After `end CategoryTheory.InjectiveTowerRoos`, the original file opened
`namespace CategoryTheory` for the public theorem, whose proof was `by sorry`.
It had no generic private helpers, their local attributes, or additive-limit
instance. The original public theorem statement and four public definitions are
retained verbatim in this delivery.

## New

The corresponding proof scope is:

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a b w uC vC r u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex
```

Inside `namespace CategoryTheory`, the additive-limit construction starts with:

```lean
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

section LimitModel
variable [HasLimitsOfShape ℕᵒᵖ A]

omit [HasCountableProducts A] in
private lemma baseLimit_additive : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro n
  simp [lim_map]

attribute [local instance] baseLimit_additive
```

The remaining additions are proved private helpers in this namespace. Their
local instances provide only the chosen shift structures and compatibility
proofs while elaborating this file; local irreducibility attributes keep
coordinate constructions from unfolding during those proofs. The elaboration
options affect proof elaboration only. The completed theorem uses these helpers
without changing its statement or introducing holes.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.InjectiveTowerRoosShifts
--uses injectiveTowerRoosShifts` reports zero downstream modules and only the
item's own occurrence of the theorem name. No consumer adaptation is necessary.
The node's existing statement dependencies and its parent attachments remain;
this is a proof completion, not a withdrawal.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.InjectiveTowerRoosShifts` | G9 | Complete its one theorem proof; private helper scope only; original public interface retained. |

## Status

landed 20261021T160330-L-3589250 2026-10-21 (merge of deliver/G9/Sheaf.CategoryTheory.InjectiveTowerRoosShifts)
