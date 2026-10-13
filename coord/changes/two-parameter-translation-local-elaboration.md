# AlgebraicGeometry.GrpObj.twoParameterRightTranslation_commutator_app

## Reason

The proof uses local elaboration commands for its private cartesian lifts and section-map
calculations. The static interface checker treats additions of `omit` and local `attribute`
commands as changes to what importers see. This record documents their actual scope: no existing
public declaration, visibility, instance, or definition changes. The file-level transparency
option controls elaboration in this file and is not imported. The irreducibility registration
is explicitly local and applies only to the newly added private lift. `omit` removes the group
instance from private helpers that do not use it. The heartbeat option applies to one private
lemma, with its reason documented next to it.

The added private lift is a concrete construction using two existing, proved pullback universal
properties. It does not choose an arbitrary existence witness or introduce an axiom.

## Old

The original module has no transparency, irreducibility, or heartbeat commands. Its section
context is verbatim:

```lean
@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]
```

All existing public signatures and definitions are unchanged by this delivery.

## New

The original section context remains. The additional elaboration commands are:

```lean
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] liftedTwoParameterTranslation

omit [GrpObj G] in

set_option maxHeartbeats 800000 in
```

The `omit` commands each precede a proved private theorem. The locally irreducible private lift
is used through its proved projection and parameter equations after its geometric construction.
The local heartbeat command precedes `double_parameters`. No command registers an exported
instance, notation, or simplification theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GroupScheme.MixedTranslationCoefficients | unclaimed | Direct importer; existing signatures and definitions remain identical, so no adaptation is necessary. |

All further importers inherit the same public interface. No downstream module is edited or
requires a forced adaptation. The target statements and the meanings of their definitions
remain unchanged.

## Status

landed 20261013T123547-L-3711979 2026-10-13 (merge of deliver/M4/Sheaf.AlgebraicGeometry.GroupScheme.TwoParameterTranslationAction)
