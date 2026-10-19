# AlgebraicGeometry.ProEtale.CondensedRing.unboundedBaseChangeExtension

## Reason

The static preflight flags the added universe names and local instance registration as
changed commands. They support private proved helpers for localizing determination and
shift compatibility. The theorem signature, its universe parameters, both existing
public definition bodies, and all public imports stay identical. No consumer needs
adaptation. The shift registration is local to this file and exports no new instance.

## Old

The existing commands were:

```lean
universe u
```

There was no local registration of `unboundedLocalizingPullbackCommShift` in this file.
The unchanged theorem signature and both definitions are in the delivered module; only
the theorem's `by sorry` body is replaced.

## New

```lean
universe u v u' v'

attribute [local instance] unboundedLocalizingPullbackCommShift
```

Only the new generic private helper uses `v`, `u'`, and `v'`; no existing declaration
acquires an extra universe. The local instance selects the canonical pullback shifts
already defined by the existing pullback module. The compatible shifts on the right
adjoints are local `let` instances inside the private proof. No public declaration
signature, definition, notation, global attribute, or imported instance changes.

## Users

`tools/downstream.py Sheaf.Paper.UnboundedBaseChangeExtension --uses
termwiseCondensedAmbientExchange UnboundedBaseChangeExtension unboundedBaseChangeExtension`
found 39 downstream modules. The two apparent downstream declaration hits are module
import lines in `IntegralLocalizingProperBaseChange` and `DetSfCompCompositionBaseChange`;
neither currently applies a declaration of this module. All downstream modules keep
identical visible signatures and definitions. The full set is listed below; holder
names are the claims at the time this record was written.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Proof completed; existing signatures and definition bodies identical. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Unchanged interface; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Unchanged interface; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Unchanged interface; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Unchanged interface; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Unchanged interface; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged interface; no adaptation. |
| TargetsCheck | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged interface; no adaptation. |

No target statement or definition used by a target changes; target meaning is unchanged.
No module held by another group is edited, and no forced adaptation is included.
The only mathematical change is a proof of the existing theorem from already stated
proper-image and pullback preservation theorems.

## Status

landed 20261019T005312-L-2750583 2026-10-19 (merge of deliver/K3/Sheaf.Paper.UnboundedBaseChangeExtension)
