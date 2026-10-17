# residueOrdinaryRestrictedRegularPullIso

## Reason

The returned delivery failed after the upstream source synchronization. Recompiling the
retained scalar and tensor-counit statements isolated the large inline ordinary coefficient
isomorphism, particularly specialization of the monoidal unit to the integral residue ring.
Construct the same isomorphism once at arbitrary condensed coefficients, then refer to it
by name. This is an actual elaboration repair; the bridge proof is not merely rebased.
The repaired three-module fallback compiled against the current source before further
proof work on the counit identities.

The two counit modules are new relative to the current shared branch. This record documents
the change from the retained returned delivery, rather than changing a landed signature.

## Old

Both retained counit statements constructed their local `e` inline:

```lean
    let e : F.obj B ≅ B' :=
      (comapUpperStarIso (integralReductionMap ℓ E) f).symm.app
        (Mod.regular (condensedRingObj A Y)) ≪≫
          SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
```

Here `A` is the residue coefficient, `SX` is restriction on X, and the statement
installs `residueOrdinaryUpperStarMonoidal A f` before this expression.

## New

```lean
@[irreducible] noncomputable def residueOrdinaryRestrictedRegularPullIso
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*⟦Λ⟧.obj
        ((Mod.comap (coefficientMap φ Y)).obj (Mod.regular (condensedRingObj A Y))) ≅
      (Mod.comap (coefficientMap φ X)).obj (Mod.regular (condensedRingObj A X)) := by
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  letI := residueOrdinaryUpperStarMonoidal A f
  exact (comapUpperStarIso φ f).symm.app (Mod.regular (condensedRingObj A Y)) ≪≫
    SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
```

Both local coefficient identifications now use:

```lean
    let e : F.obj B ≅ B' :=
      residueOrdinaryRestrictedRegularPullIso (integralCoeff ℓ E) A
        (integralReductionMap ℓ E) f
```

The local pullback counit `a` also uses the existing typed interface directly.
The retained version was:

```lean
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) := by
      unfold residueExchangeUpperStar
      exact F.leftDerivedFunctorCounit.app P
```

It is now:

```lean
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
      (residueExchangeUpperStarCounit (integralCoeff ℓ E) f).app P
```

The existing definition of `residueExchangeUpperStarCounit` is exactly the old
`unfold`/`exact` construction, uniformly in the condensed coefficient. Thus this
uses the same map with its domain already exposed by the library's interface.

Unfolding the new definition gives precisely the old composite. Its two factors are
constructed isomorphisms already in the library, so no data are chosen from an existence
statement and no new proof assumption enters its data. In particular the coefficient's
unit map, its inverse and the restriction/pullback orientation are unchanged. Zero
modules and the identity scheme morphism use the same construction without extra
hypotheses. No existing target declaration or target definition is modified.

## Users

`tools/downstream.py` on both new counit modules, with the three relevant declaration
names and `--allow-missing`, reports zero users in the current shared source. The complete
new consumers in this delivery are listed below. No other group's module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueScalarCounitModel | A2, new delivery module | Constructs the ordinary coefficient isomorphism and uses it as its local `e`; proposition unchanged by unfolding. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | A2, new delivery module | Uses the same named `e`; proposition unchanged by unfolding. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | A2 | Original signature unchanged; its proof combines the two counit identities exactly as before. |

## Status

landed 20261017T024325-L-1172589 2026-10-17 (merge of deliver/A2/Sheaf.Paper.IntegralResidueScalarGeometryBridge)
