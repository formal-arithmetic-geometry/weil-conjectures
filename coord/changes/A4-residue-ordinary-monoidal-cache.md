# AlgebraicGeometry.ProEtale.CondensedRing.residueOrdinaryUpperStarMonoidal

## Reason

Concrete comparison proofs expand the complete transported ordinary monoidal structure.
Cache that same constructed structure using non-exposure and irreducibility, and prove its
defining equation for the ordinary braiding calculation. The construction body, existing
signatures and visibility are unchanged. The module is unclaimed. Target definition review
is reopened for maintainer verification that all data are the same.

## Old

```lean
@[instance_reducible] noncomputable def residueOrdinaryUpperStarMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (f)^*⟦Λ⟧.Monoidal := by
  let G := (f)^*[Ab.{u + 1}]
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  letI : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  exact Functor.Monoidal.transport
    (Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).symm
```

## New

```lean
@[no_expose, irreducible] noncomputable def residueOrdinaryUpperStarMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (f)^*⟦Λ⟧.Monoidal := by
  let G := (f)^*[Ab.{u + 1}]
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  letI : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  exact Functor.Monoidal.transport
    (Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).symm

/-- The cached ordinary pullback structure is the original transported structure.
Source: the balanced internal-module tensor construction.
(blueprint: new-integral-residue-ordinary-monoidal)
Proof. Both sides are the identical explicit construction. -/
theorem residueOrdinaryUpperStarMonoidal_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueOrdinaryUpperStarMonoidal Λ f = (by
  let G := (f)^*[Ab.{u + 1}]
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  letI : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  exact Functor.Monoidal.transport
    (Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).symm) := by
  unfold residueOrdinaryUpperStarMonoidal
  rfl
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralResidueOrdinaryMonoidal | unclaimed | Cache the same structure and prove its defining equation. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | A4 | Use the defining equation for the ordinary braiding calculation. |

The integral specialization retains its existing body. All derived constructions still use
exactly this ordinary structure, with unchanged mathematical statements and data. No other
module directly unfolds this generic ordinary structure. No consumer adaptation is required.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralResidueOrdinaryTensorSquare | unclaimed | Same construction data and existing statement; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | unclaimed | Its normalization unfolds the cached ordinary monoidal structure; statement and data unchanged. |

| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | Same construction data and existing statement; no adaptation. |

## Status

landed 20261017T144415-L-4152973 2026-10-17 (merge of deliver/A4/Sheaf.Paper.IntegralResidueTensorRouteModel)
