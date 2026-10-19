# SheafOfModules.preservesColimits_specifiedChangeOfRings

## Reason

Expose the colimit-preservation consequence of the existing private scalar tensor/restriction adjunction, so the continuity argument can reuse that construction. No existing declaration changes.

## Old

No public colimit-preservation theorem for the specified scalar-extension functor. The existing private tensorFunctor and tensorAdjunction remain unchanged.

## New

```lean
/-- Extension of scalars, specified on both objects and maps, preserves colimits.
Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EP.
The tensor/restriction adjunction gives preservation for its tensor functor;
the two specifications give a natural isomorphism to E.
(blueprint: lem-weil-pbc-ringed-topos-pullback-filtered-colimits). -/
theorem preservesColimits_specifiedChangeOfRings
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
    {K : GrothendieckTopology D} {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (E : SheafOfModules.{w} ((sheafCompose K
        (forget₂ CommRingCat.{w} RingCat.{w})).obj A) ⥤
      SheafOfModules.{w} ((sheafCompose K
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M, E.obj M = changeOfRings.{vD, uD, w} c M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hobj M) ≫
      changeOfRingsHom.{vD, uD, w} c M f ≫ eqToHom (hobj N).symm) :
    PreservesColimitsOfSize.{0, 0} E := by
  have : PreservesColimitsOfSize.{0, 0} (tensorFunctor c) :=
    (tensorAdjunction c).leftAdjoint_preservesColimits
  let e : tensorFunctor c ≅ E := NatIso.ofComponents
    (fun M ↦ eqToIso (hobj M).symm) (by
      intro M N f
      change changeOfRingsHom c M f ≫ eqToHom (hobj N).symm =
        eqToHom (hobj M).symm ≫ E.map f
      rw [hmap]
      simp)
  exact preservesColimits_of_natIso e

```

## Users

No existing declaration uses this new name. The downstream uses search has no existing caller. The new theorem uses the existing adjunction internally, so no private definition occurs in a public signature or public definition body.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedToposPullbackFilteredColimits | unclaimed | Add proved consequence; all existing declarations unchanged. |
| Sheaf.Algebra.Homology.DerivedScalarTruncationContinuity | A5 | Use preservation of the resolution colimit. |

## Status

landed 20261019T002457-L-2139002 2026-10-19 (merge of deliver/A5/Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds)
