/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Topology.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Conservativity of covering restrictions with condensed coefficients

The module-object presentation is the published category of modules over
`coefficientRing X Λ`, whose underlying ring object is `condensedRingObj Λ.X X`.
These are ordinary unbounded derived categories, with no completion.
`CondensedRing.upperStar` uses extension along the actual coefficient isomorphism
`condensedPullbackHom`. Its exact termwise derived functor is canonically the total
left derived inverse image by `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`.
For an object of the small pro-etale site, localization and the inverse-image
comparison identify this functor with restriction, transporting the coefficient action.

## References

* Hemo--Richarz--Scholbach, Section 3, Lemma 4.5
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem isIso_of_condensed_cover
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)}
    (f : M ⟶ N) (hf : ∀ i, IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).map f)) :
    IsIso f := by
  have hweak (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒰.mem₀) ⟨i⟩
  have : IsIso ((Mod.forget (condensedRingObj Λ.X X)).map f) := by
    apply isIso_of_isIso_localizationRestriction Ab.{u + 1} _ 𝒰.f 𝒰.mem₀
    intro i
    let e : CondensedRing.upperStar Λ.X (𝒰.f i) ⋙ Mod.forget _ ≅
        Mod.forget (condensedRingObj Λ.X X) ⋙ upperStar Ab.{u + 1} (𝒰.f i) :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          ((upperStar Ab.{u + 1} (𝒰.f i)).mapMod (condensedRingObj Λ.X X))
          (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X (𝒰.f i))))
        (Mod.forget _)
    have h := hf i
    have h' : IsIso ((upperStar Ab.{u + 1} (𝒰.f i)).map f.hom) :=
      (NatIso.isIso_map_iff e f).1 (by
        change IsIso ((Mod.forget _).map ((CondensedRing.upperStar Λ.X (𝒰.f i)).map f))
        infer_instance)
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) (hweak i)) f.hom).1 h'
  exact isIso_of_reflects_iso f (Mod.forget _)

/-- Derived restrictions along any pro-etale covering family jointly detect isomorphisms
and zero objects for arbitrary commutative condensed coefficients (HRS, Section 3 and
Lemma 4.5). -/
theorem condensed_cover_restriction_conservative
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X) :
    (∀ (K L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
        (f : K ⟶ L),
      IsIso f ↔ ∀ i : 𝒰.I₀,
        IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)),
      (∀ i : 𝒰.I₀,
        IsZero ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.obj K)) →
      IsZero K) := by
  have hIso {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))}
      (f : K ⟶ L)
      (hf : ∀ i, IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f)) :
      IsIso f := by
    rw [DerivedCategory.isIso_iff]
    intro n
    apply isIso_of_condensed_cover Λ X 𝒰
    intro i
    exact (NatIso.isIso_map_iff
      ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategoryHomologyFunctorIso n) f).2
      (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f))
        have := hf i
        infer_instance)
  constructor
  · intro K L f
    exact ⟨fun _ i ↦ inferInstance, fun hf ↦ hIso f hf⟩
  · intro K hK
    open ZeroObject in
    have h : IsIso (0 : K ⟶ 0) := hIso _ fun i ↦
      (hK i).isIso
        ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map_isZero
          (isZero_zero _)) _
    exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

end AlgebraicGeometry.ProEtale
