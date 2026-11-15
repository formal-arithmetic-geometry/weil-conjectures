/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforwardPerfectComponent
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforwardLocalComparisons
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionIsIsoOpenCover

/-! # Perfect pushforward and canonical maps for supported open inclusions

## References

* Stacks Project, Tags 08DP and 08DF.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Let `j = U.ι` be an open immersion and `T ⊆ U` closed in `X`; "supported on `T`" means all
cohomology stalks vanish off `T`. A perfect `F` on `U` supported on `T` has perfect `Rj_*F`; for
`E` on `X` supported on `T` the unit `E → Rj_*(E|_U)` is invertible; and for such perfect `F`
the canonical map `j_!F → Rj_*F` (a map whose adjunct is left inverse to the unit
`F → (j_!F)|_U`) is invertible. -/
theorem supported_open_pushforward (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    (∀ F : schemeDerivedCategory U.toScheme, IsPerfect U.toScheme F →
      (∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf
            x))) →
      IsPerfect X ((schemeDerivedDirectImage U.ι).obj F)) ∧
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (E : schemeDerivedCategory X),
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x))) →
      IsIso (adj.unit.app E)) ∧
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (S : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
        (adjS : S ⊣ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory)
        (F : schemeDerivedCategory U.toScheme), IsPerfect U.toScheme F →
      (∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf
            x))) →
      ∀ φ : S.obj F ⟶ (schemeDerivedDirectImage U.ι).obj F,
        adjS.unit.app F ≫ (adj.homEquiv (S.obj F) F).symm φ = 𝟙 F → IsIso φ) := by
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  have hcover : U ⊔ V = ⊤ := by
    ext x
    change (x ∈ U ∨ x ∈ Tᶜ) ↔ x ∈ (Set.univ : Set X)
    simp only [Set.mem_univ, iff_true]
    by_cases hx : x ∈ T
    · exact Or.inl (hTU hx)
    · exact Or.inr hx
  obtain ⟨hunit, hcanonical⟩ :=
    supported_open_pushforward_local_comparisons X U T hT V rfl
  refine ⟨supported_open_pushforward_perfect X U T hT hTU, ?_, ?_⟩
  · intro adj E hE
    exact derived_restriction_isIso_open_cover X U V hcover (adj.unit.app E)
      (hunit adj E hE U (Or.inl rfl)) (hunit adj E hE V (Or.inr rfl))
  · intro adj S adjS F hF hsupport φ hφ
    exact derived_restriction_isIso_open_cover X U V hcover φ
      (hcanonical adj S adjS F hsupport φ hφ U (Or.inl rfl))
      (hcanonical adj S adjS F hsupport φ hφ V (Or.inr rfl))

end AlgebraicGeometry.Scheme
