/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat

/-!
# Termwise derived pullback of a bounded-above flat complex

## References

* Stacks Project, Cohomology, Tags 06YD and 06YJ
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A bounded-above complex `K` of flat structure-sheaf modules computes its derived
pullback term by term: there is a functor `F` agreeing with `Scheme.Modules.tensorPullback`
on objects and maps, and an isomorphism `e` from the ordinary to the derived pullback whose
inverse is the left-derived counit `ε` at `K` (Stacks, Tags 06YD and 06YJ). -/
theorem flatComplexDerivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) :
    ∃ (F : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings T.toRingedSpace))
      (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
      (_ : ∀ {M N} (a : M ⟶ N),
        F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
          eqToHom (hF N).symm)
      (_ : F.Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      (derivedPullback g).IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) ∧
        ∃ e : DerivedCategory.Qh.obj
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≅
            (derivedPullback g).obj
              (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)),
          e.inv = ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hderived, htri, hε⟩ :=
    (derivedPullback_spec g)
  refine ⟨F, hF, hFmap, hFadd, ε, hderived, ?_⟩
  have hK := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    S.toRingedSpace K hbounded hflat
  have := hε K hK
  exact ⟨(asIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))).symm,
    rfl⟩

end AlgebraicGeometry
