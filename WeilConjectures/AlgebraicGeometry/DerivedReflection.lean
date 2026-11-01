/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiDerivedData
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The normalized derived comparison is invertible after the absolute derived-unit reflection.
This is the reflection step of Steps 3--5: identify both endpoints on affine étale objects and
reflect the isomorphism through exact change of topology.
Source: Stacks 03DW, 0736 (blueprint: lem-fd-relative-etale-derived-reflection). -/
theorem relative_derived_comparison_isIso
    {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext f)
    (F : X.Modules) [F.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f] :
    IsIso (RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.arrow c F) := by
  sorry
/-- The normalized derived comparison is natural in coefficient maps. This is the mate and
coefficient-counit naturality part of Step 6, separated from invertibility.
Source: Stacks 0736 (blueprint: lem-fd-relative-etale-derived-naturality). -/
theorem relative_derived_comparison_natural
    {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext f)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (g : F ⟶ G) :
    (RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.targetDerived c).map
        ((pushforward f).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map g)) ≫
      RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.arrow c G =
    RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.arrow c F ≫
      (Etale.lowerStar AddCommGrpCat.{u+1} f).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor
          (RelativeEtaleZariskiDerivedData.RelativeEtaleAbelianSheaves X) 0).map
            ((c.source.extension ⋙
              RelativeEtaleZariskiDerivedData.relativeEtaleForgetModules X).map g)) := by
  sorry
end AlgebraicGeometry.Scheme.Modules
