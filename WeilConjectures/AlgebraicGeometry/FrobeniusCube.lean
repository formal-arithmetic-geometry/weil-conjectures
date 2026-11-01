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
/-- The Frobenius scalar restriction exchange is invertible after deriving. This is the derived
cube-isomorphism part of Step 8.
Source: Stacks 0736 and 0EBS (blueprint: lem-fd-relative-etale-frobenius-cube-iso). -/
theorem relative_frobenius_cube_isIso
    {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext f) (p : ℕ)
    (x : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusTransport c.source p)
    (s : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusTransport c.target p)
    (r : pushforward f ⋙ RelativeEtaleZariskiDerivedData.relativeZariskiRestrictScalars S s.sigma ≅
      RelativeEtaleZariskiDerivedData.relativeZariskiRestrictScalars X x.sigma ⋙ pushforward f) :
    IsIso (RelativeEtaleZariskiDerivedData.relativeEtaleZariskiResDerivedComparison c x s r) := by
  sorry
/-- The derived Frobenius cube equality after transport to the normalized comparison arrow.
Source: Stacks 0736 and 0EBS (blueprint: lem-fd-relative-etale-frobenius-cube). -/
theorem relative_frobenius_cube_commutes
    {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext f) (p : ℕ)
    (t : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusSquare c p) :
    t.sourceAction ≫ RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.arrow c
        (SheafOfModules.unit X.ringCatSheaf) =
      RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext.arrow c
        (SheafOfModules.unit X.ringCatSheaf) ≫ t.targetAction := by
  sorry
/-- The tensor-normalized target action is p-semilinear on every local section.
Source: Stacks 0EBS (blueprint: lem-fd-relative-etale-frobenius-semilinearity). -/
theorem relative_frobenius_section_semilinear
    {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext f) (p : ℕ)
    (t : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusSquare c p)
    (q : ℕ) (V : S.Etale) (a : (smallEtaleModuleRing S).obj.obj (op V))
    (e : (c.target.extension.obj (((pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf))).val.obj (op V)) :
    t.sectionAction q V (a • e) = a ^ p • t.sectionAction q V e := by
  sorry
end AlgebraicGeometry.Scheme.Modules
