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
/-- Sectionwise Frobenius restriction transports exist on both sides and commute with direct image
on tensor generators. This is exactly the data-construction part of Step 7.
Source: Stacks 0EBS (blueprint: lem-fd-relative-etale-frobenius-transport). -/
theorem relative_frobenius_transport_data
    {X S : Scheme.{u}} {f : X ⟶ S}
    (c : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiContext f)
    (p : ℕ) (hp : p.Prime) (hchar : (p : S.ringCatSheaf.obj.obj (op ⊤)) = 0) :
    ∃ x : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusTransport c.source p,
      ∃ s : RelativeEtaleZariskiDerivedData.RelativeEtaleZariskiFrobeniusTransport c.target p,
        ∃ r : pushforward f ⋙
            RelativeEtaleZariskiDerivedData.relativeZariskiRestrictScalars S s.sigma ≅
          RelativeEtaleZariskiDerivedData.relativeZariskiRestrictScalars X x.sigma ⋙
            pushforward f,
          ∀ (M : X.Modules) (W : S.Opens) (m : ((pushforward f).obj M).val.obj (op W)),
            (r.hom.app M).val.app (op W) m = m := by
  sorry
end AlgebraicGeometry.Scheme.Modules
