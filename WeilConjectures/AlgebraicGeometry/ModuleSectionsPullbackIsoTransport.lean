/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Module sections transported along an isomorphism

## References

* [Stacks, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks, Tag 0095](https://stacks.math.columbia.edu/tag/0095)
* [Stacks, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
* [Stacks, Tag 01I6](https://stacks.math.columbia.edu/tag/01I6)
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Global sections of a pulled-back module transport along a scheme isomorphism
(Stacks, Tags 0095, 0097 and 01I6). -/
theorem nonempty_module_sections_pullback_iso_transport
    {S X Y : Scheme.{u}} (h : Y ≅ X) (g : X ⟶ S) (g' : Y ⟶ S)
    (hg : h.hom ≫ g = g') (M : S.Modules) :
    Nonempty ((ModuleCat.extendScalars (Scheme.Γ.mapIso h.op).hom.hom).obj
      (ModuleCat.of Γ(X, ⊤) Γ((Scheme.Modules.pullback g).obj M, ⊤)) ≅
        ModuleCat.of Γ(Y, ⊤) Γ((Scheme.Modules.pullback g').obj M, ⊤)) := by
  classical
  let N := (Scheme.Modules.pullback g).obj M
  let s := Scheme.Γ.mapIso h.op
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv s.commRingCatIsoToRingEquiv
  let es : ModuleCat.extendScalars s.hom.hom ≅ ModuleCat.restrictScalars s.inv.hom :=
    (ModuleCat.extendRestrictScalarsAdj s.hom.hom).leftAdjointUniq E.symm.toAdjunction
  let t : (Scheme.Modules.pullback h.hom).obj N ≅
      (Scheme.Modules.pushforward h.inv).obj N := by
    simpa using (Scheme.Modules.pullbackIsoPushforwardInv h.hom).app N
  let t' := (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).mapIso t
  let k : (Scheme.Modules.pullback h.hom).obj N ≅
      (Scheme.Modules.pullback g').obj M :=
    (Scheme.Modules.pullbackComp h.hom g).app M ≪≫
      (Scheme.Modules.pullbackCongr hg).app M
  let k' := (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).mapIso k
  refine ⟨es.app _ ≪≫ ?_ ≪≫ t'.symm ≪≫ k'⟩
  exact Iso.refl _

end AlgebraicGeometry
