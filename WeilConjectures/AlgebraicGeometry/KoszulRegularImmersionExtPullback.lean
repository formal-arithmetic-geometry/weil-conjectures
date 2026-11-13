/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.KoszulExtRankSupport
import WeilConjectures.AlgebraicGeometry.KoszulExtConstantRankTop

/-! # Pullback of scalar Ext to a Koszul-regular closed subscheme

## References

* Stacks Project, Tag 0BQZ (affine dual Koszul calculation and localization).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On the closed subscheme, the pullback of scalar Ext is the locally ranked
conormal-dual determinant. This makes no assertion about reconstructing a sheaf
on the ambient scheme from its pullback (Stacks, Tag 0BQZ). -/
theorem koszulRegularImmersion_ext_pullback
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    {q : ℤ} (hq : 0 ≤ q) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    Nonempty ((Scheme.Modules.tensorPullback i).obj F ≅
      (Scheme.Modules.locallyRankedExteriorTerm
      (SheafOfModules.homObj (R := Z.sheaf)
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
        (SheafOfModules.unit Z.ringCatSheaf)) r q)) := by
  dsimp only
  let V := Scheme.Modules.exteriorRankOpen r q.toNat
  have hVrank : ∀ z : Z, z ∈ V →
      Module.finrank (Z.presheaf.stalk z)
        ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) = q.toNat := by
    intro z hz
    exact (hr z).symm.trans hz
  obtain ⟨e⟩ := koszulRegularImmersion_ext_constantRank_top i V q.toNat
    (fun z _ ↦ hregular z) hVrank
  have hs := koszulRegularImmersion_ext_rankSupport i hregular r hr hq
  rw [Int.toNat_of_nonneg hq] at e
  dsimp only at hs
  refine ⟨@asIso _ _ _ _ ((Scheme.Modules.restrictAdjunction V.ι).unit.app _) hs ≪≫
    (Scheme.Modules.pushforward V.ι).mapIso e ≪≫ ?_⟩
  exact eqToIso (by simp only [Scheme.Modules.locallyRankedExteriorTerm, ite_eq_left hq, V])

end AlgebraicGeometry
