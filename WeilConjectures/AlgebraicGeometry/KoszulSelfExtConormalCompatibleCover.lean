/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtConormalNestedCharts
import WeilConjectures.AlgebraicGeometry.KoszulRegularAffineRefinement

/-! # A compatible regular Koszul comparison cover

## References

* Stacks Project, Tags 0BQY and 062I.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A regular immersion admits a compatible Koszul comparison on a covering
family of neighborhoods, without gluing to an arbitrary prescribed neighborhood
(Stacks, Tags 0BQY, 062I). -/
theorem koszulRegularImmersion_self_ext_conormal_compatible_cover
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∃ (W : V.toScheme → V.toScheme.Opens),
      (∀ z : V.toScheme, z ∈ W z) ∧
      ∃ c : ∀ z : V.toScheme, F.over (W z) ≅ T.over (W z),
        ∀ (x y : V.toScheme) (U : V.toScheme.Opens)
          (hx : U ≤ W x) (hy : U ≤ W y),
          (c x).hom.val.app (op (Over.mk (homOfLE hx))) =
            (c y).hom.val.app (op (Over.mk (homOfLE hy))) := by
  classical
  intro B S H G T F
  obtain ⟨c, hc⟩ := koszulRegularImmersion_self_ext_conormal_nested_charts i V n
  have hcharts (z : V.toScheme) : ∃ U : Y.affineOpens, i z.1 ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f := hregular z.1 z.2
  choose A hmem hA using hcharts
  let W (z : V.toScheme) := V.ι ⁻¹ᵁ (i ⁻¹ᵁ (A z).1)
  refine ⟨W, hmem, (fun z ↦ c (A z) (hA z)), ?_⟩
  intro x y U hx hy
  have hsmall (z : U) : ∃ R : Y.affineOpens,
      i z.1.1 ∈ R.1 ∧ R.1 ≤ (A x).1 ∧ R.1 ≤ (A y).1 ∧
        ∃ (m : ℕ) (f : Fin m → Γ(Y, R.1)),
          Ideal.span (Set.range f) = i.ker.ideal R ∧
            RingTheory.Sequence.IsKoszulRegular f :=
    koszulRegularImmersion_affine_refinement i (A x) (A y) z.1.1
      (hx z.2) (hy z.2) (hA x)
  choose R hRmem hRx hRy hR using hsmall
  let Q (z : U) : V.toScheme.Opens := U ⊓ (V.ι ⁻¹ᵁ (i ⁻¹ᵁ (R z).1))
  have hQx (z : U) : Q z ≤ W x := fun _ hp ↦ hRx z hp.2
  have hQy (z : U) : Q z ≤ W y := fun _ hp ↦ hRy z hp.2
  have he (z : U) :
      (c (A x) (hA x)).hom.val.app (op (Over.mk (homOfLE (hQx z)))) =
        (c (A y) (hA y)).hom.val.app (op (Over.mk (homOfLE (hQy z)))) := by
    exact (hc (R z) (A x) (hR z) (hA x) (hRx z) (Q z)
      inf_le_right (hQx z)).symm.trans
        (hc (R z) (A y) (hR z) (hA y) (hRy z) (Q z)
          inf_le_right (hQy z))
  ext s
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨T.presheaf, T.isSheaf⟩ Q U
    (fun _ ↦ homOfLE inf_le_left) ?_ _ _ (fun z ↦ ?_)
  · intro z hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hz, hRmem ⟨z, hz⟩⟩
  · let ax : Over.mk (homOfLE (hQx z)) ⟶ Over.mk (homOfLE hx) :=
      Over.homMk (homOfLE inf_le_left)
    let ay : Over.mk (homOfLE (hQy z)) ⟶ Over.mk (homOfLE hy) :=
      Over.homMk (homOfLE inf_le_left)
    have ex := ConcreteCategory.congr_hom ((c (A x) (hA x)).hom.val.naturality ax.op) s
    have ey := ConcreteCategory.congr_hom ((c (A y) (hA y)).hom.val.naturality ay.op) s
    exact ex.symm.trans ((ConcreteCategory.congr_hom (he z) _).trans ey)

end AlgebraicGeometry
