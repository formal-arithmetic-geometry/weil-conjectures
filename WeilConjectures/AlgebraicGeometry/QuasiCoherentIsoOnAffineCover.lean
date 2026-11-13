/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover
import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Isomorphisms of quasi-coherent modules detected on an affine open cover

## References

* [Stacks Project, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA)
* [Stacks Project, Tag 01IB](https://stacks.math.columbia.edu/tag/01IB)
* [Stacks Project, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism of quasi-coherent modules is an isomorphism if its maps on sections over an
arbitrary affine open cover are bijective. -/
theorem Hom.isIso_of_bijective_on_affine_open_cover {Y : Scheme.{u}} {F G : Y.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) {A : Type u}
    (W : A → Y.Opens) (hcover : ⨆ a, W a = ⊤) (haffine : ∀ a : A, IsAffineOpen (W a))
    (hbijective : ∀ a : A, Function.Bijective (φ.app (W a))) : IsIso φ := by
  have affine_iso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
      [M.IsQuasicoherent] [N.IsQuasicoherent] (α : M ⟶ N)
      (hα : Function.Bijective (α.app ⊤)) : IsIso α := by
    have : IsIso ((moduleSpecΓFunctor (R := R)).map α) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hα
    have : IsIso ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map α)) :=
      inferInstance
    have : IsIso ((tilde.adjunction (R := R)).counit.app N) :=
      inferInstanceAs (IsIso N.fromTildeΓ)
    have hn := (tilde.adjunction (R := R)).counit.naturality α
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    have : IsIso (M.fromTildeΓ ≫ α) := by
      change IsIso ((tilde.adjunction (R := R)).counit.app M ≫ α)
      rw [← hn]
      infer_instance
    exact (isIso_comp_left_iff M.fromTildeΓ α).1 this
  apply (sheaf_module_isIso_iff_isIso_over_open_cover Y.toRingedSpace A W hcover F G φ).2
  intro a
  let f := (haffine a).fromSpec
  have htop : f ''ᵁ (⊤ : (Spec Γ(Y, W a)).Opens) = W a := by
    ext x
    simp [f]
  have hα : IsIso ((restrictFunctor f).map φ) := by
    apply affine_iso
    change Function.Bijective (φ.app (f ''ᵁ ⊤))
    rw [htop]
    exact hbijective a
  have : IsIso ((restrictFunctor (haffine a).isoSpec.hom).map
      ((restrictFunctor f).map φ)) := inferInstance
  have e : restrictFunctor (W a).ι ≅
      restrictFunctor f ⋙ restrictFunctor (haffine a).isoSpec.hom :=
    (restrictFunctorCongr (haffine a).isoSpec_hom_fromSpec).symm ≪≫
      restrictFunctorComp _ _
  have : IsIso ((restrictFunctor (W a).ι).map φ) := by
    apply (NatIso.isIso_map_iff e φ).2
    change IsIso ((restrictFunctor (haffine a).isoSpec.hom).map
      ((restrictFunctor f).map φ))
    infer_instance
  have : IsIso ((overEquiv (W a)).functor.map (φ.over (W a))) := by
    exact (NatIso.isIso_map_iff (overFunctorEquiv (W a)) φ).2 inferInstance
  exact isIso_of_reflects_iso (φ.over (W a)) (overEquiv (W a)).functor

end AlgebraicGeometry.Scheme.Modules
