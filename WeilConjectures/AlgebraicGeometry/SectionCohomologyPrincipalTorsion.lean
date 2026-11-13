/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.InvertSCOhomology
import WeilConjectures.AlgebraicGeometry.CohomologyFractionEventuallyZero
import WeilConjectures.AlgebraicGeometry.ResolutionUnitTwistComparison

/-! # Kernel torsion for raw section cohomology

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A raw resolution cohomology class vanishing on a principal open is killed by
some power of its defining function. This is only the kernel assertion and makes
no claim that classes on the principal open lift. -/
theorem sectionCohomologyPresheaf_pow_annihilates {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    ∀ x : P.obj (op W), (P.map (homOfLE (T.basicOpen_le a)).op).hom x = 0 →
      ∃ n : ℕ, a ^ n • x = 0 := by
  dsimp only
  let Y := (f ⁻¹ᵁ W).toScheme
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let L := MonoidalCategory.tensorUnit Y.Modules
  have : CompactSpace Y := isCompact_iff_compactSpace.mp (f.isCompact_preimage hW.isCompact)
  have : QuasiSeparatedSpace Y :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ W).isOpen).mp
      (f.isQuasiSeparated_preimage hW.isQuasiSeparated)
  have : G.IsQuasicoherent := isQuasicoherent_restrictFunctor _ F
  obtain ⟨s, e, hres, hmul⟩ := resolution_unitTwist_comparison f F I q W a
  obtain ⟨U, hU, c, hc⟩ := invertS_cohomology Y L G s q
  obtain ⟨d, hd⟩ := hres U hU
  intro x hx
  have hrestrict := (hd x).trans (by rw [hx, map_zero])
  have hcanonical := hc 0 (e 0 x)
  have hz : c (cohomologyFraction L G s q ⊤ 0 (e 0 x)) = 0 := by
    have heq : (RingedSpace.openModuleCohomology Y.toRingedSpace q U).map
        (MonoidalCategory.rightUnitor G).inv
          (c (cohomologyFraction L G s q ⊤ 0 (e 0 x))) = 0 := by
      simpa only [tensorPowSection_zero, tensorPow_zero, MonoidalCategory.whiskerLeft_id,
        Category.comp_id] using hcanonical.trans hrestrict
    exact (ConcreteCategory.bijective_of_isIso
      ((RingedSpace.openModuleCohomology Y.toRingedSpace q U).map
        (MonoidalCategory.rightUnitor G).inv)).1
        (heq.trans (map_zero _).symm)
  have hfrac : cohomologyFraction L G s q ⊤ 0 (e 0 x) = 0 :=
    c.injective (hz.trans c.map_zero.symm)
  obtain ⟨n, hn⟩ := cohomologyFraction_eventually_zero L G s q ⊤ 0 (e 0 x) hfrac
  refine ⟨n, (e (0 + n)).injective ?_⟩
  rw [map_zero, ← hmul n x]
  exact hn

end AlgebraicGeometry.Scheme.Modules
