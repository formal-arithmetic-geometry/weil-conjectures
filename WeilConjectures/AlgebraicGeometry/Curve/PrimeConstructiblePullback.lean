/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.AlgebraicGeometry.Curve.ModuleSheafUnderlyingColimit
import WeilConjectures.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageColimits
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Constructible approximation for one prime and one pullback -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Bijectivity on constructible prime-field module sheaves extends to every abelian sheaf
killed by the same prime, for a fixed morphism of qcqs schemes.
Source: Stacks Project, 03SA(3), 03Q5, and the first paragraph of the proof of 03SC. -/
theorem bijective_cohomologyMap_of_constructible_prime
    {X Y : Scheme.{u}} (a : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (r : ℕ) [Fact r.Prime]
    (H : ∀ (M : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Scheme.IsConstructibleSheaf M],
      ∀ q : ℕ, Function.Bijective (cohomologyMap a
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj M) q))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : r • 𝟙 G = 0) (q : ℕ) :
    Function.Bijective (cohomologyMap a G q) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero X r G hG
  obtain ⟨A, hA, hfiltered, D, hD, ι, ⟨hc⟩⟩ :=
    Scheme.exists_filtered_colimit_constructible M
  let := hA
  let := hfiltered
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})
  let F := D ⋙ U
  let c := U.mapCocone (CategoryTheory.Limits.Cocone.mk M ι)
  have hcU : CategoryTheory.Limits.IsColimit c := (Scheme.moduleSheaf_underlying_isColimit hc).some
  let L := Sheaf.functorH X.smallEtaleTopology q
  let L' := (a)^*[AddCommGrpCat.{u + 1}] ⋙ Sheaf.functorH Y.smallEtaleTopology q
  have : CategoryTheory.Limits.PreservesColimit F L := 
      CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone
    hcU (Scheme.sheafH_isColimit_large_filtered X hcU q).some
  have hc' : CategoryTheory.Limits.IsColimit (((a)^*[AddCommGrpCat.{u + 1}]).mapCocone c) :=
    CategoryTheory.Limits.isColimitOfPreserves _ hcU
  have : CategoryTheory.Limits.PreservesColimit F L' := 
      CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone
    hcU (Scheme.sheafH_isColimit_large_filtered Y hc' q).some
  let α : L ⟶ L' :=
    { app := fun K ↦ AddCommGrpCat.ofHom (cohomologyMap a K q)
      naturality := by
        intro K K' φ
        ext x
        exact cohomologyMap_map a q φ x }
  have : ∀ i, IsIso ((Functor.whiskerLeft F α).app i) := by
    intro i
    have : Scheme.IsConstructibleSheaf (D.obj i) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf (D.obj i)).mp (hD i)
    exact (ConcreteCategory.isIso_iff_bijective _).2 (H (D.obj i) q)
  have : IsIso (Functor.whiskerLeft F α) := NatIso.isIso_of_isIso_app _
  have : IsIso (α.app c.pt) :=
    CategoryTheory.Limits.isIso_app_coconePt_of_preservesColimit F α c hcU
  have hM : Function.Bijective (cohomologyMap a (U.obj M) q) :=
    ConcreteCategory.bijective_of_isIso (α.app c.pt)
  let eH := (Sheaf.functorH X.smallEtaleTopology q).mapIso e
  let eaH := (Sheaf.functorH Y.smallEtaleTopology q).mapIso
    (((a)^*[AddCommGrpCat.{u + 1}]).mapIso e)
  apply (Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso eH.hom)).mp
  have heq : cohomologyMap a G q ∘ eH.hom =
      eaH.hom ∘ cohomologyMap a (U.obj M) q := by
    funext x
    exact cohomologyMap_map a q e.hom x
  rw [heq]
  exact (ConcreteCategory.bijective_of_isIso eaH.hom).comp hM

end AlgebraicGeometry.Etale
