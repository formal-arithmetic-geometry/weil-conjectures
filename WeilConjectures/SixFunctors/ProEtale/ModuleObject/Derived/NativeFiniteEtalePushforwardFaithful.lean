/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleCounit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-! # Faithfulness of finite-etale direct image on native modules -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem ab_clopen_surjective {X : Scheme.{u}}
    (G : Sheaf (ProEt.topology X) Ab.{u + 1}) {V P : X.ProEt}
    (i : V ⟶ P) [IsOpenImmersion i.left] (hi : IsClosed (Set.range i.left.base)) :
    Function.Surjective (G.obj.map i.op) := by
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1}).asEquivalence.inverse
  let H := (sheafCompose (ProEt.topology X) E).obj G
  have h := Scheme.ProEt.surjective_map_of_isOpenImmersion_of_isClosed_range H i hi
  have he : Epi (E.map (G.obj.map i.op)) := (ModuleCat.epi_iff_surjective _).mpr h
  have hf : Epi (G.obj.map i.op) := Functor.epi_of_epi_map E he
  exact (AddCommGrpCat.epi_iff_surjective _).mp hf

private theorem ab_finiteEtale_counit_epi {U X : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] (M : Sheaf (ProEt.topology U) Ab.{u + 1}) :
    Epi ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app M) := by
  rw [← Adjunction.leftAdjointUniq_hom_app_counit _
    (ProEtale.localizationRestrictionLowerStarAdjunction _ p inferInstance)]
  suffices Epi ((ProEtale.localizationRestrictionLowerStarAdjunction Ab.{u + 1} p
      inferInstance).counit.app M) from epi_comp _ _
  have : Sheaf.IsLocallySurjective ((ProEtale.localizationRestrictionLowerStarAdjunction
      Ab.{u + 1} p inferInstance).counit.app M) := by
    refine Presheaf.isLocallySurjective_of_surjective _ _ fun ⟨V⟩ ↦ ?_
    have : IsOpenImmersion ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ p
        inferInstance trivial).unit.app V).left :=
      AlgebraicGeometry.isOpenImmersion_pullbackLift_of_etale p V.hom
    exact ab_clopen_surjective M
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ p inferInstance trivial).unit.app V)
      (AlgebraicGeometry.isClosedImmersion_pullbackLift_of_isSeparated p V.hom
        ).isClosedEmbedding.isClosed_range
  infer_instance

/-- For a finite etale map the native pullback/direct-image counit is epi.
Source: the open-and-closed diagonal and extension of sections by zero.
(blueprint: new-det-sp-native-finite-etale-pushforward-faithful).
Proof. Compute pullback by restriction to the localized site. Its counit restricts
sections along a graph, which is open and closed. Every section extends by zero
on the complement, so restriction is surjective. Transfer this computation from
abelian sheaves through the coefficient pullback comparison. The module forgetful
functor reflects epimorphisms. No surjectivity of the scheme map is used. -/
theorem nativeFiniteEtale_counit_epi
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    Epi ((upperStarLowerStarAdjunction Λ p).counit.app M) := by
  have he := ab_finiteEtale_counit_epi p M.X
  have h := forget_map_upperStarLowerStarAdjunction_counit_app Λ p M
  simp only [lowerStarForgetIso, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at h
  have hc : Epi ((upperStarForgetIso Λ p).hom.app ((lowerStar Λ p).obj M) ≫
      ((upperStarLowerStarAdjunction Λ p).counit.app M).hom) := h.symm ▸ he
  have hf : Epi ((upperStarLowerStarAdjunction Λ p).counit.app M).hom :=
    epi_of_epi ((upperStarForgetIso Λ p).hom.app ((lowerStar Λ p).obj M)) _
  exact Functor.epi_of_epi_map (Mod.forget _) hf

/-- Direct image along a finite etale map detects equality of native module maps.
Source: the counit epimorphisms above and the adjunction criterion for faithfulness.
(blueprint: new-det-sp-native-finite-etale-pushforward-faithful). -/
theorem nativeFiniteEtale_lowerStar_faithful
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] : (lowerStar Λ p).Faithful := by
  have : ∀ M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U),
      Epi ((upperStarLowerStarAdjunction Λ p).counit.app M) :=
    fun M ↦ nativeFiniteEtale_counit_epi Λ p M
  exact (upperStarLowerStarAdjunction Λ p).faithful_R_of_epi_counit_app

end AlgebraicGeometry.ProEtale.CondensedRing
