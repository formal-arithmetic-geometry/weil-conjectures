/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorDualToIhomMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarComparison

/-!
# Duality for lisse `ℓ`-adic sheaves

For a lisse sheaf `M` of `ℚ̄_ℓ,Y`-modules on the pro-étale site of `Y`, with dual
`M^∨ = 𝓗om(M, ℚ̄_ℓ)`, the canonical morphism `X ⊗ M^∨ ⟶ 𝓗om(M, X)`,
`x ⊗ φ ↦ (m ↦ x φ(m))` (`CategoryTheory.Mod.tensorDualToIhom`), is an isomorphism for every
`ℓ`-adic sheaf `X` (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_tensorDualToIhom`); that
is, `- ⊗ M^∨ ≅ 𝓗om(M, -)` (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.tensorDualIsoIhom`).

Being an isomorphism is local for the pro-étale topology
(`AlgebraicGeometry.ProEtale.AdicSheaf.isIso_of_isIso_upperStar`), and the pullback along a
weakly étale morphism `g` carries the canonical morphism for `M` to the canonical morphism for
`g^* M` (`AlgebraicGeometry.ProEtale.isIso_upperStar_map_tensorDualToIhom_iff`), since it
commutes with tensor products and internal homs compatibly with the evaluations. On a cover
trivialising `M`, `g^* M` is free of finite rank, for which the canonical morphism is an
isomorphism (`CategoryTheory.Mod.isIso_tensorDualToIhom_of_iso_biproduct`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

attribute [local instance] Sheaf.symmetricCategory

section Pullback

variable {V : Scheme.{u}} (g : V ⟶ Y) [WeaklyEtale g]

variable (l) in
/-- The pullback of the dual is the dual of the pullback, along a weakly étale morphism:
`g^* 𝓗om(M, ℚ̄_ℓ) ≅ 𝓗om(g^* M, g^* ℚ̄_ℓ) ≅ 𝓗om(g^* M, ℚ̄_ℓ)`. -/
noncomputable def adicUpperStarDualIso (M : AdicSheaf l Y) :
    (g)^*ᵃ[l].obj ((AdicSheaf.ihom M).obj (AdicSheaf.unit l Y)) ≅
      (AdicSheaf.ihom ((g)^*ᵃ[l].obj M)).obj (AdicSheaf.unit l V) :=
  (adicUpperStarIhomIso l g M).app _ ≪≫ (AdicSheaf.ihom _).mapIso (adicUpperStarUnitIso l g)

/-- The identification of the pullback of the dual with the dual of the pullback is compatible
with the evaluations. -/
lemma adicUpperStarDualIso_evaluation (M : AdicSheaf l Y) :
    (adicUpperStarDualIso l g M).hom.hom ▷ ((g)^*ᵃ[l].obj M).X ≫
        Mod.evaluation ((g)^*ᵃ[l].obj M) (AdicSheaf.unit l V) =
      μ (g)^*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj (AdicSheaf.unit l Y)).X M.X ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.evaluation M (AdicSheaf.unit l Y)) ≫
          (adicUpperStarUnitIso l g).hom.hom := by
  rw [adicUpperStarDualIso, Iso.trans_hom, Mod.comp_hom', comp_whiskerRight_assoc,
    Iso.app_hom, Functor.mapIso_hom, Mod.evaluation_naturality,
    ← Category.assoc, adicUpperStarIhomIso_evaluation, Category.assoc]

/-- **Pullback along a weakly étale morphism and `X ⊗ M^∨ ⟶ 𝓗om(M, X)`**: the pullback of the
canonical morphism for `M` and `X` is an isomorphism if the canonical morphism for `g^* M` and
`g^* X` is. -/
lemma isIso_upperStar_map_tensorDualToIhom (M X : AdicSheaf l Y)
    [IsIso (Mod.tensorDualToIhom ((g)^*ᵃ[l].obj M) ((g)^*ᵃ[l].obj X))] :
    IsIso ((g)^*ᵃ[l].map (Mod.tensorDualToIhom M X)) := by
  have hβ (P Q : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :=
    Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g) P Q
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  have key := Mod.tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom
    (adicUpperStarRingHom l g) hβ M X ((adicUpperStarIhomIso l g M).hom.app X)
    (adicUpperStarIhomIso_evaluation g M X) (adicUpperStarDualIso l g M).hom
    (adicUpperStarUnitIso l g).hom.hom (IsIso.hom_inv_id _) (adicUpperStarDualIso_evaluation g M)
  have : IsIso ((Mod.tensorLeftMap (adicUpperStarDualIso l g M).hom).app ((g)^*ᵃ[l].obj X)) :=
    inferInstanceAs (IsIso ((Mod.tensorLeftMapIso (adicUpperStarDualIso l g M)).hom.app _))
  have : IsIso ((Mod.tensorLeftCompMapModComapIso (adicUpperStarRingHom l g) hβ
      ((AdicSheaf.ihom M).obj (AdicSheaf.unit l Y))).inv.app X ≫
        (g)^*ᵃ[l].map (Mod.tensorDualToIhom M X) ≫ (adicUpperStarIhomIso l g M).hom.app X) := by
    have : IsIso (Mod.tensorDualToIhom ((Mod.mapModComap (adicUpperStarRingHom l g)).obj M)
        ((Mod.mapModComap (adicUpperStarRingHom l g)).obj X)) :=
      ‹IsIso (Mod.tensorDualToIhom ((g)^*ᵃ[l].obj M) ((g)^*ᵃ[l].obj X))›
    have : IsIso ((Mod.tensorLeftMap (adicUpperStarDualIso l g M).hom).app
        ((Mod.mapModComap (adicUpperStarRingHom l g)).obj X)) :=
      ‹IsIso ((Mod.tensorLeftMap (adicUpperStarDualIso l g M).hom).app ((g)^*ᵃ[l].obj X))›
    erw [key]
    infer_instance
  have := IsIso.of_isIso_comp_left ((Mod.tensorLeftCompMapModComapIso (adicUpperStarRingHom l g)
    hβ ((AdicSheaf.ihom M).obj (AdicSheaf.unit l Y))).inv.app X)
    ((g)^*ᵃ[l].map (Mod.tensorDualToIhom M X) ≫ (adicUpperStarIhomIso l g M).hom.app X)
  exact IsIso.of_isIso_comp_right _ ((adicUpperStarIhomIso l g M).hom.app X)

end Pullback

/-- **Duality for lisse sheaves**: for a lisse `ℓ`-adic sheaf `M` and any `ℓ`-adic sheaf `X`, the
canonical morphism `X ⊗ M^∨ ⟶ 𝓗om(M, X)`, `x ⊗ φ ↦ (m ↦ x φ(m))`, is an isomorphism. It is so
after pullback along the members of a pro-étale cover trivialising `M`, where `M` becomes free of
finite rank. -/
theorem IsAdicLisseSheaf.isIso_tensorDualToIhom {M : AdicSheaf l Y} (hM : IsAdicLisseSheaf M)
    (X : AdicSheaf l Y) : IsIso (Mod.tensorDualToIhom M X) := by
  obtain ⟨R, hR, hRM⟩ := hM
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine AdicSheaf.isIso_of_isIso_upperStar g hR _ fun i ↦ ?_
  obtain ⟨n, ⟨e⟩⟩ := hRM (g i) (.mk i)
  have := Mod.isIso_tensorDualToIhom_of_iso_biproduct ((g i)^*ᵃ[l].obj X) e
  exact isIso_upperStar_map_tensorDualToIhom (g i) M X

/-- **Duality for lisse sheaves**: for a lisse `ℓ`-adic sheaf `M`, `- ⊗ M^∨ ≅ 𝓗om(M, -)`,
through `x ⊗ φ ↦ (m ↦ x φ(m))`. -/
noncomputable def IsAdicLisseSheaf.tensorDualIsoIhom {M : AdicSheaf l Y}
    (hM : IsAdicLisseSheaf M) :
    Mod.tensorLeft ((AdicSheaf.ihom M).obj (AdicSheaf.unit l Y)) ≅ AdicSheaf.ihom M :=
  have (X : AdicSheaf l Y) : IsIso ((Mod.tensorDualToIhomNatTrans M).app X) :=
    hM.isIso_tensorDualToIhom X
  have : IsIso (Mod.tensorDualToIhomNatTrans M) := NatIso.isIso_of_isIso_app _
  asIso (Mod.tensorDualToIhomNatTrans M)

@[simp]
lemma IsAdicLisseSheaf.tensorDualIsoIhom_hom_app {M : AdicSheaf l Y} (hM : IsAdicLisseSheaf M)
    (X : AdicSheaf l Y) : hM.tensorDualIsoIhom.hom.app X = Mod.tensorDualToIhom M X :=
  rfl

end AlgebraicGeometry.ProEtale
