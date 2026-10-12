/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Detection

/-!
# Global sections of extensions by zero of lisse sheaves

Let `j : U ⟶ X` be an open immersion and `G` a sheaf of `ℚ̄_ℓ,U`-modules. A global section `a`
of the extension by zero `j_! G` vanishes near every point `z` outside `U`: its pullback to
`Spec κ(z)` vanishes
(`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek`),
so `a` vanishes on a weakly étale neighbourhood `V` of a point over `z`
(`AlgebraicGeometry.ProEtale.exists_mem_precoverage_map_eq_zero`). Weakly étale morphisms lift
generizations, so `V` also has a point over every generization `x` of `z`, and `a` vanishes at
the geometric points of `X` over `x` factoring through `V`
(`AlgebraicGeometry.ProEtale.exists_globalSectionsToUpperStar_eq_zero_of_specializes`).

If `G` is lisse and `U` is irreducible, with generic point specializing to a point outside `U`,
the restriction of `a` to `U`, a section of the lisse sheaf `G`, therefore vanishes at a
geometric point over the generic point of `U`, hence vanishes
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero`); and
a section of `j_! G` restricting to zero on `U` is zero, `j_! G ⟶ j_* G` being a monomorphism.
So `Γ(X, j_! G) = 0`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_hom_adicOpenImmersionLowerShriek`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

section Restriction

variable {R : Type (u + 1)} [Ring R] {W Z : Scheme.{u}}

/-- A global section `a` of a pro-étale sheaf `F` on `W` which vanishes on an object `V` of the
pro-étale site of `W` restricts to zero along every morphism `t ≫ V.hom` factoring through
`V`. -/
lemma globalSectionsToUpperStar_app_eq_zero_of_map_eq_zero
    (F : Sheaf (ProEt.topology W) (ModuleCat.{u + 1} R))
    (a : (Sheaf.Γ (ProEt.topology W) (ModuleCat.{u + 1} R)).obj F) {V : W.ProEt}
    (f : V ⟶ ProEt.mk (𝟙 W))
    (hf : F.obj.map f.op
      (((Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId W)).hom.app F) a) = 0)
    (t : Z ⟶ V.left) :
    ((globalSectionsToUpperStar _ (t ≫ V.hom)).app F) a = 0 := by
  set g := t ≫ V.hom
  set P := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
  let σ : ProEt.mk (𝟙 Z) ⟶ P.obj V :=
    MorphismProperty.Over.homMk (pullback.lift t (𝟙 Z) (Category.id_comp _).symm) (by simp [P])
      trivial
  have hσ : (overPullbackObjMkIdIso g).inv = σ ≫ P.map f :=
    (IsTerminal.ofIso (ProEt.isTerminalMkId Z) (overPullbackObjMkIdIso g).symm).hom_ext _ _
  set a' := ((Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId W)).hom.app F) a
  set η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).unit.app F
  have hu : ((g)^*[ModuleCat.{u + 1} R].obj F).obj.map (P.map f).op (η.hom.app _ a') = 0 := by
    have := congrArg (fun φ ↦ φ a') (η.hom.naturality f.op)
    simp only [ConcreteCategory.comp_apply] at this
    erw [← this, hf, map_zero]
  have hΓ := congrArg (fun φ ↦ φ a)
    ((Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId W)).hom.naturality η)
  simp only [ConcreteCategory.comp_apply] at hΓ
  rw [globalSectionsToUpperStar_app, globalSectionsLowerStarIso_hom_app',
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hσ,
    op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]
  erw [hΓ, hu, map_zero, map_zero]

end Restriction

section ExtensionByZero

variable {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

open scoped ProEtale

/-- **A section of an extension by zero vanishes near the boundary.** A global section `a` of
`j_! G` vanishes at a geometric point over every generization `x` of a point `z` outside the
open `U`: the pullback of `j_! G` to `Spec κ(z)` vanishes, so `a` vanishes on a weakly étale
neighbourhood `V` of a point over `z`
(`AlgebraicGeometry.ProEtale.exists_mem_precoverage_map_eq_zero`), and `V`, being flat over `X`,
has a point over `x`. -/
theorem exists_globalSectionsToUpperStar_eq_zero_of_specializes {G : AdicSheaf l U}
    (a : (Sheaf.Γ (ProEt.topology X) (WeilCoefficients.{u} l)).obj ((j)_!ᵃ[l].obj G).X)
    {x z : X} (hxz : x ⤳ z) (hz : z ∉ Set.range j.base) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (p : Spec (.of K) ⟶ X),
      p.base (IsLocalRing.closedPoint K) = x ∧
      ((globalSectionsToUpperStar _ p).app ((j)_!ᵃ[l].obj G).X) a = 0 := by
  let M := (j)_!ᵃ[l].obj G
  set g := X.fromSpecResidueField z
  have hg : Set.range j.base ∩ Set.range g.base = ∅ := by
    rw [range_fromSpecResidueField, Set.inter_singleton_eq_empty]
    exact hz
  have hzero : IsZero ((g)^*ᵃ[l].obj M) :=
    isZero_adicUpperStar_adicOpenImmersionLowerShriek j g hg G
  set a' := ((Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId X)).hom.app M.X) a
  have hs : ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit.app M.X).hom.app
      (op (ProEt.mk (𝟙 X))) a' = 0 := by
    have h0 : (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g).unit.app M.X = 0 :=
      ((lowerStar _ g).map_isZero ((AdicSheaf.forget _).map_isZero hzero)).eq_of_tgt _ _
    rw [h0]
    rfl
  obtain ⟨P, hP, hPs⟩ := exists_mem_precoverage_map_eq_zero g M.X a' hs
  obtain ⟨ι, T, φ, rfl⟩ := P.exists_eq_ofArrows
  rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
  -- a point over `z` of the base change of `X` to `Spec κ(z)`
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝟙 X) (g := g) z
    (IsLocalRing.closedPoint _) (by simp [g])
  obtain ⟨m, τ, hτ⟩ := ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 hP.2).1 w
  obtain ⟨V, f, ψ, hψ, hf⟩ := hPs (φ m) (.mk m)
  -- the point `v` of `V` over `z`
  set v := (ψ.left ≫ pullback.fst V.hom g).base τ
  have hv : V.hom v = z := by
    have : ψ.left ≫ pullback.fst V.hom g ≫ V.hom = ψ.left ≫ pullback.snd V.hom g ≫ g := by
      rw [pullback.condition]
    change (ψ.left ≫ pullback.fst V.hom g ≫ V.hom).base τ = z
    rw [this]
    simp [g]
  obtain ⟨v₀, -, hv₀⟩ := Flat.generalizingMap V.hom (hv ▸ hxz)
  let K := AlgebraicClosure (V.left.residueField v₀)
  let t : Spec (.of K) ⟶ V.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (V.left.residueField v₀) K)) ≫
      V.left.fromSpecResidueField v₀
  refine ⟨K, inferInstance, inferInstance, t ≫ V.hom, ?_, ?_⟩
  · change V.hom ((V.left.fromSpecResidueField v₀) _) = x
    rw [Scheme.fromSpecResidueField_apply, hv₀]
  · exact globalSectionsToUpperStar_app_eq_zero_of_map_eq_zero M.X a f hf t

lemma globalSectionOfModHom_comp {Y : Scheme.{u}} {M N : AdicSheaf l Y}
    (v : AdicSheaf.unit l Y ⟶ M) (w : M ⟶ N) :
    globalSectionOfModHom (v ≫ w) = ((Sheaf.Γ _ _).map w.hom) (globalSectionOfModHom v) := by
  rw [globalSectionOfModHom_eq, globalSectionOfModHom_eq, Mod.comp_hom', Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- **A morphism `ℚ̄_ℓ ⟶ j_! G` into the extension by zero of a lisse sheaf vanishes** if `U` is
irreducible and its generic point specializes to a point `z` outside `U`. Its restriction to `U`,
a section of the lisse sheaf `G`, vanishes at a geometric point over the generic point of `U`
(`AlgebraicGeometry.ProEtale.exists_globalSectionsToUpperStar_eq_zero_of_specializes`), hence
vanishes; and the comparison `j_! G ⟶ j_* G`, through which `ℚ̄_ℓ ⟶ j_! G` is determined by its
restriction to `U`, is a monomorphism. -/
theorem IsAdicLisseSheaf.eq_zero_of_hom_adicOpenImmersionLowerShriek [IrreducibleSpace U]
    {G : AdicSheaf l U} (hG : IsAdicLisseSheaf G) {z : X} (hz : z ∉ Set.range j.base)
    (hspec : j.base (genericPoint U) ⤳ z) (α : AdicSheaf.unit l X ⟶ (j)_!ᵃ[l].obj G) :
    α = 0 := by
  obtain ⟨K, _, _, p, hp, hpa⟩ := exists_globalSectionsToUpperStar_eq_zero_of_specializes j
    (globalSectionOfModHom α) hspec hz
  have hpr : Set.range p.base ⊆ Set.range j.base := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint K), hp]
    exact ⟨_, rfl⟩
  let pU := IsOpenImmersion.lift j p hpr
  have hpU : pU ≫ j = p := IsOpenImmersion.lift_fac _ _ _
  have hpU' : pU.base (IsLocalRing.closedPoint K) = genericPoint U :=
    j.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, hpU, hp])
  let e := asIso ((adicOpenImmersionLowerShriekAdjunction l j).unit.app G)
  let β : AdicSheaf.unit l U ⟶ G := (adicUpperStarUnitIso l j).inv ≫ (j)^*ᵃ[l].map α ≫ e.inv
  have hβ : β = 0 := by
    refine hG.eq_zero_of_globalSectionsToUpperStar_eq_zero β K fun y ↦
      ⟨genericPoint U, pU, genericPoint_specializes y, by rw [hpU'], ?_⟩
    have h₀ : ((globalSectionsToUpperStar _ (pU ≫ j)).app ((j)_!ᵃ[l].obj G).X)
        (globalSectionOfModHom α) = 0 := by
      rw [hpU]
      exact hpa
    have h₁ := congrArg (fun φ ↦ φ (globalSectionOfModHom α))
      (globalSectionsToUpperStar_comp _ pU j ((j)_!ᵃ[l].obj G).X)
    simp only [ConcreteCategory.comp_apply] at h₁
    rw [h₀, map_zero] at h₁
    have h₂ := congrArg (fun φ ↦ φ (((globalSectionsToUpperStar _ j).app
      ((j)_!ᵃ[l].obj G).X) (globalSectionOfModHom α)))
      ((globalSectionsToUpperStar _ pU).naturality e.inv.hom)
    simp only [ConcreteCategory.comp_apply, Functor.comp_map] at h₂
    have h₃ : globalSectionOfModHom β = ((Sheaf.Γ _ _).map e.inv.hom)
        (((globalSectionsToUpperStar _ j).app ((j)_!ᵃ[l].obj G).X) (globalSectionOfModHom α)) := by
      rw [globalSectionsToUpperStar_globalSectionOfModHom, ← globalSectionOfModHom_comp]
      simp only [β, Category.assoc]
    rw [h₃]
    erw [h₂, ← h₁, map_zero]
  have hj : (j)^*ᵃ[l].map α = 0 := by
    have : (j)^*ᵃ[l].map α = (adicUpperStarUnitIso l j).hom ≫ β ≫ e.hom := by
      simp [β]
    rw [this, hβ, zero_comp, comp_zero]
  set c := (adicOpenImmersionLowerShriekToLowerStar l j).app G
  have hc : α ≫ c = 0 := by
    apply ((adicUpperStarLowerStarAdjunction l j).homEquiv _ _).symm.injective
    simp [Adjunction.homEquiv_counit, hj]
  rw [← cancel_mono c, hc, zero_comp]

end ExtensionByZero

end AlgebraicGeometry.ProEtale
