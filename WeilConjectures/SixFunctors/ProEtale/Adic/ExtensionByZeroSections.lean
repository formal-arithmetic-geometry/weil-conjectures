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
`Spec κ(z)` vanishes (`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek`),
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
    MorphismProperty.Over.homMk (pullback.lift t (𝟙 Z) (Category.id_comp _).symm) (by simp [P]) trivial
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
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hσ, op_comp, Functor.map_comp,
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
  have hzero : IsZero ((g)^*ᵃ[l].obj M) := isZero_adicUpperStar_adicOpenImmersionLowerShriek j g hg G
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

end ExtensionByZero

end AlgebraicGeometry.ProEtale
