/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.GlobalSectionsLimitComparison
import Sheaf.AlgebraicGeometry.PullbackSectionsComparison
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Continuity of sections of étale sheaves at inverse limits

Let `h₁ : T ⟶ S` and `h₂ : S ⟶ R` be morphisms of schemes. For an abelian étale sheaf `G` on
`R`, the unit of `h₁^* ⊣ h₁_*` induces a comparison map
`h₂_* h₂^* G ⟶ (h₁ ≫ h₂)_* (h₁ ≫ h₂)^* G`
(`AlgebraicGeometry.Etale.unitComparison`), compatible with the units of `h₂` and `h₁ ≫ h₂`.
On sections over an étale `R`-scheme `W` it is the pullback of sections of `G|_{W ×_R S}` to
`W ×_R T`.

For a cofiltered system `(Dⱼ)` of quasi-compact quasi-separated schemes over `R` with affine
transition maps and limit `X`, the comparison maps exhibit the sections of the pullback of `G`
over `W ×_R X` as the colimit of the sections over the `W ×_R Dⱼ`, for `W` quasi-compact and
quasi-separated (`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`). This is
blueprint `lem-weil-pbc-etale-section-continuity`, which belongs to the subsection
`sk-prop-h2`. The proof below reduces it to global-section continuity and naturality
under cartesian pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale

variable {R S T : Scheme.{u}}

/-- The comparison map `h₂_* h₂^* G ⟶ h₁₂_* h₁₂^* G` for `h₁₂ = h₁ ≫ h₂`, induced by the unit of
`h₁^* ⊣ h₁_*` at `h₂^* G` and the composition isomorphisms of pushforwards and pullbacks. -/
noncomputable def unitComparison (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₁₂ : T ⟶ R)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (h₂)_*[AddCommGrpCat.{u + 1}].obj ((h₂)^*[AddCommGrpCat.{u + 1}].obj G) ⟶
      (h₁₂)_*[AddCommGrpCat.{u + 1}].obj ((h₁₂)^*[AddCommGrpCat.{u + 1}].obj G) :=
  (h₂)_*[AddCommGrpCat.{u + 1}].map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₁).unit.app
        ((h₂)^*[AddCommGrpCat.{u + 1}].obj G)) ≫
    (lowerStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh₁₂).hom.app _ ≫
      (h₁₂)_*[AddCommGrpCat.{u + 1}].map
        ((upperStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh₁₂).inv.app G)

/-- The comparison map is compatible with the units: the unit of `h₂` followed by the comparison
map is the unit of `h₁ ≫ h₂`. -/
@[reassoc]
lemma unit_app_comp_unitComparison (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₁₂ : T ⟶ R)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₂).unit.app G ≫
        unitComparison h₁ h₂ h₁₂ hh₁₂ G =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₁₂).unit.app G := by
  have h := upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} h₁ h₂ G h₁₂ hh₁₂
  rw [Adjunction.comp_unit_app] at h
  rw [← cancel_mono ((h₁₂)_*[AddCommGrpCat.{u + 1}].map
    ((upperStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh₁₂).hom.app G)), h, unitComparison]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

variable {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
  (π : D ⟶ (Functor.const J).obj R) (c : Cone D) (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j)

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **Continuity of sections at an inverse limit.** Let `(Dⱼ)` be a cofiltered system of
quasi-compact quasi-separated schemes over `R` with affine transition maps, with limit `X`, let
`G` be an abelian étale sheaf on `R` and `W` a quasi-compact quasi-separated étale `R`-scheme,
where `R` is quasi-separated, so that all the `W ×_R Dⱼ` are quasi-compact and quasi-separated
(as for the étale objects of finite presentation of the blueprint; without it the statement
fails).
Then the sections of the pullback of `G` over `W ×_R X` are the filtered colimit of the sections
of the pullbacks of `G` over the `W ×_R Dⱼ`: every section over `W ×_R X` comes from some
`W ×_R Dⱼ`, and a section over `W ×_R Dⱼ` which vanishes on `W ×_R X` already vanishes on some
`W ×_R Dⱼ'`, `j' ⟶ j`. The sections of the pullback of `G` over `W ×_R Dⱼ` are written as the
sections of `πⱼ_* πⱼ^* G` over `W`, and the transition maps are
`AlgebraicGeometry.Etale.unitComparison`.
(blueprint: `lem-weil-pbc-etale-section-continuity`) -/
theorem unitComparison_app_isColimit_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    (∀ t : ((P)_*[AddCommGrpCat.{u + 1}].obj
        ((P)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W),
      ∃ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
        ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
        (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = t) ∧
    ∀ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
        ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
      (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = 0 →
        ∃ (j' : J) (f : j' ⟶ j), (unitComparison (D.map f) (π.app j) (π.app j')
          (by simp) G).hom.app (op W) s = 0 := by
  classical
  let : IsConnected J := IsCofiltered.isConnected J
  let : QuasiSeparated W.hom := @QuasiSeparated.of_quasiSeparatedSpace W.left R W.hom inferInstance
  let E : J ⥤ Scheme.{u} :=
    { obj := fun j ↦ pullback W.hom (π.app j)
      map := fun {j k} f ↦ pullback.map _ _ _ _ (𝟙 W.left) (D.map f) (𝟙 R)
        (by simp) (by simp)
      map_id := fun j ↦ by apply pullback.hom_ext <;> simp
      map_comp := fun f g ↦ by apply pullback.hom_ext <;> simp }
  let d : Cone E :=
    { pt := pullback W.hom P
      π :=
        { app := fun j ↦ pullback.map _ _ _ _ (𝟙 W.left) (c.π.app j) (𝟙 R)
            (by simp) (by simpa using hP j)
          naturality := fun j k f ↦ by
            apply pullback.hom_ext <;> simp [E] } }
  let β : E ⟶ D :=
    { app := fun j ↦ pullback.snd W.hom (π.app j)
      naturality := fun j k f ↦ by simp [E] }
  have hd : IsLimit d :=
    isLimitOfIsPullbackOfIsConnected β d c
      { hom := pullback.snd W.hom P
        w := fun j ↦ by simp [d, β] }
      (fun j ↦ isPullback_pullback_map W.hom P (π.app j) (c.π.app j) (hP j).symm) hc
  let σ : E ⟶ (Functor.const J).obj R :=
    { app := fun j ↦ pullback.fst W.hom (π.app j) ≫ W.hom
      naturality := fun j k f ↦ by simp [E] }
  let Q : d.pt ⟶ R := pullback.fst W.hom P ≫ W.hom
  have hQ : ∀ j, Q = d.π.app j ≫ σ.app j := by
    intro j
    simp [Q, d, σ]
  let : ∀ j, CompactSpace (E.obj j) := fun j ↦ by dsimp [E]; infer_instance
  let : ∀ j, QuasiSeparatedSpace (E.obj j) := fun j ↦
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd W.hom (π.app j))
  let : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (E.map f) := fun {j k} f ↦
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_pullback_map W.hom (π.app j) (π.app k) (D.map f)
        (by simp)).flip inferInstance
  let e := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ pullbackSectionsEquiv G W f
  have he := fun {X Y : Scheme.{u}} ↦ @pullbackSections_comparison R G W X Y
  obtain ⟨hsurj, hzero⟩ := globalSections_limit_comparison E σ d Q hQ hd G
  constructor
  · intro t
    obtain ⟨j, s, hs⟩ := hsurj (e P t)
    refine ⟨j, (e (π.app j)).symm s, ?_⟩
    apply (e P).injective
    simp only [unitComparison]
    exact (he (c.π.app j) (π.app j) P (hP j) (d.π.app j)
      (by simp [d]) (by simp [d]) ((e (π.app j)).symm s)).trans
      (by simpa only [e, AddEquiv.apply_symm_apply, Q, σ, d, Functor.const_obj_obj] using hs)
  · intro j s hs
    have hz := congrArg (e P) hs
    simp only [unitComparison] at hz
    have hz' := (he (c.π.app j) (π.app j) P (hP j) (d.π.app j)
      (by simp [d]) (by simp [d]) s).symm.trans hz
    simp only [map_zero] at hz'
    obtain ⟨j', f, hf⟩ := hzero j (e (π.app j) s) hz'
    refine ⟨j', f, ?_⟩
    apply (e (π.app j')).injective
    simp only [unitComparison]
    exact (he (D.map f) (π.app j) (π.app j') (by simp) (E.map f)
      (by simp [E]) (by simp [E]) s).trans (by simpa only [map_zero] using hf)

/-- **Continuity of sections at an inverse limit, surjectivity**: the first half of
`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`. -/
theorem unitComparison_app_surjective_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (t : ((P)_*[AddCommGrpCat.{u + 1}].obj ((P)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)) :
    ∃ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
      ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
      (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = t :=
  (unitComparison_app_isColimit_of_isLimit D π c P hP hc G W).1 t

/-- **Continuity of sections at an inverse limit, injectivity**: the second half of
`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`. -/
theorem exists_unitComparison_app_eq_zero_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] (j : J)
    (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
      ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W))
    (hs : (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = 0) :
    ∃ (j' : J) (f : j' ⟶ j), (unitComparison (D.map f) (π.app j) (π.app j')
      (by simp) G).hom.app (op W) s = 0 :=
  (unitComparison_app_isColimit_of_isLimit D π c P hP hc G W).2 j s hs

end Etale

end AlgebraicGeometry
