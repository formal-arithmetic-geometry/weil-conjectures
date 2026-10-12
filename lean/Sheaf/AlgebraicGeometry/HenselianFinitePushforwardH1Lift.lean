module
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import WeilConjectures.SixFunctors.Finite.BaseChange
import Sheaf.AlgebraicGeometry.EtaleEdgeMapBaseChange
import Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison
/-! # Finite pushforward H¹ lifting over a henselian local ring

Source: Stacks Project, Lemma 0A5H, finite-pushforward lifting argument.
(blueprint: lem-weil-pbc-henselian-finite-pushforward-h1-lift) -/
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private lemma hmap_bijective {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : F ⟶ G) [IsIso e] (n : ℕ) : Function.Bijective (Sheaf.H.map e n) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨Sheaf.H.map (inv e) n, ?_, ?_⟩
  · intro x
    rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]
  · intro x
    rw [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private lemma restriction_finite_constant
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (i : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (sq : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    {V : Scheme.{u}} (h : V ⟶ Y) [IsFinite h]
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Function.Surjective (cohomologyMap i
      ((h)_*[AddCommGrpCat.{u + 1}].obj ((constantSheaf V.smallEtaleTopology _).obj M)) 1) := by
  let V₀ := Limits.pullback h i
  let j : V₀ ⟶ V := Limits.pullback.fst h i
  let h₀ : V₀ ⟶ Y₀ := Limits.pullback.snd h i
  have sh : IsPullback j h₀ h i := IsPullback.of_hasPullback h i
  have sv : IsPullback j (h₀ ≫ f₀) (h ≫ f)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) := sh.paste_vert sq
  have : IsProper (h ≫ f) := inferInstance
  let F := (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  have hj : Function.Surjective (cohomologyMap j F 1) :=
    (bijective_cohomologyMap_one_constantSheaf_of_henselianRing
      (IsLocalRing.maximalIdeal A) (h ≫ f) j (h₀ ≫ f₀) sv M).2
  have hb := bijective_edgeMap_baseChange sh F 1
    (by have := isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sh
        infer_instance)
  intro x
  obtain ⟨a, ha⟩ := hj (
    ((Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₀).counit.app
      ((j)^*[AddCommGrpCat.{u + 1}].obj F)) 1).comp
      ((cohomologyMap h₀ _ 1).comp
        (Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1} sh.toCommSq).app F) 1))) x)
  obtain ⟨z, hz⟩ := hb.1.2 a
  refine ⟨z, hb.2.1 ?_⟩
  have comm := DFunLike.congr_fun (cohomology_edgeMap_baseChange sh F 1) z
  simp only [AddMonoidHom.comp_apply] at comm ha hz ⊢
  rw [← ha]
  have hc : (Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₀).counit.app
      ((j)^*[AddCommGrpCat.{u + 1}].obj F)) 1)
      ((cohomologyMap h₀ _ 1) ((Sheaf.H.map ((baseChangeMap AddCommGrpCat.{u + 1}
        sh.toCommSq).app F) 1) ((cohomologyMap i _ 1) z))) =
      (cohomologyMap j F 1) ((Sheaf.H.map ((upperStarLowerStarAdjunction
        AddCommGrpCat.{u + 1} h).counit.app F) 1) ((cohomologyMap h _ 1) z)) := by
    simpa [AddMonoidHom.comp_apply, Category.assoc] using comm.symm
  change (Sheaf.H.map _ 1)
    ((cohomologyMap h₀ _ 1) ((Sheaf.H.map _ 1) ((cohomologyMap i _ 1) z))) = _
  exact hc.trans (congrArg (cohomologyMap j F 1) hz)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private lemma restriction_surjective_of_iso {X Y : Scheme.{u}} (i : X ⟶ Y)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (n : ℕ) (hf : Function.Surjective (cohomologyMap i F n)) :
    Function.Surjective (cohomologyMap i G n) := by
  intro x
  obtain ⟨y, hy⟩ := (hmap_bijective (((i)^*[AddCommGrpCat.{u + 1}]).map e.hom) n).2 x
  obtain ⟨z, hz⟩ := hf y
  refine ⟨Sheaf.H.map e.hom n z, ?_⟩
  rw [cohomologyMap_map, hz, hy]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def underlyingPushforwardConstantIso
    {V Y : Scheme.{u}} (h : V ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ]
    (M : ModuleCat.{u + 1} Λ) :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((h)_*[ModuleCat.{u + 1} Λ].obj ((constantSheaf V.smallEtaleTopology _).obj M)) ≅
    (h)_*[AddCommGrpCat.{u + 1}].obj
      ((constantSheaf V.smallEtaleTopology _).obj
        ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)) := by
  let F := (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : V.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification _ _
  let e : (sheafCompose Y.smallEtaleTopology U).obj ((h)_*[ModuleCat Λ].obj F) ≅
      (h)_*[AddCommGrpCat].obj ((sheafCompose V.smallEtaleTopology U).obj F) :=
    { hom := ⟨(Functor.associator
        (MorphismProperty.Over.pullback @Etale ⊤ h).op F.obj U).hom⟩
      inv := ⟨(Functor.associator
        (MorphismProperty.Over.pullback @Etale ⊤ h).op F.obj U).inv⟩ }
  exact e ≪≫ (h)_*[AddCommGrpCat].mapIso
    ((constantCommuteCompose V.smallEtaleTopology U).app M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private lemma moduleComparison_naturality
    {X Y : Scheme.{u}} (i : X ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ]
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ψ : F ⟶ G) :
    set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  let UY := sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    let UX := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    let c := fun J ↦ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv
      (UY.obj J) (UX.obj ((i)^*[ModuleCat.{u + 1} Λ].obj J))).symm
        (UY.map ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app J))
    (i)^*[AddCommGrpCat.{u + 1}].map (UY.map ψ) ≫ c G =
      c F ≫ UX.map ((i)^*[ModuleCat.{u + 1} Λ].map ψ) := by
  dsimp only
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hn := congrArg (fun t ↦
    (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map t)
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.naturality ψ)
  simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hn
  exact hn

/-- Finite pushforward classes on the closed fibre are carried, after a morphism to a
module sheaf, to the restriction of a class on the total space.

Proof steps (Stacks Project, Lemma 0A5H):
1. Use permanence of finite morphisms and finite exchange to identify the finite
   pushforward after passage to the residue fibre.
2. Pull back the constructible constant sheaf and apply finite pushforward
   cohomology, followed by edge-map base change, to compare the degree-one
   classes on the total space and on the closed fibre.
3. Apply finite étale lifting over the henselian local ring and the H¹ torsor
   comparison to obtain a class `z` on the total finite pushforward whose
   restriction represents `x`.
4. Identify constant-module sheaves with their underlying abelian sheaves and
   use cohomology pullback functoriality.  The inverse-image module exactness
   comparison supplies the canonical map appearing in the conclusion.
5. Naturality of the cohomology map induced by `ψ` then gives the displayed
   equality between the restricted image of `x` and the restriction of
   `H¹(ψ)(z)`.

Source: Stacks Project, Lemma 0A5H, finite-pushforward lifting argument.
(blueprint: lem-weil-pbc-henselian-finite-pushforward-h1-lift)
-/
theorem finite_pushforward_H_one_lift_of_henselianLocalRing
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (i : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (sq : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V : Scheme.{u}} (h : V ⟶ Y) [IsFinite h] [LocallyOfFinitePresentation h]
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (ψ : (h)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf V.smallEtaleTopology _).obj M) ⟶ J)
    (x : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj
        ((h)_*[ModuleCat.{u + 1} Λ].obj
          ((constantSheaf V.smallEtaleTopology _).obj M)))) 1) :
    ∃ z : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((h)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf V.smallEtaleTopology _).obj M))) 1,
      Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1} Λ].map ψ)) 1 x =
        Sheaf.H.map
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv _ _).symm
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
              AddCommGrpCat.{u + 1})).map
                ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app J))) 1
          (cohomologyMap i _ 1
            (Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
              AddCommGrpCat.{u + 1})).map ψ) 1 z)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  let UY := sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let UX := sheafCompose Y₀.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let K := (h)_*[ModuleCat.{u + 1} Λ].obj
    ((constantSheaf V.smallEtaleTopology _).obj M)
  let c := fun F ↦ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv
    (UY.obj F) (UX.obj ((i)^*[ModuleCat.{u + 1} Λ].obj F))).symm
      (UY.map ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F))
  have : IsIso (c K) := isIso_moduleAbelianInverseImageComparison i Λ K
  have hl : Function.Surjective (cohomologyMap i (UY.obj K) 1) := by
    apply restriction_surjective_of_iso i
      (underlyingPushforwardConstantIso h Λ M).symm 1
    exact restriction_finite_constant f i f₀ sq h
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)
  obtain ⟨y, hy⟩ := (hmap_bijective (c K) 1).2 x
  obtain ⟨z, hz⟩ := hl y
  refine ⟨z, ?_⟩
  change Sheaf.H.map (UX.map ((i)^*[ModuleCat.{u + 1} Λ].map ψ)) 1 x =
    Sheaf.H.map (c J) 1 (cohomologyMap i (UY.obj J) 1 (Sheaf.H.map (UY.map ψ) 1 z))
  rw [cohomologyMap_map, hz, ← hy]
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun t ↦ Sheaf.H.map t 1 y)
    (moduleComparison_naturality i Λ ψ).symm

end AlgebraicGeometry.Etale
