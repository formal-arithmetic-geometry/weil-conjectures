/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups U2 and H2
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Mathlib.CategoryTheory.Filtered.Basic
import Sheaf.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit

/-!
# Higher direct images and filtered diagrams at coefficient size

Source: Stacks Project, Tags 0739 and 03Q8, and the proof of Tag 09Z1.
(blueprint: lem-sbc-higher-direct-image-large-filtered-colimit)
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Large filtered continuity for shifted maps from the terminal free sheaf.
For negative shifts, the standard t-structure makes the Hom groups zero. -/
private theorem shiftedHom_final_large (Λ : Type (u + 1)) [CommRing Λ] (Z : Scheme.{u})
    [CompactSpace Z] [QuasiSeparatedSpace Z] (q : ℤ) (J : Type (u + 1)) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J
      (Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) q) := by
  classical
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let S := sheafCompose Z.smallEtaleTopology U
    let A := DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
      0 ⋙ Etale.cohomology AddCommGrpCat.{u + 1} Z (n : ℤ)
    have : S.IsLeftAdjoint := Scheme.moduleSheafForgetIsLeftAdjoint Z Λ
    have : PreservesColimitsOfShape J A :=
      ⟨fun {D} ↦ preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
        (Scheme.etaleCohomology_isColimit_large_filtered Z (colimit.isColimit D) n).some⟩
    have : PreservesColimitsOfShape J (S ⋙ A) := inferInstance
    let e := (Scheme.nonempty_freeSheafDerivedSectionsIso Z Λ n).some
    let e' := (Scheme.nonempty_etaleModuleCohomology_forgetIso Z Λ n).some
    exact preservesColimitsOfShape_of_natIso (e ≪≫ e').symm
  · have hq : q < 0 := lt_of_not_ge hq
    let F := Etale.shiftedHomFunctor Λ
      ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) q
    apply F.preservesColimitsOfShape_of_isZero _ J
    rw [Functor.isZero_iff]
    intro N
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    change Subsingleton
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) ⟶
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N)⟦q⟧)
    refine ⟨fun f g ↦ ?_⟩
    have hz (f : (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) ⟶
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N)⟦q⟧) : f = 0 := by
      let t := DerivedCategory.Plus.TStructure.t
        (C := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      have ht := t.isGE_shift ((DerivedCategory.Plus.singleFunctor _ 0).obj N)
        0 q (-q) (by omega)
      exact t.zero f 0 (-q) (by omega)
    exact (hz f).trans (hz g).symm

/-- Raw higher-image cohomology on a qcqs pullback preserves large filtered colimits. -/
private theorem presheaf_app_large (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ) (W : X.Etale)
    [CompactSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left]
    [QuasiSeparatedSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left]
    (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        Etale.higherDirectImagePresheafFunctor Λ h q ⋙ (evaluation _ _).obj (Opposite.op W)) := by
  let W' := (MorphismProperty.Over.pullback @Etale ⊤ h).obj W
  let instHom : PreservesColimitsOfShape J
      (Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ W'.left).obj (Etale.finalObject _)) q) :=
    shiftedHom_final_large Λ W'.left q J
  let instPull : PreservesColimitsOfShape J ((W'.hom)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimitsOfShape J ((W'.hom)^*[ModuleCat.{u + 1} Λ] ⋙
      Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ W'.left).obj (Etale.finalObject _)) q) :=
    @comp_preservesColimitsOfShape _ _ _ _ J _ _ _ _ _ instPull instHom
  let F := Etale.shiftedHomFunctor Λ
    ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W)) q
  let H := (W'.hom)^*[ModuleCat.{u + 1} Λ] ⋙
    Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ W'.left).obj (Etale.finalObject _)) q
  let e : F ≅ H := Etale.shiftedHomFunctorUpperStarFreeSheafIso Λ h W q
  exact preservesColimitsOfShape_of_natIso (F := H) (G := F) e.symm

/-- Higher direct image along a qcqs morphism preserves filtered diagrams indexed
in the coefficient universe, without a torsion assumption.

Source: Stacks Project, Tag 0739 (lemma-colim-works-over-collection),
Tag 03Q8 (higher-image cohomology presheaf), and Tag 09Z1 (lemma-relative-colimit).
(blueprint: lem-sbc-higher-direct-image-large-filtered-colimit)

Proof:
1. On a qcqs scheme Z, compose the free-sheaf derived-sections isomorphism with
   the module-to-abelian cohomology isomorphism. The resulting functor is abelian
   cohomology after coefficient forgetting. The latter is a left adjoint, so
   large filtered-colimit continuity for abelian cohomology proves continuity for
   shifted maps from the terminal free sheaf. For negative q, t-structure
   orthogonality makes these maps zero, hence their functor preserves colimits.
2. Restriction to the pullback of an affine etale object preserves colimits by
   its inverse-image adjunction. The shifted-Hom pullback comparison therefore
   proves pointwise continuity of the raw cohomology presheaf on affine objects.
   Such pullbacks are qcqs by permanence under base change.
3. Restrict the raw presheaf to the affine etale site and apply pointwise colimit
   preservation. Sheafification preserves colimits, and Mathlib's dense-subsite
   compatibility transports this to the small etale site. The restriction functor
   on sheaves is an equivalence and reflects colimits.
4. The canonical raw cohomology comparison induces an isomorphism after
   sheafification. Its naturality follows by transposing its naturality square
   through the sheafification adjunction. Transport colimit preservation through
   this natural isomorphism, and reflect it through coefficient forgetting.
The indexing category remains in Type(u+1). This includes the zero ring, empty
schemes, degree zero, negative degrees and singleton indexing categories. -/
theorem preservesColimitsOfShape_higherDirectImage_large
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) := by
  let G := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : U.IsLeftAdjoint := Scheme.moduleSheafForgetIsLeftAdjoint X Λ
  have : ReflectsColimitsOfShape J U := reflectsColimitsOfShape_of_reflectsIsomorphisms (G := U)
  suffices hGU : PreservesColimitsOfShape J (G ⋙ U) by
    exact preservesColimitsOfShape_of_reflects_of_preserves G U
  let P := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      Etale.higherDirectImagePresheafFunctor Λ h q
  let B := Scheme.AffineEtale.Spec X
  let A := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj B.op
  let L := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : Small.{u + 1} X.AffineEtale := small_self _
  have : LocallySmall.{u + 1} X.AffineEtale := ⟨fun _ _ ↦ small_max.{u + 1} _⟩
  have : EssentiallySmall.{u + 1} X.AffineEtale :=
    essentiallySmall_of_small_of_locallySmall X.AffineEtale
  have : HasSheafify (Scheme.AffineEtale.topology X) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let L' := presheafToSheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u + 1}
  let T := B.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology
  have : PreservesColimitsOfShape J (P ⋙ A) := by
    apply preservesColimitsOfShape_of_evaluation
    rintro ⟨W⟩
    have : IsAffine (B.obj W).left := by
      dsimp only [B]
      rw [Scheme.AffineEtale.Spec_obj_left]
      infer_instance
    obtain ⟨_, _⟩ := Etale.compactSpace_and_quasiSeparatedSpace_pullback h (B.obj W)
    exact presheaf_app_large Λ h q (B.obj W) J
  have : PreservesColimitsOfShape J ((P ⋙ A) ⋙ L') := inferInstance
  have : HasLimitsOfSize.{u, u + 1} AddCommGrpCat.{u + 1} := inferInstance
  have : ∀ V : X.Etaleᵒᵖ,
      HasLimitsOfShape (StructuredArrow V B.op) AddCommGrpCat.{u + 1} := fun V ↦
    HasLimitsOfSize.has_limits_of_shape (C := AddCommGrpCat.{u + 1}) (StructuredArrow V B.op)
  have : ∀ (F : X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (V : X.Etaleᵒᵖ),
      HasLimit (StructuredArrow.proj V B.op ⋙ F) := fun F V ↦
    HasLimitsOfShape.has_limit (StructuredArrow.proj V B.op ⋙ F)
  have : T.IsEquivalence :=
    (B.sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (Scheme.AffineEtale.topology X) X.smallEtaleTopology).toEquivalence.isEquivalence_functor
  let ec := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology B AddCommGrpCat.{u + 1}
  let ec' : (P ⋙ A) ⋙ L' ≅ (P ⋙ L) ⋙ T :=
    Functor.associator P A L' ≪≫ Functor.isoWhiskerLeft P ec ≪≫
      (Functor.associator P L T).symm
  have : PreservesColimitsOfShape J ((P ⋙ L) ⋙ T) :=
    preservesColimitsOfShape_of_natIso ec'
  have : PreservesColimitsOfShape J (P ⋙ L) :=
    preservesColimitsOfShape_of_reflects_of_preserves (P ⋙ L) T
  let adj := sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let ψ : ∀ F, P.obj F ⟶ (U.obj (G.obj F)).obj := fun F ↦
    Etale.higherDirectImagePresheafToSheaf Λ h q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  have hψ : ∀ {F F'} (g : F ⟶ F'), P.map g ≫ ψ F' = ψ F ≫ (U.map (G.map g)).hom :=
    fun g ↦ Etale.higherDirectImagePresheafToSheaf_naturality Λ h q _
  let e : P ⋙ L ≅ G ⋙ U := NatIso.ofComponents (fun F ↦ by
    let a : L.obj (P.obj F) ⟶ U.obj (G.obj F) :=
      (adj.homEquiv (P.obj F) (U.obj (G.obj F))).symm (ψ F)
    have : IsIso a :=
      Etale.isIso_higherDirectImagePresheafToSheaf_singleFunctor Λ h q F
    exact asIso a) (by
      intro F F' g
      exact adj.homEquiv_naturality_right_square
        (Y := U.obj (G.obj F)) (Y' := U.obj (G.obj F'))
        (P.map g) (ψ F') (ψ F) (U.map (G.map g)) (hψ g))
  exact preservesColimitsOfShape_of_natIso e

end AlgebraicGeometry.Etale
