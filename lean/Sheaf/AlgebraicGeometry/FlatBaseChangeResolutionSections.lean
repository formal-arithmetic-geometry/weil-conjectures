/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
import Sheaf.AlgebraicGeometry.FlatPullbackHomologyAdjointSections
import Sheaf.AlgebraicGeometry.FlatBaseChangeRestrictedLiftHomology

/-! # FlatBaseChangeResolutionSections

Source: Stacks Project, Cohomology, Tags 02N7, 01FB and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

private theorem section_diagram_cancel {A B C D E F G H : AddCommGrpCat.{uBC}}
    (r : A ⟶ B) (theta : B ⟶ C) (u : C ⟶ D) (v : D ⟶ C)
    (k : C ⟶ E) (h : B ⟶ F) (theta' : F ⟶ E) (d : E ⟶ G)
    (m : A ⟶ H) (s : H ⟶ F) (hu : u ≫ v = 𝟙 C)
    (hc : theta ≫ k = h ≫ theta') (hh : r ≫ h = m ≫ s) :
    (r ≫ theta ≫ u) ≫ (v ≫ k ≫ d) = m ≫ (s ≫ theta' ≫ d) := by
  simp only [Category.assoc]
  rw [← Category.assoc u, hu, Category.id_comp, ← Category.assoc theta, hc]
  simp only [Category.assoc]
  rw [← Category.assoc r, hh]
  simp only [Category.assoc]

set_option maxHeartbeats 800000 in
-- Resolution transports compare section, scheme-module and homology functor composites.
set_option backward.isDefEq.respectTransparency true in
/-- The section formula for one augmented resolution lift.
Source: Stacks, Cohomology, Tags 02N7, 01FB, 01E4, 01EZ.
(blueprint: lem-weil-pbc-flat-base-change-resolution-sections).

Proof: Restrict t to U = f⁻¹V and use the augmentation-preserving comparisons
 in D to obtain a map of the source resolution into the direct image of the
 target resolution on W = g'⁻¹U. D.unit_square gives its augmentation equation
 with D.psi. Resolve that pushed complex by lambda into injectives. In the
 recorded construction of moduleCohomologyFMap choose lambda times the restricted
 lift as the horizontal map. Sections of lambda induce invertible homology maps
 (01EZ), so H(lambda) inverse times H(lambda t) equals H(t). Independence of the
 cohomology-map choices (`moduleCohomologyFMap_independent`) identifies this
 with the recorded map. Naturality of
 theta with respect to maps of section complexes transports this equation to
 the two resolutionSectionClass maps. Finally q is the adjoint of c, namely
 unit followed by g_*c. Exactness of g^* identifies its homology with pullback
 of homology; on each locally represented cocycle the adjoint of H(c) therefore
 sends its class to the class of q(s). Sheafification gives the same equality
 of sections. The isoRightDerivedObj maps in sourceClass, targetClass and beta
 transport that equality to precisely the displayed formula. -/
theorem flatBaseChangeResolutionBeta_sections {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J.ι.f 0))
    (p : ℕ) :
    ∀ (V : S.Opens)
        (D : FlatBaseChangeOpenChoices f g F I J V)
        (xi : (forget₂ _ AddCommGrpCat.{uBC}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F))),
        Hom.app ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
          (flatBaseChangeResolutionBeta f g I J t p)) V
          (D.sourceClass p xi) =
        D.targetClass p
          (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
            ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p xi) := by
  intro V D xi
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let L := ((pushforward (pullback.fst g f)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj J.cocomplex
  let a := D.target.sections ≪≫ eqToIso (congrArg (fun U ↦
    ((RingedSpace.openModuleSections (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
       (ComplexShape.up ℕ)).obj J.cocomplex)
        (flatBaseChangeOpenEquality f g V))
  let r := resolutionSectionHomology D.source.resolution K V D.source.sections p
  let s := resolutionSectionHomology D.target.resolution L (g ⁻¹ᵁ V) a p
  let m := moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
    ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  let c := ((K.sc p).mapHomologyIso (tensorPullback g)).inv ≫
    (HomologicalComplex.homologyFunctor S'.Modules (ComplexShape.up ℕ) p).map
      (flatBaseChangeResolutionC f g I J t)
  let k := adj.homEquiv _ _ c
  let eI := I.isoRightDerivedObj (pushforward f) p
  let eJ := J.isoRightDerivedObj (pushforward (pullback.fst g f)) p
  have hb : adj.homEquiv _ _ (flatBaseChangeResolutionBeta f g I J t p) =
      eI.hom ≫ k ≫ (pushforward g).map eJ.inv := by
    change adj.homEquiv _ _ ((tensorPullback g).map eI.hom ≫ c ≫ eJ.inv) = _
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    rfl
  have hsource : D.sourceClass p =
      r ≫ sectionHomologyClass K V p ≫ Hom.app eI.inv V := by
    dsimp only [FlatBaseChangeOpenChoices.sourceClass]
    rw [resolutionSectionClass_factor]
    simp only [Category.assoc]
    rfl
  have htarget : D.targetClass p =
      s ≫ sectionHomologyClass L (g ⁻¹ᵁ V) p ≫ Hom.app eJ.inv (g ⁻¹ᵁ V) := by
    dsimp only [FlatBaseChangeOpenChoices.targetClass]
    rw [resolutionSectionClass_factor]
    simp only [Category.assoc]
    rfl
  have hc : sectionHomologyClass K V p ≫ Hom.app k V =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC} (ComplexShape.up ℕ) p).map
        (pushforwardComplexSections g (flatBaseChangeResolutionQ f g I J t) V) ≫
      sectionHomologyClass L (g ⁻¹ᵁ V) p :=
    flatPullbackHomologyAdjoint_sections g K L (flatBaseChangeResolutionQ f g I J t) V p
  have hh : r ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC} (ComplexShape.up ℕ) p).map
        (pushforwardComplexSections g (flatBaseChangeResolutionQ f g I J t) V) = m ≫ s :=
    flatBaseChangeRestrictedLift_homology f g I J t ht V D p
  have hi : Hom.app eI.inv V ≫ Hom.app eI.hom V = 𝟙 _ := by
    rw [← Hom.comp_app, eI.inv_hom_id, Hom.id_app]
  have hb' : Hom.app (adj.homEquiv _ _ (flatBaseChangeResolutionBeta f g I J t p)) V =
      Hom.app eI.hom V ≫ Hom.app k V ≫ Hom.app eJ.inv (g ⁻¹ᵁ V) := by
    rw [hb, Hom.comp_app, Hom.comp_app, pushforward_map_app]
    rfl
  have hs := section_diagram_cancel r (sectionHomologyClass K V p)
    (Hom.app eI.inv V) (Hom.app eI.hom V) (Hom.app k V)
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{uBC} (ComplexShape.up ℕ) p).map
      (pushforwardComplexSections g (flatBaseChangeResolutionQ f g I J t) V))
    (sectionHomologyClass L (g ⁻¹ᵁ V) p) (Hom.app eJ.inv (g ⁻¹ᵁ V)) m s hi hc hh
  have he := (congrArg₂ (fun a b ↦ a ≫ b) hsource hb').trans
    (hs.trans (congrArg (fun a ↦ m ≫ a) htarget.symm))
  exact congrArg (fun a ↦ a xi) he

end AlgebraicGeometry.Scheme.Modules
