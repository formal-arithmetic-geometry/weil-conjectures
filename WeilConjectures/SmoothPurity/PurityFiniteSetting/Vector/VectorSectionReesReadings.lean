/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorSectionReesCoordinates
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncComparisons
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.SmoothSectionExchangeComposition

/-! # Section-exchange readings of a geometric Rees trivialization

Source: smooth-purity, Agreement on the model; section geometry (1) and (4).
(blueprint: lem-pur-vector-section-rees-readings).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem section_comp_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' B B' B'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian B] [IsNoetherian B'] [IsNoetherian B'']
    (d : ℕ) (f : X ⟶ B) (f' : X' ⟶ B') (f'' : X'' ⟶ B'')
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    [HasInvertibleExponent A X] [HasInvertibleExponent A X']
    {a : X' ⟶ X} {a' : X'' ⟶ X'} {b : B' ⟶ B} {b' : B'' ⟶ B'}
    (sq : IsPullback a f' f b) (sq' : IsPullback a' f'' f' b')
    (a'' : X'' ⟶ X) (b'' : B'' ⟶ B)
    (ha : a'' = a' ≫ a) (hb : b'' = b' ≫ b)
    (outer : IsPullback a'' f'' f b'')
    (s : B ⟶ X) (s' : B' ⟶ X') (s'' : B'' ⟶ X'')
    (hs : s' ≫ a = b ≫ s) (hs' : s'' ≫ a' = b' ≫ s')
    (hs'' : s'' ≫ a'' = b'' ≫ s) :
    Dnc.sectionBaseChange A d f outer s s'' hs'' =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b' b b'' hb).app _ ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} A) b').leftDerivedFunctor.mapIso
          (Dnc.sectionBaseChange A d f sq s s' hs) ≪≫
        Dnc.sectionBaseChange A d f' sq' s' s'' hs' := by
  subst a''
  subst b''
  exact Dnc.section_baseChange_comp A d f f' f'' sq sq' s s' s'' hs hs'

private theorem constant_square_reading (A : Type (u + 1)) [CommRing A] [Finite A]
    {E T B S : Scheme.{u}}
    [IsNoetherian E] [IsNoetherian T] [IsNoetherian B] [IsNoetherian S]
    (d : ℕ) (π : E ⟶ B) (f : T ⟶ S)
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [HasCompactification π] [HasCompactification f] [QuasiCompact f]
    [SmoothOfRelativeDimension d π] [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent A E] [HasInvertibleExponent A T]
    (a : S ⟶ B) (i : B ⟶ S) (hi : i ≫ a = 𝟙 B)
    (m : T ⟶ E) (v : E ⟶ T) (hm : v ≫ m = 𝟙 E)
    (sq : IsPullback m f π a) (sq' : IsPullback v π f i)
    (z : B ⟶ E) (t : S ⟶ T)
    (ht : t ≫ m = a ≫ z) (hz : z ≫ v = i ≫ t) :
    (Etale.upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.mapIso
        (Dnc.sectionBaseChange A d π sq z t ht).symm ≪≫
      (Etale.leftDerivedUpperStarCompSectionIso _ i a hi).app _ =
        Dnc.sectionBaseChange A d f sq' t z hz := by
  let L := Dnc.sectionBaseChange A d π sq z t ht
  let R := Dnc.sectionBaseChange A d f sq' t z hz
  let C := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i a
    (𝟙 B) hi.symm).app (Etale.sectionInvariant A π z)
  let I := (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).app
    (Etale.sectionInvariant A π z)
  have h := section_comp_eq A d π f π sq sq' (𝟙 E) (𝟙 B) hm.symm hi.symm
    (IsPullback.id_horiz π) z t z ht hz (by simp)
  have hI := congrArg (fun e ↦ I ≪≫ e) (Dnc.section_baseChange_id A d π z)
  simp only [Iso.trans_refl] at hI
  change I ≪≫ I.symm ≪≫ Dnc.sectionBaseChange A d π
    (IsPullback.id_horiz π) z z (by simp) = I at hI
  simp only [Iso.self_symm_id_assoc] at hI
  have hread :
      (Etale.upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.mapIso L ≪≫ R =
        (Etale.leftDerivedUpperStarCompSectionIso _ i a hi).app _ := by
    have hh := congrArg (fun e ↦ C.symm ≪≫ e) (h.symm.trans hI)
    change C.symm ≪≫ C ≪≫
      (Etale.upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.mapIso L ≪≫ R =
        C.symm ≪≫ I at hh
    change _ = C.symm ≪≫ I
    simpa only [Iso.symm_self_id_assoc] using hh
  rw [← hread]
  change ((Etale.upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.mapIso L).symm ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor.mapIso L ≪≫ R = R
  exact Iso.symm_self_id_assoc _ _

/-- The two readings of a specified geometric Rees trivialization are the actual
smooth section exchanges. This is a mate-pasting assertion, with the geometric
trivialization supplied as a hypothesis; it asserts no DNC specialization equation.
Source: smooth-purity, Agreement on the model, standard-pair family; DNC geometry (1).
(blueprint: lem-pur-vector-section-rees-readings).

Proof: let a:A1_B→B and let m:D_sT→E(F) be M.family inverse followed by the
constant-family projection. Its Cartesian square over a preserves the sections.
The inverse section exchange for that square constructs kappa. At either endpoint i,
M.one or M.zero identifies the composite of its fibre map with m as the identity
on E(F). The resulting outer Cartesian rectangle is the identity bundle square.
The section-base-change composition and identity laws identify the endpoint reading
with the section exchange for the composite endpoint square. Factoring that square
through the actual Rees fibre gives the canonical fibre mate followed by the e or
M.normal exchange over identity. The left-identity composition law supplies exactly
the inverse identity-pullback factors in cS and cN displayed below. All these are unit
and pasting laws and apply in rank zero and over the empty base without alteration. -/
theorem vectorSection_reesReadings (P : PurityFiniteSetting.{u})
    {T B : Scheme.{u}} [IsNoetherian B] (d : ℕ)
    (g : T ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ T) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (e : VectorBundleZeroSection.scheme B d F ≅ T)
    (we : e.hom ≫ g = VectorBundleZeroSection.π B d F)
    (ze : VectorBundleZeroSection.zero B d F ≫ e.hom = s)
    (M : VectorReesModel d g s F e) :
    letI := SmoothOfRelativeDimension.smooth d g
    letI := Dnc.compactifiable P g aB
    letI := Dnc.invertibleExponent P (g ≫ aB)
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
    let q := Scheme.Hom.normalConeProj g s
    letI := Dnc.normalCompactifiable P d g aB s hs
    letI : SmoothOfRelativeDimension d q :=
      (Scheme.Hom.normalConeData d hs).smoothOfRelativeDimension_proj
    letI := Dnc.invertibleExponent P (q ≫ aB)
    let cS := (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).symm.app _ ≪≫
      Dnc.sectionBaseChange P.Coefficient d g
        (IsPullback.of_horiz_isIso ⟨we.trans (Category.comp_id _).symm⟩)
        s (VectorBundleZeroSection.zero B d F) (ze.trans (Category.id_comp _).symm)
    let cN := (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).symm.app _ ≪≫
      Dnc.sectionBaseChange P.Coefficient d q
        (IsPullback.of_horiz_isIso ⟨M.normal_proj.trans (Category.comp_id _).symm⟩)
        s.normalConeZeroSection (VectorBundleZeroSection.zero B d F)
          (M.normal_zero.trans (Category.id_comp _).symm)
    let K := Etale.sectionInvariant P.Coefficient (VectorBundleZeroSection.π B d F)
      (VectorBundleZeroSection.zero B d F)
    ∃ κ : Dnc.familyEtale P d g aB s hs ≅
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj K,
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso _ _ _
            (AffineSpace.oneSection_comp_over _ B)).app K =
        Dnc.fibreOne P d g aB s hs ≪≫ cS) ∧
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso _ _ _
            (AffineSpace.zeroSection_comp_over _ B)).app K =
        Dnc.fibreZero P d g aB s hs ≪≫ cN)  := by
  have := SmoothOfRelativeDimension.smooth d g
  have := Dnc.compactifiable P g aB
  have := Dnc.invertibleExponent P (g ≫ aB)
  have := (Etale.vectorIntegration_geometry B d F).1
  have := (Etale.vectorIntegration_geometry B d F).2.1
  let π := VectorBundleZeroSection.π B d F
  let z := VectorBundleZeroSection.zero B d F
  have := Dnc.compactifiable P π aB
  have : SmoothOfRelativeDimension d π := by
    change SmoothOfRelativeDimension d (VectorBundleZeroSection.π B d F)
    rw [← we]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension d) e.hom g).2 inferInstance
  have := SmoothOfRelativeDimension.smooth d π
  have := Dnc.invertibleExponent P (π ≫ aB)
  let A := AffineSpace (ULift.{u} (Fin 1)) B
  let a := A ↘ B
  let f := Scheme.Hom.deformationSpaceProj g s
  let t := s.deformationSpaceSection
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have := SmoothOfRelativeDimension.smooth d f
  have := Dnc.compactifiable P f (a ≫ aB)
  have := Dnc.invertibleExponent P (f ≫ a ≫ aB)
  have := P.noetherian (π ≫ aB)
  have := P.noetherian (g ≫ aB)
  have := P.noetherian (a ≫ aB)
  have := P.noetherian (f ≫ a ≫ aB)
  let m := M.family.inv ≫ pullback.fst π a
  have hproj : M.family.inv ≫ pullback.snd π a = f := by
    rw [← M.family_proj, Iso.inv_hom_id_assoc]
  have sq : IsPullback m f π a := by
    have h := (IsPullback.of_horiz_isIso
      (show CommSq M.family.inv f (pullback.snd π a) (𝟙 A) from
        ⟨hproj.trans (Category.comp_id _).symm⟩)).paste_horiz
          (IsPullback.of_hasPullback π a)
    change IsPullback (M.family.inv ≫ pullback.fst π a) f π (𝟙 A ≫ a) at h
    rw [Category.id_comp] at h
    exact h
  have ht : t ≫ m = a ≫ z := by
    have ht' : t ≫ M.family.inv = vectorReesZero B d F := by
      change s.deformationSpaceSection ≫ M.family.inv = _
      rw [← M.family_zero, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    dsimp only [m]
    rw [← Category.assoc, ht']
    exact pullback.lift_fst _ _ _
  let L := Dnc.sectionBaseChange P.Coefficient d π sq z t ht
  refine ⟨L.symm, ?_, ?_⟩
  · let i := AffineSpace.oneSection (ULift.{u} (Fin 1)) B
    let v := Scheme.Hom.deformationSpaceOneFibre g s
    let sqE : IsPullback e.hom π g (𝟙 B) :=
      IsPullback.of_horiz_isIso ⟨we.trans (Category.comp_id _).symm⟩
    have sq' : IsPullback (e.hom ≫ v) π f i := by
      simpa only [Category.id_comp] using sqE.paste_horiz
        (Scheme.Hom.isPullback_deformationSpaceOneFibre g s)
    have hm : (e.hom ≫ v) ≫ m = 𝟙 _ := by
      change (e.hom ≫ Scheme.Hom.deformationSpaceOneFibre g s) ≫
        M.family.inv ≫ pullback.fst π a = _
      rw [← M.one]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.lift_fst _ _ _
    have hz : z ≫ (e.hom ≫ v) = i ≫ t := by
      rw [← Category.assoc, ze]
      exact Scheme.Hom.comp_deformationSpaceOneFibre hs
    have hh := constant_square_reading P.Coefficient d π f a i
      (AffineSpace.oneSection_comp_over _ B) m (e.hom ≫ v) hm sq sq' z t ht hz
    have hp := Dnc.section_baseChange_comp_left_id P.Coefficient d f g π
      (Scheme.Hom.isPullback_deformationSpaceOneFibre g s) sqE t s z
      (Scheme.Hom.comp_deformationSpaceOneFibre hs) ze
    exact hh.trans hp
  · let q := Scheme.Hom.normalConeProj g s
    have := Dnc.normalCompactifiable P d g aB s hs
    have : SmoothOfRelativeDimension d q :=
      (Scheme.Hom.normalConeData d hs).smoothOfRelativeDimension_proj
    have := SmoothOfRelativeDimension.smooth d q
    have := Dnc.invertibleExponent P (q ≫ aB)
    have := Dnc.normalQuasiCompact d g s hs
    have := P.noetherian (q ≫ aB)
    let i := AffineSpace.zeroSection (ULift.{u} (Fin 1)) B
    let v := s.ker.normalConeToDeformationSpace
    let sqN : IsPullback M.normal.hom π q (𝟙 B) :=
      IsPullback.of_horiz_isIso ⟨M.normal_proj.trans (Category.comp_id _).symm⟩
    have sq' : IsPullback (M.normal.hom ≫ v) π f i := by
      simpa only [Category.id_comp] using sqN.paste_horiz
        (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
    have hm : (M.normal.hom ≫ v) ≫ m = 𝟙 _ := by
      change (M.normal.hom ≫ s.ker.normalConeToDeformationSpace) ≫
        M.family.inv ≫ pullback.fst π a = _
      rw [← M.zero]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.lift_fst _ _ _
    have hz : z ≫ (M.normal.hom ≫ v) = i ≫ t := by
      rw [← Category.assoc, M.normal_zero]
      exact Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace
    have hh := constant_square_reading P.Coefficient d π f a i
      (AffineSpace.zeroSection_comp_over _ B) m (M.normal.hom ≫ v) hm sq sq' z t ht hz
    have hp := Dnc.section_baseChange_comp_left_id P.Coefficient d f q π
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) sqN t
      s.normalConeZeroSection z
      Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace M.normal_zero
    exact hh.trans hp

end WeilConjectures.PurityFiniteSetting
