/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Paper.RingedDerivedSliceData
import Sheaf.Paper.RingedSliceDerivedAdjunction
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat

/-!
# Invertibility of the derived slice mate

Source: Stacks Project, algebraization.tex, Tag 099J; Modules on Sites, Tag 04J0;
Cohomology on Sites, Tag 07A6
(blueprint: lem-weil-pbc-ringed-slice-derived-mate-isIso).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 256

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

attribute [local irreducible] ringedSliceRestriction ringedSliceRestrictionFactors

attribute [local instance 20000] CategoryTheory.siteAbelianHasSheafify
  CategoryTheory.siteAbelianWEqualsLocallyBijective


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 20000 in
-- The generic mate identity needs only a small fixed elaboration budget.
private theorem mateOnRepresentative
    {A B Av Bv DA DB DAv DBv : Type*}
    [Category A] [Category B] [Category Av] [Category Bv]
    [Category DA] [Category DB] [Category DAv] [Category DBv]
    {G : A ⥤ B} {F : B ⥤ A} {Gv : Av ⥤ Bv} {Fv : Bv ⥤ Av}
    (adj : G ⊣ F) (adjv : Gv ⊣ Fv)
    (rA : A ⥤ Av) (rB : B ⥤ Bv)
    (QA : A ⥤ DA) (QB : B ⥤ DB) (QAv : Av ⥤ DAv) (QBv : Bv ⥤ DBv)
    {L : DA ⥤ DB} {R : DB ⥤ DA} {Lv : DAv ⥤ DBv} {Rv : DBv ⥤ DAv}
    (d : L ⊣ R) (dv : Lv ⊣ Rv)
    (jA : DA ⥤ DAv) (jB : DB ⥤ DBv)
    (cA : QA ⋙ jA ≅ rA ⋙ QAv) (cB : QB ⋙ jB ≅ rB ⋙ QBv)
    (ε : QA ⋙ L ⟶ G ⋙ QB) (η : F ⋙ QA ⟶ QB ⋙ R)
    (εv : QAv ⋙ Lv ⟶ Gv ⋙ QBv) (ηv : Fv ⋙ QAv ⟶ QBv ⋙ Rv)
    (b : F ⋙ rA ≅ rB ⋙ Fv) (beta : R ⋙ jA ≅ jB ⋙ Rv)
    (P : A) (lam : Gv.obj (rA.obj P) ⟶ rB.obj (G.obj P))
    (hlam : adjv.homEquiv _ _ lam = rA.map (adj.unit.app P) ≫ b.hom.app (G.obj P))
    (hunit : d.unit.app (QA.obj P) ≫ R.map (ε.app P) =
      QA.map (adj.unit.app P) ≫ η.app (G.obj P))
    (hnormal : jA.map (η.app (G.obj P)) ≫ beta.hom.app (QB.obj (G.obj P)) ≫
        Rv.map (cB.hom.app (G.obj P)) =
      cA.hom.app (F.obj (G.obj P)) ≫ QAv.map (b.hom.app (G.obj P)) ≫
        ηv.app (rB.obj (G.obj P)))
    (hlocal : dv.homEquiv _ _ (εv.app (rA.obj P) ≫ QBv.map lam) =
      QAv.map (adjv.homEquiv _ _ lam) ≫ ηv.app (rB.obj (G.obj P))) :
    (((mateEquiv d dv).symm (TwoSquare.mk _ _ _ _ beta.hom)).natTrans).app (QA.obj P) ≫
        jB.map (ε.app P) ≫ cB.hom.app (G.obj P) =
      Lv.map (cA.hom.app P) ≫ εv.app (rA.obj P) ≫ QBv.map lam := by
  apply (dv.homEquiv _ _).injective
  have hu := unit_mateEquiv_symm d dv (TwoSquare.mk _ _ _ _ beta.hom) (QA.obj P)
  change jA.map (d.unit.app (QA.obj P)) ≫ beta.hom.app (L.obj (QA.obj P)) =
    dv.unit.app (jA.obj (QA.obj P)) ≫
      Rv.map (((mateEquiv d dv).symm (TwoSquare.mk _ _ _ _ beta.hom)).natTrans.app
        (QA.obj P)) at hu
  rw [dv.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  rw [hlocal]
  rw [Adjunction.homEquiv_unit]
  simp only [Rv.map_comp, ← Category.assoc]
  rw [← hu]
  simp only [Category.assoc]
  have hn := beta.hom.naturality (ε.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  slice_lhs 2 3 => rw [← hn]
  simp only [← Category.assoc]
  rw [← jA.map_comp, hunit, jA.map_comp]
  simp only [Category.assoc]
  rw [hnormal]
  have hc := cA.hom.naturality (adj.unit.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc
  rw [← Category.assoc, ← Category.assoc, hc]
  simp only [Category.assoc, ← QAv.map_comp, hlam, Functor.id_obj]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryUnit
    {A B Av Bv : Type*} [Category A] [Category B] [Category Av] [Category Bv]
    {G : A ⥤ B} {F : B ⥤ A} {Gv : Av ⥤ Bv} {Fv : Bv ⥤ Av}
    (adj : G ⊣ F) (adjv : Gv ⊣ Fv) (rA : A ⥤ Av) (rB : B ⥤ Bv)
    (lam : rA ⋙ Gv ≅ G ⋙ rB) (b : F ⋙ rA ≅ rB ⋙ Fv)
    (ht : ∀ (M : A) (N : B) (h : M ⟶ F.obj N),
      lam.hom.app M ≫ rB.map ((adj.homEquiv M N).symm h) =
        (adjv.homEquiv _ _).symm (rA.map h ≫ b.hom.app N)) (P : A) :
    adjv.homEquiv _ _ (lam.hom.app P) =
      rA.map (adj.unit.app P) ≫ b.hom.app (G.obj P) := by
  apply (adjv.homEquiv _ _).symm.injective
  have hh := ht P (G.obj P) (adj.unit.app P)
  rw [Adjunction.homEquiv_symm_unit] at hh
  rw [rB.map_id] at hh
  erw [Category.comp_id] at hh
  dsimp only [Functor.comp_obj] at hh ⊢
  simpa only [Equiv.symm_apply_apply] using hh


private theorem unitOfNormalized
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    {G : A ⥤ B} {F : B ⥤ A} (adj : G ⊣ F)
    (QA : A ⥤ DA) (QB : B ⥤ DB) {L : DA ⥤ DB} {R : DB ⥤ DA} (d : L ⊣ R)
    (ε : QA ⋙ L ⟶ G ⋙ QB) (η : F ⋙ QA ⟶ QB ⋙ R)
    (hn : ∀ (P : A) (I : B) (h : G.obj P ⟶ I),
      d.homEquiv _ _ (ε.app P ≫ QB.map h) =
        QA.map (adj.homEquiv _ _ h) ≫ η.app I) (P : A) :
    d.unit.app (QA.obj P) ≫ R.map (ε.app P) =
      QA.map (adj.unit.app P) ≫ η.app (G.obj P) := by
  have h := hn P (G.obj P) (𝟙 _)
  dsimp only [Functor.comp_obj] at h
  rw [QB.map_id, Category.comp_id] at h
  rw [d.homEquiv_unit, adj.homEquiv_unit, F.map_id] at h
  dsimp only [Functor.comp_obj] at h
  rw [Category.comp_id] at h
  exact h


private theorem isIsoAppTransport
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (τ : F ⟶ G) {X Y : A} (c : X ≅ Y) [IsIso (τ.app X)] : IsIso (τ.app Y) := by
  have h : IsIso (F.map c.hom ≫ τ.app Y) := by
    rw [τ.naturality c.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map c.hom) (τ.app Y)


private def mapComplexSquareIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ)


variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem epsilonOnFlat
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)]
    (e : RingedSliceDerivedImage.{u, w} u a)
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hp : P.IsAcyclicTensorKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) :
    IsIso (e.epsilon.app P) := by
  obtain ⟨e₀, he₀⟩ := ringedSliceDerivedImage_exists u a
  let := e.isLeftDerived
  let := e₀.isLeftDerived
  have := he₀ P hp hf
  let c := Functor.leftDerivedNatIso e.left e₀.left e.epsilon e₀.epsilon
    (HomologicalComplex.quasiIso _ (.up ℤ)) (Iso.refl _)
  have h := Functor.leftDerivedNatTrans_app e.left e₀.left e.epsilon e₀.epsilon
    (HomologicalComplex.quasiIso _ (.up ℤ)) (𝟙 _) P
  simp only [NatTrans.id_app, Category.comp_id] at h
  change c.hom.app (DerivedCategory.Q.{w}.obj P) ≫ e₀.epsilon.app P = e.epsilon.app P at h
  rw [← h]
  infer_instance


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- The mate normalization compares four complex and derived category presentations.
/-- The normalized right-derived slice comparison has invertible inverse mate.
Source: Stacks Project, Modules on Sites, Tag 04J0; Cohomology on Sites, Tags 08FI
and 07A6 (blueprint: lem-weil-pbc-ringed-slice-derived-mate-isIso).

Proof: Left-derived uniqueness compares each supplied presentation to the one
whose counit is invertible on flat-term K-flat complexes. Thus both supplied
counits are invertible there. Restriction preserves K-flatness and flat terms.
The ordinary inverse-adjunct identity, specialized to the unit, identifies the
ordinary slice comparison's adjunct. Apply the derived unit identity for mates,
the global Hom normalization, the assumed normalization of beta, and the local
Hom normalization. Naturality of the restriction factorization gives the equation
identifying the mate, followed by the global counit, with the local counit followed
by Q of the ordinary slice comparison. On a flat-term K-flat representative every
other factor is invertible, so the mate is invertible there. Resolve an arbitrary
derived object's complex representative by a flat-term K-flat complex and use
naturality along its inverted resolution map. All mate components, and hence the
mate itself, are invertible. This applies to empty sites and zero rings too. -/
theorem ringedSliceDerivedMate_isIso
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] (V : D)
    [hc : (Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    [_hl : PreservesFiniteLimits
      ((Over.post (X := V) u).sheafPullback (Type u) (K.over V) (J.over (u.obj V)))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (u.obj V)))]
    (e : RingedSliceDerivedImage.{u, w} u a)
    (l : RingedSliceDerivedImage.{u, w} (Over.post (X := V) u)
      (localizedRingedSiteMap u a V))
    (beta : e.right ⋙ ringedSliceRestriction.{u, w} R V ≅
        ringedSliceRestriction.{u, w} S (u.obj V) ⋙ l.right)
    (hnormal : ∀ (I : CochainComplex (SheafOfModules.{u}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ),
            (ringedSliceRestriction.{u, w} R V).map (e.eta.app I) ≫
              beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
              l.right.map ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app I) =
            (ringedSliceRestrictionFactors.{u, w} R V).hom.app
              (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I) ≫
              DerivedCategory.Q.{w}.map (ringedSlicePushforwardComplexIso u a V I).hom ≫
              l.eta.app
              ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I)) :
    IsIso (((mateEquiv e.adjunction l.adjunction).symm
        (TwoSquare.mk _ _ _ _ beta.hom)).natTrans) := by
  classical
  let : K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let : (K.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let : (J.over (u.obj V)).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let adjM := ringedSliceModuleAdjunction u a
  let adjMv := ringedSliceModuleAdjunction (Over.post (X := V) u)
    (localizedRingedSiteMap u a V)
  let jA := ringedSliceRestriction.{u, w} R V
  let jB := ringedSliceRestriction.{u, w} S (u.obj V)
  let cA := ringedSliceRestrictionFactors.{u, w} R V
  let cB := ringedSliceRestrictionFactors.{u, w} S (u.obj V)
  let QA := DerivedCategory.Q.{w} (C := SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
  let QB := DerivedCategory.Q.{w} (C := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  let QAv := DerivedCategory.Q.{w} (C := SheafOfModules.{u}
    (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over V))
  let QBv := DerivedCategory.Q.{w} (C := SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (u.obj V)))
  let rA := overFunctor ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) V
  let rB := overFunctor ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (u.obj V)
  let : rA.Additive := (ringedOverFunctor_exactGeneral.{u, u, u, u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) V).1
  let : rB.Additive := (ringedOverFunctor_exactGeneral.{u, u, u, u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (u.obj V)).1
  let G := ringedSliceModulePullback u a
  let Gv := ringedSliceModulePullback (Over.post (X := V) u)
    (localizedRingedSiteMap u a V)
  let : G.Additive := ringedSlicePullbackAdditive u a
  let : Gv.Additive := ringedSlicePullbackAdditive
    (Over.post (X := V) u) (localizedRingedSiteMap u a V)
  let F := ringedSliceModulePushforward u a
  let Fv := ringedSliceModulePushforward (Over.post (X := V) u)
    (localizedRingedSiteMap u a V)
  let : F.Additive := ringedSlicePushforwardAdditive u a
  let : Fv.Additive := ringedSlicePushforwardAdditive
    (Over.post (X := V) u) (localizedRingedSiteMap u a V)
  let rAc := rA.mapHomologicalComplex (.up ℤ)
  let rBc := rB.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Gvc := Gv.mapHomologicalComplex (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Fvc := Fv.mapHomologicalComplex (.up ℤ)
  let adj := adjM.mapHomologicalComplex (.up ℤ)
  let adjv := adjMv.mapHomologicalComplex (.up ℤ)
  obtain ⟨_, _, _, _, _, lam, b, hb, ht⟩ :=
    localize_ringed_site_morphism_general (K := K) (J := J) (R := R) (S := S) u a V
  change rA ⋙ Gv ≅ G ⋙ rB at lam
  let lamc : rAc ⋙ Gvc ≅ Gc ⋙ rBc :=
    mapComplexSquareIso rA Gv G rB lam
  let bc : Fc ⋙ rAc ≅ rBc ⋙ Fvc := mapComplexSquareIso F rA rB Fv b
  let m := ((mateEquiv e.adjunction l.adjunction).symm
    (TwoSquare.mk _ _ _ _ beta.hom)).natTrans
  have hfac (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
      m.app (QA.obj P) ≫
          jB.map (e.epsilon.app P) ≫
          cB.hom.app (Gc.obj P) =
        l.left.map (cA.hom.app P) ≫
          l.epsilon.app (rAc.obj P) ≫ QBv.map (lamc.hom.app P) := by
    apply mateOnRepresentative adj adjv rAc rBc
      QA QB QAv QBv
      e.adjunction l.adjunction jA
      jB
      cA cB
      e.epsilon e.eta l.epsilon l.eta bc beta P (lamc.hom.app P)
    · apply HomologicalComplex.hom_ext
      intro n
      change (adjMv.homEquiv _ _ (lam.hom.app (P.X n))) = _
      have hh := ordinaryUnit adjM adjMv rA rB lam b ht (P.X n)
      exact hh
    · exact unitOfNormalized adj QA QB e.adjunction
        e.epsilon e.eta e.normalized P
    · have hbc : bc.hom.app (Gc.obj P) =
          (ringedSlicePushforwardComplexIso u a V (Gc.obj P)).hom := by
        apply HomologicalComplex.hom_ext
        intro n
        change b.hom.app ((Gc.obj P).X n) = 𝟙 _
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro T
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        exact hb _ T.unop
      rw [hbc]
      exact hnormal (Gc.obj P)
    · exact l.normalized (rAc.obj P) (rBc.obj (Gc.obj P)) (lamc.hom.app P)
  have hgood (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ)
      (hp : P.IsAcyclicTensorKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) :
      IsIso (m.app (QA.obj P)) := by
    have hrest : CochainComplex.IsAcyclicTensorKFlat (R := R.over V) (rAc.obj P) := by
      apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp
      apply (ringedSite_restriction_exact_kflat K R V).2.2 P
      exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hp
    have hflat : ∀ n : ℤ, IsFlat (R := R.over V) ((rAc.obj P).X n) := by
      intro n
      exact isFlat_over (P.X n) V (hf n)
    have := epsilonOnFlat u a e P hp hf
    have := epsilonOnFlat (Over.post (X := V) u) (localizedRingedSiteMap u a V)
      l (rAc.obj P) hrest hflat
    have hh := hfac P
    have hiso : IsIso (m.app (QA.obj P) ≫
        jB.map (e.epsilon.app P) ≫
        cB.hom.app (Gc.obj P)) := by
      rw [hh]
      infer_instance
    exact IsIso.of_isIso_comp_right (m.app (QA.obj P))
      (jB.map (e.epsilon.app P) ≫
        cB.hom.app (Gc.obj P))
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro X
  obtain ⟨P, s, hp, hf, hs, _⟩ := CochainComplex.exists_isKFlatResolution
    (QA.objPreimage X)
  let := hs
  have := hgood P hp hf
  let c := asIso (QA.map s) ≪≫ QA.objObjPreimageIso X
  exact isIsoAppTransport m c

end SheafOfModules
