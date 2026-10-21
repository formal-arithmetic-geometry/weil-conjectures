/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.RingedDerivedSliceLocalization
public import Sheaf.CategoryTheory.Sites.LocalizedModulePullbackComparison
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.Paper.RingedSliceDerivedAdjunction

/-!
# Normalization of the derived pullback comparison for a ringed slice

Source: Stacks Project, Modules on Sites, Tag 04J0; Cohomology on Sites,
Tags 07A6, 07A7 and 08FI
(blueprint: lem-weil-pbc-ringed-slice-pullback-mate-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 256

universe u w v x

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

attribute [local implicit_reducible] DerivedCategory HomotopyCategory
  SheafOfModules.instCategory SheafOfModules.instAbelian

attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
  CategoryTheory.siteAbelianHasSheafify
  CategoryTheory.siteAbelianWEqualsLocallyBijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizeRepresentative
    {A B Av Bv : Type*} {DA DB DAv DBv : Type v}
    [Category A] [Category B] [Category Av] [Category Bv]
    [Category.{x} DA] [Category.{x} DB] [Category.{x} DAv] [Category.{x} DBv]
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
    (sq : RingedSliceAdjunctionSquare d dv jA jB) (P : A)
    (τ : rA.obj (F.obj (G.obj P)) ⟶ Fv.obj (rB.obj (G.obj P)))
    (lam : Gv.obj (rA.obj P) ⟶ rB.obj (G.obj P))
    (hlam : adjv.homEquiv _ _ lam = rA.map (adj.unit.app P) ≫ τ)
    (hunit : d.unit.app (QA.obj P) ≫ R.map (ε.app P) =
      QA.map (adj.unit.app P) ≫ η.app (G.obj P))
    (hnormal : jA.map (η.app (G.obj P)) ≫ sq.beta.hom.app (QB.obj (G.obj P)) ≫
        Rv.map (cB.hom.app (G.obj P)) =
      cA.hom.app (F.obj (G.obj P)) ≫ QAv.map τ ≫
        ηv.app (rB.obj (G.obj P)))
    (hlocal : dv.homEquiv _ _ (εv.app (rA.obj P) ≫ QBv.map lam) =
      QAv.map (adjv.homEquiv _ _ lam) ≫ ηv.app (rB.obj (G.obj P))) :
    sq.lambda.hom.app (QA.obj P) ≫
        jB.map (ε.app P) ≫ cB.hom.app (G.obj P) =
      Lv.map (cA.hom.app P) ≫ εv.app (rA.obj P) ≫ QBv.map lam := by
  apply (dv.homEquiv _ _).injective
  have hu : jA.map (d.unit.app (QA.obj P)) ≫ sq.beta.hom.app (L.obj (QA.obj P)) =
      dv.unit.app (jA.obj (QA.obj P)) ≫ Rv.map (sq.lambda.hom.app (QA.obj P)) := by
    have h := congrArg (fun f ↦ f ≫ Rv.map (sq.lambda.hom.app (QA.obj P)))
      (sq.unit (QA.obj P))
    simp only [Category.assoc, ← Rv.map_comp, Iso.inv_hom_id_app] at h
    erw [Rv.map_id, Category.comp_id] at h
    exact h
  rw [dv.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  rw [hlocal]
  rw [Adjunction.homEquiv_unit]
  simp only [Rv.map_comp, ← Category.assoc]
  rw [← hu]
  simp only [Category.assoc]
  have hn := sq.beta.hom.naturality (ε.app P)
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


variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary localization comparison applied termwise to a complex. Its components
are the specified inverse mate of the sectionwise identity, not a chosen isomorphism.
Source: Stacks Tag 04J0
(blueprint: lem-weil-pbc-ringed-slice-pullback-mate-normalization). -/
def ringedSlicePullbackComplexMap (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ((ringedSliceModulePullback (Over.post (X := V) u)
        (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ)).obj
        ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P) ⟶
      (CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj
        (((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj P) where
  f n := (sliceModulePullbackMap u (ringedSiteModuleMap u a) V).app (P.X n)
  comm' i j _ :=
    ((sliceModulePullbackMap u (ringedSiteModuleMap u a) V).naturality (P.d i j)).symm

private theorem slicePushforward_hom_eq_id (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (I : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :
    (sliceModulePushforwardIso u (ringedSiteModuleMap u a) V).hom.app I = 𝟙 _ := by
  ext T x
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryTranspose (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    (((ringedSliceModuleAdjunction (Over.post (X := V) u)
      (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ)).homEquiv _ _
        (ringedSlicePullbackComplexMap u a V P)) =
      (CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).map
        (((ringedSliceModuleAdjunction u a).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      (ringedSlicePushforwardComplexIso u a V
        (((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj P)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  have h := (sliceModulePullbackMap_unit u (ringedSiteModuleMap u a) V (P.X n)).symm
  rw [slicePushforward_hom_eq_id u a V] at h
  exact h

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem epsilon_isIso
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)]
    (e : RingedSliceDerivedImage.{u, w} u a)
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hf : ∀ n : ℤ, (P.X n).IsFlat) :
    IsIso (e.epsilon.app P) := by
  obtain ⟨e₀, he₀⟩ := ringedSliceDerivedImage_exists u a
  have := e.isLeftDerived
  have := e₀.isLeftDerived
  let t := e.left.leftDerivedLift e.epsilon
    (HomologicalComplex.quasiIso _ (.up ℤ)) e₀.left e₀.epsilon
  have : IsIso t :=
    (e.left.isLeftDerivedFunctor_iff_isIso_leftDerivedLift e.epsilon
      (HomologicalComplex.quasiIso _ (.up ℤ)) e₀.left e₀.epsilon).1 e₀.isLeftDerived
  have hg : IsIso (e₀.epsilon.app P) := he₀ P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP) hf
  have ht : t.app (DerivedCategory.Q.obj P) ≫ e.epsilon.app P = e₀.epsilon.app P :=
    e.left.leftDerived_fac_app e.epsilon
      (HomologicalComplex.quasiIso _ (.up ℤ)) e₀.left e₀.epsilon P
  have : IsIso (t.app (DerivedCategory.Q.obj P) ≫ e.epsilon.app P) := ht.symm ▸ hg
  exact IsIso.of_isIso_comp_left (t.app (DerivedCategory.Q.obj P)) (e.epsilon.app P)

attribute [local irreducible] ringedSliceRestriction ringedSliceRestrictionFactors
  HomologicalComplex.quasiIso ringedSliceModulePullback ringedSliceModulePushforward
  ringedSliceModuleAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
-- The comparison uses both complex and derived adjunction presentations.
/-- The canonical derived slice comparison is Q of the ordinary comparison on every
flat-term K-flat representative, and its direct-image comparison is the exchange mate.
The hypothesis `hnormal` specifies the canonical right-derived comparison on all
complexes, exactly as in `ringedDerivedSliceLocalization`; `d.lambda` is theta in
this statement's orientation. The four factors in the representative equation retain
both restriction factorizations and both derived pullback model comparisons.
Source: Stacks Tags 04J0, 07A6, 07A7 and 08FI
(blueprint: lem-weil-pbc-ringed-slice-pullback-mate-normalization).

Proof:
1. Exact slice restriction preserves independent K-flatness, and restriction of a
flat module is flat. The localized set pullback preserves finite limits.
2. Use the existing normalized derived-image existence theorem on each site. Uniqueness
of left derived functors and its factorization identity transfer invertibility of the
model comparisons to the given presentations e and l.
3. Apply the ordinary inverse-mate unit identity in each degree. The ordinary
pushforward comparison is the sectionwise identity. This computes the local ordinary
transpose of ringedSlicePullbackComplexMap without any injectivity hypothesis.
4. Apply the local derived adjunction Hom bijection to the representative equation.
Its left transpose is computed by the square unit identity, beta naturality, global
normalization at the identity of the actual pulled-back complex, and hnormal at that
complex. Naturality of the restriction factorization moves its source comparison to
the front. Local normalization and step 3 give the same right transpose. Injectivity
of the Hom bijection gives the equation with all comparison arrows retained.
5. The square counit identity and mateEquiv_counit give the same inverse transpose
for beta and the mate of lambda. Injectivity and natural-transformation extensionality
prove the exchange identity and its stated counit-transpose formula. -/
theorem ringedSlicePullbackMateNormalization
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (u.obj V)))]
    (e : RingedSliceDerivedImage.{u, w} u a)
    (l : RingedSliceDerivedImage.{u, w} (Over.post (X := V) u)
      (localizedRingedSiteMap u a V))
    (d : RingedSliceAdjunctionSquare e.adjunction l.adjunction
      (ringedSliceRestriction.{u, w} R V) (ringedSliceRestriction.{u, w} S (u.obj V)))
    (hnormal : ∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ),
      (ringedSliceRestriction.{u, w} R V).map
          (X := DerivedCategory.Q.{w}.obj
            (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I))
          (Y := e.right.obj (DerivedCategory.Q.{w}.obj I)) (e.eta.app I) ≫
        d.beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
        l.right.map
          (X := (ringedSliceRestriction.{u, w} S (u.obj V)).obj (DerivedCategory.Q.{w}.obj I))
          (Y := DerivedCategory.Q.{w}.obj
            ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I))
          ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app I) =
      (ringedSliceRestrictionFactors.{u, w} R V).hom.app
          (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.{w}.map (ringedSlicePushforwardComplexIso u a V I).hom ≫
        l.eta.app ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u}
          J S (u.obj V)).obj I)) :
    (∀ (P : CochainComplex (SheafOfModules.{u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ n : ℤ, (P.X n).IsFlat) →
      CochainComplex.IsKFlatIndependentCoefficients
          ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P) ∧
        (∀ n : ℤ, IsFlat (R := R.over V)
          (((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P).X n)) ∧
        IsIso (e.epsilon.app P) ∧
        IsIso (l.epsilon.app
          ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P)) ∧
        d.lambda.hom.app (DerivedCategory.Q.{w}.obj P) ≫
            (ringedSliceRestriction.{u, w} S (u.obj V)).map (e.epsilon.app P) ≫
            (ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app
              (((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj P) =
          l.left.map ((ringedSliceRestrictionFactors.{u, w} R V).hom.app P) ≫
            l.epsilon.app
              ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P) ≫
            DerivedCategory.Q.{w}.map (ringedSlicePullbackComplexMap u a V P)) ∧
      (mateEquiv e.adjunction l.adjunction
        (TwoSquare.mk _ _ _ _ d.lambda.hom)).natTrans = d.beta.hom ∧
      ∀ M : ringedSiteDerived.{u, w} S,
        l.adjunction.homEquiv _ _
          (d.lambda.hom.app (e.right.obj M) ≫
            (ringedSliceRestriction.{u, w} S (u.obj V)).map (e.adjunction.counit.app M)) =
          d.beta.hom.app M  := by
  classical
  let : K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let : (K.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let : (J.over (u.obj V)).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  have hcounit (M : ringedSiteDerived.{u, w} S) :
      l.adjunction.homEquiv _ _
        (d.lambda.hom.app (e.right.obj M) ≫
          (ringedSliceRestriction.{u, w} S (u.obj V)).map
            (e.adjunction.counit.app M)) = d.beta.hom.app M := by
    apply (l.adjunction.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (d.counit M).symm
  refine ⟨?_, ?_, hcounit⟩
  · intro P hP hf
    have hres := (ringedSite_restriction_exact_kflat.{u, u, u}
      K R V).2.2 P hP
    have hflat : ∀ n : ℤ, IsFlat (R := R.over V)
        (((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P).X n) :=
      by
        intro n
        change IsFlat (R := R.over V) ((P.X n).over V)
        exact isFlat_over (R := R) (P.X n) V (hf n)
    have hl := sliceSetPullback_preservesFiniteLimits (K := K) (J := J) u V
    have := hl
    refine ⟨hres, hflat, epsilon_isIso u a e P hP hf,
      epsilon_isIso (K := K.over V) (J := J.over (u.obj V))
        (R := R.over V) (S := S.over (u.obj V)) (Over.post (X := V) u)
        (localizedRingedSiteMap u a V) l
        ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P)
        hres hflat, ?_⟩
    let F := (ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)
    let r := CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V
    let s := CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)
    let j := ringedSliceRestriction.{u, w} R V
    let k := ringedSliceRestriction.{u, w} S (u.obj V)
    let cr := ringedSliceRestrictionFactors.{u, w} R V
    let cs := ringedSliceRestrictionFactors.{u, w} S (u.obj V)
    let adj := (ringedSliceModuleAdjunction u a).mapHomologicalComplex (.up ℤ)
    let adjv := (ringedSliceModuleAdjunction (Over.post (X := V) u)
      (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ)
    let σ := ringedSlicePullbackComplexMap u a V P
    let QA := DerivedCategory.Q.{w} (C := SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    let QB := DerivedCategory.Q.{w} (C := SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    let QAv := DerivedCategory.Q.{w} (C := SheafOfModules.{u}
      (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over V))
    let QBv := DerivedCategory.Q.{w} (C := SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (u.obj V)))
    apply normalizeRepresentative adj adjv r s QA QB QAv QBv
      e.adjunction l.adjunction j k cr cs e.epsilon e.eta l.epsilon l.eta d P
      (ringedSlicePushforwardComplexIso u a V (F.obj P)).hom σ
    · exact ordinaryTranspose u a V P
    · exact unitOfNormalized adj QA QB e.adjunction e.epsilon e.eta e.normalized P
    · exact hnormal (F.obj P)
    · exact l.normalized (r.obj P) (s.obj (F.obj P)) σ
  · apply NatTrans.ext
    funext M
    apply (l.adjunction.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    exact (mateEquiv_counit e.adjunction l.adjunction
      (TwoSquare.mk _ _ _ _ d.lambda.hom) M).trans (d.counit M).symm

end SheafOfModules
