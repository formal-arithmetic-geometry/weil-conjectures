/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.Paper.CompletedTensorUnitInsertionData
import all Sheaf.Paper.ConstantCompletionEquivalence
import all Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.SixFunctors.RingedDerivedTensorLift
import all Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Canonical native derived tensor comparison for constant coefficients -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe uB vB uE vE u
open CategoryTheory CategoryTheory.Limits MonoidalCategory WeilConjectures Opposite
namespace CategoryTheory.ConstantCompletion

-- Use the named derived functor and its comparison throughout the normalization proof.
attribute [local irreducible] derivedPull

private theorem square_cancel {D : Type*} [Category D] {X Y Z W : D}
    (f : X ⟶ Y) (a : X ⟶ W) (q : Z ≅ W) (r : Z ≅ Y)
    (h : f = a ≫ q.inv ≫ r.hom) : f ≫ r.inv ≫ q.hom = a := by
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem five_cancel {C : Type*} [Category C] {X U V Y Z W : C}
    (f : X ⟶ U) (g : U ⟶ V) (h : V ⟶ Y) (a : X ⟶ W)
    (q : Z ≅ W) (r : Z ≅ Y) (H : f ≫ g ≫ h = a ≫ q.inv ≫ r.hom) :
    f ≫ g ≫ h ≫ r.inv ≫ q.hom = a := by
  have h := square_cancel (f ≫ g ≫ h) a q r H
  simpa only [Category.assoc] using h

private theorem normalize_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : D × D ⥤ D)
    {X Y : C} {A B A' B' Z W : D}
    {f f' : X ⟶ Y} {g : F.obj Y ⟶ T.obj (A, B)}
    {p p' : A ⟶ A'} {q q' : B ⟶ B'} {a a' : F.obj X ⟶ W}
    (s : Z ≅ W) (r : Z ≅ T.obj (A', B')) {k : Z ⟶ T.obj (A', B')}
    (hf : f = f') (hp : p = p') (hq : q = q') (ha : a = a') (hk : k = r.hom)
    (H : F.map f ≫ g ≫ T.map (Prod.mkHom p q) = a ≫ s.inv ≫ k) :
    F.map f' ≫ g ≫ T.map (Prod.mkHom p' q') ≫ r.inv ≫ s.hom = a' := by
  rw [hf, hp, hq, ha, hk] at H
  exact five_cancel _ _ _ _ s r H

private theorem kan_unprecomp
    {A B D H : Type*} [Category A] [Category B] [Category D] [Category H]
    (P : A ⥤ B) (Q : B ⥤ D) (T : D ⥤ H) (G : B ⥤ H) (ε : Q ⋙ T ⟶ G)
    [((Functor.whiskeringLeft A B H).obj P).Faithful]
    [T.IsRightKanExtension
      ((Functor.associator P Q T).hom ≫ Functor.whiskerLeft P ε)] :
    T.IsRightKanExtension ε := by
  let α := (Functor.associator P Q T).hom ≫ Functor.whiskerLeft P ε
  let K := (Functor.whiskeringLeft A B H).obj P
  let lift (s : Functor.RightExtension Q G) : s.left ⟶ T :=
    T.liftOfIsRightKanExtension α s.left
      ((Functor.associator P Q s.left).hom ≫ Functor.whiskerLeft P s.hom)
  have fac (s : Functor.RightExtension Q G) :
      Functor.whiskerLeft Q (lift s) ≫ ε = s.hom := by
    apply K.map_injective
    apply NatTrans.ext
    funext X
    have h := congrArg (fun t ↦ t.app X)
      (T.liftOfIsRightKanExtension_fac α s.left
        ((Functor.associator P Q s.left).hom ≫ Functor.whiskerLeft P s.hom))
    change (lift s).app (Q.obj (P.obj X)) ≫ (𝟙 _ ≫ ε.app (P.obj X)) =
      𝟙 _ ≫ s.hom.app (P.obj X) at h
    change (lift s).app (Q.obj (P.obj X)) ≫ ε.app (P.obj X) = s.hom.app (P.obj X)
    simpa only [Category.id_comp] using h
  clear_value lift
  refine ⟨⟨IsTerminal.ofUniqueHom
    (fun s ↦ CostructuredArrow.homMk (lift s) (fac s)) ?_⟩⟩
  intro s m
  apply CostructuredArrow.hom_ext
  apply T.hom_ext_of_isRightKanExtension α
  apply NatTrans.ext
  funext X
  have h := congrArg (fun t ↦ t.app (P.obj X)) (CostructuredArrow.w m)
  have h' := congrArg (fun t ↦ t.app (P.obj X)) (fac s)
  change m.left.app (Q.obj (P.obj X)) ≫ (𝟙 _ ≫ ε.app (P.obj X)) =
    (lift s).app (Q.obj (P.obj X)) ≫ (𝟙 _ ≫ ε.app (P.obj X))
  change m.left.app (Q.obj (P.obj X)) ≫ ε.app (P.obj X) = s.hom.app (P.obj X) at h
  change (lift s).app (Q.obj (P.obj X)) ≫ ε.app (P.obj X) = s.hom.app (P.obj X) at h'
  simpa only [Category.id_comp] using h.trans h'.symm

private theorem homotopy_counit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ T ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [T.IsRightKanExtension α] :
    ∃ ε : DerivedCategory.Qh ⋙ T ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh,
      T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) ∧
      ∀ P : CochainComplex A ℤ, derivedPullbackComplexComparison F T ε P = α.app P := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ H ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let τ : q ⋙ (DerivedCategory.Qh ⋙ T) ⟶ q ⋙ H :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight i.hom T ≫ α ≫ j.inv
  let ε : DerivedCategory.Qh ⋙ T ⟶ H := Quotient.natTransLift _ τ
  have he : (Functor.associator q DerivedCategory.Qh T).hom ≫
      Functor.whiskerLeft q ε = Functor.whiskerRight i.hom T ≫ α ≫ j.inv := by
    ext P
    change 𝟙 _ ≫ τ.app P = _
    simp only [τ, NatTrans.comp_app, Functor.associator_inv_app, Category.id_comp]
  have hkan : T.IsRightKanExtension
      ((Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε) := by
    rw [he]
    exact kan_change T i.symm j.symm α
  have : T.IsRightKanExtension ε := kan_unprecomp q DerivedCategory.Qh T H ε
  refine ⟨ε, ⟨inferInstance⟩, ?_⟩
  intro P
  have h : ε.app (q.obj P) = T.map (i.hom.app P) ≫ α.app P ≫ j.inv.app P := by
    simpa only [NatTrans.comp_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp] using
      congrArg (fun t ↦ t.app P) he
  have hj : j.hom.app P =
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    simp only [j, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
    exact Category.id_comp _
  change T.map (i.inv.app P) ≫ ε.app (q.obj P) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
      (DerivedCategory.quotientCompQhIso B).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) = _
  rw [← hj, h]
  simp only [Category.assoc]
  rw [← T.map_comp_assoc, i.inv_hom_id_app, T.map_id, Category.id_comp]
  simp

-- The model is fixed; keep the sheafification tensor construction folded below.
attribute [local irreducible] SheafOfModules.monoidalCategory HasDerivedCategory.standard
attribute [local irreducible] constantSheaf

-- Match the native and flat-term representative interfaces explicitly.
/-- Ordinary inverse image has its native derived symmetric monoidal comparison,
normalized by the canonical cochain comparison on flat-term K-flat representatives.
Source: Stacks Project, sites-cohomology.tex, lemma-pullback-tensor-product (Tag 07A4)
and lemma-symmetric-monoidal-derived (Tag 0FPT).
(blueprint: lem-pur-constant-native-pullback-monoidal).

Proof: choose the canonical ordinary pure-tensor comparison for the scalar extension
pullback. Its cochain comparison respects reassociation, signed symmetry and action
unitors. On flat-term K-flat complexes use the native tensorIso to conjugate that
comparison through the left-derived counit. Pullback preserves these resolving
complexes. The native representative tensor comparison and its localization are
fully faithful, so this defines a unique natural isomorphism mu on derived inputs,
with exactly ConstantTensorNormalization's equation. The native derived associator,
braiding and unitors are represented by the same cochain constraints. Consequently
the four cochain coherence equations give the corresponding derived equations on
resolving representatives, hence on all objects by their essential surjectivity.
The degree-zero scalar-action unit gives e. Take delta=mu and eta=e; the inherited
naturality, associativity and unit equations supply the oplax monoidal structure. -/
theorem constantNativePullbackMonoidal
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)}
    (F : InverseImageData L) (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : L ⊣ V) [PreservesFiniteLimits L] (A : Type u) [CommRing A]
    (G : Mod (constant JD A) ⥤ Mod (constant JC A))
    (aM : pull F (constantMap F A) ⊣ G)
    (RF : D (constant JD A) ⥤ D (constant JC A))
    (aD : (derivedPull F V adj (constantMap F A)).functor ⊣ RF) :
    letI := constantDerivedMonoidal JC A
    letI := constantDerivedSymmetric JC A
    letI := constantDerivedMonoidal JD A
    letI := constantDerivedSymmetric JD A
    letI LF := (derivedPull F V adj (constantMap F A)).functor
    ∃ (k : ConstantTensorData F A)
      (μ : constantDerivedTensor JC A ⋙ LF ≅ (LF.prod LF) ⋙ constantDerivedTensor JD A)
      (e : LF.obj (𝟙_ (D (constant JC A))) ≅ 𝟙_ (D (constant JD A)))
      (o : LF.OplaxMonoidal),
      ConstantTensorNormalization F V adj A k μ ∧
      (∀ X W : D (constant JC A), o.δ X W = μ.hom.app (X, W)) ∧
      o.η = e.hom ∧
      (∀ X W : D (constant JC A),
        μ.hom.app (X, W) ≫ (β_ (LF.obj X) (LF.obj W)).hom =
          LF.map (β_ X W).hom ≫ μ.hom.app (W, X)) := by
  classical
  dsimp only [ConstantTensorNormalization]
  generalize hd : derivedPull F V adj (constantMap F A) = d at aD ⊢
  obtain ⟨LF, α, hα, hαcomp⟩ := d
  let := HasDerivedCategory.standard (Mod (constant JC A))
  let := HasDerivedCategory.standard (Mod (constant JD A))
  let : MonoidalCategory (D (constant JC A)) := constantDerivedMonoidal JC A
  let : SymmetricCategory (D (constant JC A)) := constantDerivedSymmetric JC A
  let : MonoidalCategory (D (constant JD A)) := constantDerivedMonoidal JD A
  let : SymmetricCategory (D (constant JD A)) := constantDerivedSymmetric JD A
  let : LF.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (Mod (constant JC A)) (.up ℤ)) :=
    hα
  have : LF.IsRightKanExtension α :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension LF α
      (HomologicalComplex.quasiIso (Mod (constant JC A)) (.up ℤ))
  obtain ⟨ε, hε, hεcomp⟩ := homotopy_counit (pull F (constantMap F A)) LF α
  obtain ⟨⟨mC, adjC, evC⟩, hmC, TM_C, βC, hcC, hβC, htC⟩ :=
    CategoryTheory.ringedDerived_closed_symmetric_monoidal_native.{u, u, u} JC (constant JC A)
  dsimp only [CoefficientClosedStructure.monoidal] at hmC
  subst mC
  have hβC := eq_of_heq hβC
  subst βC
  obtain ⟨⟨mD, adjD, evD⟩, hmD, TM_D, βD, hcD, hβD, htD⟩ :=
    CategoryTheory.ringedDerived_closed_symmetric_monoidal_native.{u, u, u} JD (constant JD A)
  dsimp only [CoefficientClosedStructure.monoidal] at hmD
  subst mD
  have hβD := eq_of_heq hβD
  subst βD
  let YC : RingedDerivedComparisons.Site := {
    C := C
    J := JC
    A := constant JC A
    closed := ⟨constantDerivedMonoidal JC A, adjC, evC⟩
    model := TM_C
    symmetry := constantDerivedSymmetric JC A
    coherence := hcC }
  let XD : RingedDerivedComparisons.Site := {
    C := E
    J := JD
    A := constant JD A
    closed := ⟨constantDerivedMonoidal JD A, adjD, evD⟩
    model := TM_D
    symmetry := constantDerivedSymmetric JD A
    coherence := hcD }
  obtain ⟨rC, hrC⟩ := RingedDerivedComparisons.tensor_model YC
  obtain ⟨rD, hrD⟩ := RingedDerivedComparisons.tensor_model XD
  have hm {M N : Mod (constant JC A)} (f : M ⟶ N) :
      (pull F (constantMap F A)).map f = eqToHom (rfl :
        (pull F (constantMap F A)).obj M = _) ≫
        SheafOfModules.changeOfRingsHom (constantMap F A)
          ((F.algebra (constant JC A)).modules.obj M)
          ((F.algebra (constant JC A)).modules.map f) ≫ eqToHom (rfl :
            (pull F (constantMap F A)).obj N = _).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨⟨k⟩, _⟩ := SheafOfModules.canonicalRingedTensorComparison_existsUnique
    (constant JC A) (constant JD A) (F.rings.obj (constant JC A)) L
    (F.algebra (constant JC A)) (constantMap F A) (pull F (constantMap F A))
    (fun _ ↦ rfl) V adj hm
  let edge : SheafOfModules.RingedTensorEdge YC.corner XD.corner := {
    inverse := L
    direct := V
    adjunction := adj
    inverseRing := F.rings.obj (constant JC A)
    algebraic := F.algebra (constant JC A)
    ringMap := constantMap F A
    pullback := pull F (constantMap F A)
    object_eq := fun _ ↦ rfl
    map_eq := hm
    ordinaryTensor := k
    pushforward := G
    moduleAdjunction := aM
    left := LF
    epsilon := ε
    isLeftDerived := hε
    right := RF
    derivedAdjunction := aD }
  obtain ⟨t⟩ := RingedDerivedComparisons.tensorLift_exists edge rC rD hrC hrD
  let μ : constantDerivedTensor JC A ⋙ LF ≅
      (LF.prod LF) ⋙ constantDerivedTensor JD A := edge.tensorComparison rC rD
  let o : LF.OplaxMonoidal := t.monoidal.toOplaxMonoidal
  let e : LF.obj (𝟙_ (D (constant JC A))) ≅ 𝟙_ (D (constant JD A)) :=
    t.monoidal.εIso.symm
  refine ⟨k, μ, e, o, ?_, t.tensor_canonical, rfl, ?_⟩
  case refine_2 =>
    intro X W
    simpa only [t.tensor_canonical] using t.symmetric X W
  intro P Q hP hQ hfP hfQ
  have hp := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP
  have hq := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).1 hQ
  have hs := Classical.choose_spec
    (SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback
      L V adj (F.algebra (constant JC A)) (constantMap F A)
      (pull F (constantMap F A)) (fun _ ↦ rfl) hm LF ε hε
      YC.corner.mateFlat XD.corner.mateFlat (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
      YC.closed.tensor XD.closed.tensor rC.representative rD.representative k G aM).2.exists
  obtain ⟨hp', hq', hsquare⟩ := hs P Q ⟨hp, hfP⟩ ⟨hq, hfQ⟩
  have hP' := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2 hp'.1
  have hQ' := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2 hq'.1
  refine ⟨hP', hQ', ?_⟩
  have hc (P Q : Cx (constant JC A)) (hp) (hq) (hfP) (hfQ) :
      rC.representative.hom.app (⟨P, ⟨hp, hfP⟩⟩, ⟨Q, ⟨hq, hfQ⟩⟩) =
        (RingedDerivedNative.tensorIso.{u, u, u} JC (constant JC A) P Q
          (Or.inl ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp))).hom := by
    exact (hrC P Q ⟨hp, hfP⟩ ⟨hq, hfQ⟩).trans
      (congrArg Iso.hom (eq_of_heq (htC P Q
        ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp)
        ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).2 hq))))
  have hd (P Q : Cx (constant JD A)) (hp) (hq) (hfP) (hfQ) :
      rD.representative.hom.app (⟨P, ⟨hp, hfP⟩⟩, ⟨Q, ⟨hq, hfQ⟩⟩) =
        (RingedDerivedNative.tensorIso.{u, u, u} JD (constant JD A) P Q
          (Or.inl ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp))).hom := by
    exact (hrD P Q ⟨hp, hfP⟩ ⟨hq, hfQ⟩).trans
      (congrArg Iso.hom (eq_of_heq (htD P Q
        ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp)
        ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).2 hq))))
  have hsource := hc P Q hp hq hfP hfQ
  have htarget := hd _ _ hp'.1 hq'.1 hp'.2 hq'.2
  change LF.map _ ≫ μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
    (constantDerivedTensor JD A).map _ = _ at hsquare
  clear_value μ
  let q := DerivedCategory.Q.mapIso (k.totalIso (constant JC A) (constant JD A)
    (F.rings.obj (constant JC A)) L (F.algebra (constant JC A)) (constantMap F A)
    (pull F (constantMap F A)) (fun _ ↦ rfl) G aM P Q)
  let r := RingedDerivedNative.tensorIso.{u, u, u} JD (constant JD A)
    (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj P)
    (((pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj Q) (Or.inl hP')
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    have H := normalize_square LF (constantDerivedTensor JD A) q r
      hsource (hεcomp P) (hεcomp Q)
      (hεcomp ((WeilConjectures.coefficientTotalTensor.{u, u, u}
        JC (constant JC A)).obj (P, Q))) htarget hsquare
    simp only [q, r, Functor.mapIso_hom,
      SheafOfModules.CanonicalRingedTensorComparison.totalIso, asIso_hom] at H
    delta constantDerivedTensor constantDerivedMonoidal D
      CategoryTheory.ConstantCompletion.Q Mod siteModuleRings ringedSiteModules at H ⊢
    exact H

end CategoryTheory.ConstantCompletion
