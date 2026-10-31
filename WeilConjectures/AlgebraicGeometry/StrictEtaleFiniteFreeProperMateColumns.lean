/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictEtaleFiniteFreeScalarCoordinates
public import WeilConjectures.AlgebraicGeometry.StrictEtaleIsomorphicStageProjectionInterfaces
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.EtaleCompactSupportScalarAction
import WeilConjectures.AlgebraicGeometry.StrictEtaleFiniteFreeScalarExact
import all WeilConjectures.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates

/-! # Basis columns of the proper coefficient mate

Source: Zheng, Construction 5.15 and Lemma 5.16.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
open scoped ChangeOfRings
universe a b c d av bv cv dv

private theorem finiteFreeUnitColumn
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{av} A] [Category.{bv} B] [Category.{cv} C] [Category.{dv} D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {S : A ⥤ C} {U : C ⥤ A} {T : B ⥤ D} {V : D ⥤ B}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : S ⊣ U) (t : T ⊣ V)
    (e : S ⋙ L' ≅ L ⋙ T) (M : B) :
    s.unit.app (R.obj M) ≫
      U.map ((mateEquiv adj adj' (.mk _ _ _ _ e.hom)).natTrans.app M) ≫
      ((conjugateIsoEquiv (adj.comp t) (s.comp adj') e).symm.hom.app (T.obj M)) =
        R.map (t.unit.app M) := by
  let m := mateEquiv adj adj' (.mk _ _ _ _ e.hom)
  let d := conjugateIsoEquiv (adj.comp t) (s.comp adj') e
  have hd : (mateEquiv t s m).natTrans = d.hom :=
    iterated_mateEquiv_conjugateEquiv adj adj' s t (.mk _ _ _ _ e.hom)
  have h := unit_mateEquiv t s m M
  change R.map (t.unit.app M) ≫ (mateEquiv t s m).natTrans.app (T.obj M) =
    s.unit.app (R.obj M) ≫ U.map (m.natTrans.app M) at h
  rw [hd] at h
  apply (cancel_mono (d.hom.app (T.obj M))).1
  change (s.unit.app (R.obj M) ≫ U.map (m.natTrans.app M) ≫
    d.inv.app (T.obj M)) ≫ d.hom.app (T.obj M) = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact h.symm


universe u
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private def strictEtaleProperRestrictionIso
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
    (n : ℕ)
    (e : (TY.level n).derived ⋙ (SB.properDerived.level n).inverse ≅
      (SA.properDerived.level (index n)).inverse ⋙ (TZ.level n).derived) :
    (SB.properDerived.level n).direct ⋙ (TY.level n).restriction ≅
      (TZ.level n).restriction ⋙ (SA.properDerived.level (index n)).direct :=
  (conjugateIsoEquiv
    ((SA.properDerived.level (index n)).adjunction.comp (TZ.level n).derivedAdj)
    ((TY.level n).derivedAdj.comp (SB.properDerived.level n).adjunction) e).symm


private def levelAction (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (t r : O) (n : ℕ) : 𝟭 (strictEtaleLevel T O t n) ⟶ 𝟭 _ where
  app := levelScalar T O t r n
  naturality M N f := levelScalar_naturality T O t r n M N f

private def levelDerivedAction (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (t r : O) (n : ℕ) : 𝟭 (DerivedCategory (strictEtaleLevel T O t n)) ⟶ 𝟭 _ := by
  let Q := DerivedCategory.Q (C := strictEtaleLevel T O t n)
  let W := HomologicalComplex.quasiIso (strictEtaleLevel T O t n) (.up ℤ)
  letI : Localization.Lifting Q W Q (𝟭 _) := ⟨Functor.rightUnitor Q⟩
  exact Localization.liftNatTrans Q W Q Q (𝟭 _) (𝟭 _)
    (whiskerRight ((levelAction T O t r n).mapHomologicalComplex (.up ℤ)) Q)

private theorem levelDerivedAction_rep
    (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (t r : O) (n : ℕ)
    (P : CochainComplex (strictEtaleLevel T O t n) ℤ) :
    (levelDerivedAction T O t r n).app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
        (((levelAction T O t r n).mapHomologicalComplex (.up ℤ)).app P) := by
  dsimp only [levelDerivedAction]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Functor.rightUnitor_hom_app,
    Functor.rightUnitor_inv_app, whiskerRight_app, Category.comp_id]
  exact Category.id_comp _

private theorem inverseDerived_preserves_action
    {O : Type (u + 1)} [CommRing O] {t : O} {X Y : Scheme.{u}} {g : X ⟶ Y}
    (S : StrictEtaleOrdinaryImage O t g)
    (r : O) (n : ℕ)
    (D : CoefficientDerivedImage (S.lift n).modules (S.right n) (S.levelAdj n))
    (M : DerivedCategory (strictEtaleLevel Y O t n)) :
    D.inverse.map ((levelDerivedAction Y O t r n).app M) =
      (levelDerivedAction X O t r n).app (D.inverse.obj M) := by
  have he : whiskerRight (levelDerivedAction Y O t r n) D.inverse =
      whiskerLeft D.inverse (levelDerivedAction X O t r n) := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel Y O t n) (.up ℤ))
    intro P
    change D.inverse.map
      ((levelDerivedAction Y O t r n).app (DerivedCategory.Q.obj P)) = _
    rw [levelDerivedAction_rep]
    apply (cancel_mono (D.inverseFactors.hom.app P)).mp
    have hc : ((S.lift n).modules.mapHomologicalComplex (.up ℤ)).map
        (((levelAction Y O t r n).mapHomologicalComplex (.up ℤ)).app P) =
      ((levelAction X O t r n).mapHomologicalComplex (.up ℤ)).app
        (((S.lift n).modules.mapHomologicalComplex (.up ℤ)).obj P) := by
      apply HomologicalComplex.hom_ext
      intro i
      exact inverse_levelScalar S r n (P.X i)
    calc
      _ = D.inverseFactors.hom.app P ≫ DerivedCategory.Q.map
          (((S.lift n).modules.mapHomologicalComplex (.up ℤ)).map
            (((levelAction Y O t r n).mapHomologicalComplex (.up ℤ)).app P)) :=
        D.inverseFactors.hom.naturality _
      _ = D.inverseFactors.hom.app P ≫ (levelDerivedAction X O t r n).app
          (DerivedCategory.Q.obj
            (((S.lift n).modules.mapHomologicalComplex (.up ℤ)).obj P)) := by
        rw [hc, levelDerivedAction_rep]
      _ = (levelDerivedAction X O t r n).app
          (D.inverse.obj (DerivedCategory.Q.obj P)) ≫
            D.inverseFactors.hom.app P :=
        (levelDerivedAction X O t r n).naturality _
  exact congr_app he M

private theorem directDerived_preserves_action
    {O : Type (u + 1)} [CommRing O] {t : O} {X Y : Scheme.{u}} {g : X ⟶ Y}
    (S : StrictEtaleOrdinaryImage O t g)
    (r : O) (n : ℕ)
    (D : CoefficientDerivedImage (S.lift n).modules (S.right n) (S.levelAdj n))
    (M : DerivedCategory (strictEtaleLevel X O t n)) :
    D.direct.map ((levelDerivedAction X O t r n).app M) =
      (levelDerivedAction Y O t r n).app (D.direct.obj M) :=
  adjoint_preserves_right D.adjunction
    (levelDerivedAction Y O t r n) (levelDerivedAction X O t r n)
    (inverseDerived_preserves_action S r n D) M


private theorem scalarUnit_rep
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {T : A ⥤ B} {R : B ⥤ A} [T.Additive] [R.Additive] {adj : T ⊣ R}
    {KFlat : CochainComplex A ℤ → Prop}
    (L : DerivedCoefficientScalarExtension T R adj KFlat) (P : CochainComplex A ℤ) :
    L.derivedAdj.unit.app (DerivedCategory.Q.obj P) ≫
      L.restriction.map (L.counit.app P) ≫
      L.restrictionFactors.hom.app ((T.mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map
          (((adj.mapHomologicalComplex (.up ℤ)).unit).app P) := by
  have h := L.transpose P ((T.mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
  simp only [Adjunction.homEquiv_unit] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  have hh := congrArg
    (fun f ↦ f ≫ L.restrictionFactors.hom.app
      ((T.mapHomologicalComplex (.up ℤ)).obj P)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh

private theorem scalarMate_action_column
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {S : A ⥤ C} {U : C ⥤ A} {T : B ⥤ D} {V : D ⥤ B}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : S ⊣ U) (t : T ⊣ V)
    (e : S ⋙ L' ≅ L ⋙ T)
    (bC : 𝟭 C ⟶ 𝟭 C) (bD : 𝟭 D ⟶ 𝟭 D)
    (hb : ∀ N, R'.map (bD.app N) = bC.app (R'.obj N)) (M : B) :
    (s.unit.app (R.obj M) ≫ U.map (bC.app (S.obj (R.obj M)))) ≫
        U.map ((mateEquiv adj adj' (.mk _ _ _ _ e.hom)).natTrans.app M) ≫
        ((conjugateIsoEquiv (adj.comp t) (s.comp adj') e).symm.hom.app (T.obj M)) =
      R.map (t.unit.app M ≫ V.map (bD.app (T.obj M))) := by
  let m := (mateEquiv adj adj' (.mk _ _ _ _ e.hom)).natTrans
  let d := (conjugateIsoEquiv (adj.comp t) (s.comp adj') e).symm
  have hm : bC.app (S.obj (R.obj M)) ≫ m.app M =
      m.app M ≫ R'.map (bD.app (T.obj M)) := by
    rw [hb]
    exact (bC.naturality (m.app M)).symm
  have hd := d.hom.naturality (bD.app (T.obj M))
  change U.map (R'.map (bD.app (T.obj M))) ≫ d.hom.app (T.obj M) =
      d.hom.app (T.obj M) ≫ R.map (V.map (bD.app (T.obj M))) at hd
  change (s.unit.app (R.obj M) ≫ U.map (bC.app (S.obj (R.obj M)))) ≫
      U.map (m.app M) ≫ d.hom.app (T.obj M) = _
  simp only [Category.assoc]
  rw [← U.map_comp_assoc, hm, U.map_comp, Category.assoc, hd]
  rw [← Category.assoc, ← Category.assoc]
  have hu : (s.unit.app (R.obj M) ≫ U.map (m.app M)) ≫
      d.hom.app (T.obj M) = R.map (t.unit.app M) := by
    simpa only [Category.assoc] using finiteFreeUnitColumn adj adj' s t e M
  rw [hu]
  exact (R.map_comp _ _).symm
private theorem siteTensorUnit_apply
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (n : ℕ)
    (M : strictEtaleLevel T O ell (index n)) (V : T.Etaleᵒᵖ) (x : M.val.obj V) :
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)).unit.app M).val.app V x =
      (toSheafify T.smallEtaleTopology
        (changeOfRingsPresheaf (a.sheaf T n) M).presheaf).app V
        ((1 : (coefficientQuotientSheaf (J := T.smallEtaleTopology) O' mu n).obj.obj V)
        ⊗ₜ[(coefficientQuotientSheaf (J := T.smallEtaleTopology)
            O ell (index n)).obj.obj V, ((a.sheaf T n).hom.app V).hom] x) := by
  dsimp only [Functor.comp_obj]
  have hn : SiteCoefficientTensorAdjunctionNormalized.{u + 1, u, u + 1} (a.sheaf T n)
      (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)) :=
    (siteCoefficientTensorAdj_exists (a.sheaf T n)).exists.choose_spec
  have h := hn M _ (𝟙 _) V x
  simp only [Adjunction.homEquiv_unit] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  simp only [ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at h
  exact h

private theorem scalarPure_smul
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (n : ℕ)
    (M : strictEtaleLevel T O ell (index n)) (V : T.Etaleᵒᵖ)
    (s : (coefficientQuotientSheaf (J := T.smallEtaleTopology) O' mu n).obj.obj V)
    (x : M.val.obj V) :
    (show ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).obj M).val.obj V
      from (toSheafify T.smallEtaleTopology
      (changeOfRingsPresheaf (a.sheaf T n) M).presheaf).app V
      (s ⊗ₜ[(coefficientQuotientSheaf (J := T.smallEtaleTopology)
        O ell (index n)).obj.obj V, ((a.sheaf T n).hom.app V).hom] x)) =
    s • (show ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).obj M).val.obj V
      from (toSheafify T.smallEtaleTopology
      (changeOfRingsPresheaf (a.sheaf T n) M).presheaf).app V
      ((1 : (coefficientQuotientSheaf (J := T.smallEtaleTopology) O' mu n).obj.obj V)
        ⊗ₜ[(coefficientQuotientSheaf (J := T.smallEtaleTopology)
          O ell (index n)).obj.obj V, ((a.sheaf T n).hom.app V).hom] x)) := by
  exact CategoryTheory.FiniteFreeScalarProof.scalarSection_smul.{u + 1, u, u + 1}
    T.smallEtaleTopology (a.sheaf T n)
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)) (fun _ ↦ rfl) M V s x
private theorem levelScalar_apply (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (t r : O) (n : ℕ) (M : strictEtaleLevel T O t n) (V : T.Etaleᵒᵖ)
    (x : M.val.obj V) :
    (levelScalar T O t r n M).val.app V x = scalarSection T O t r n V • x := rfl

private theorem normalizedInclusion_unit_action
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}} {n : ℕ}
    (L : StrictEtaleLevelScalar a T n) {r : ℕ}
    (b : Module.Basis (Fin r) (O ⧸ Ideal.span {ell} ^ (index n + 1))
      ((ModuleCat.restrictScalars (a.ring n)).obj
        (ModuleCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))
          (O' ⧸ Ideal.span {mu} ^ (n + 1)))))
    (ι : StrictEtaleLevelScalarInclusions L r)
    (hι : StrictEtaleLevelBasisCoordinates L b ι)
    (M : DerivedCategory (strictEtaleLevel T O ell (index n))) (i : Fin r) :
    ι M i = L.derivedAdj.unit.app M ≫ L.restriction.map
      ((levelDerivedAction T O' mu (Quotient.out (b i)) n).app (L.derived.obj M)) := by
  classical
  let : Algebra (O ⧸ Ideal.span {ell} ^ (index n + 1))
      (O' ⧸ Ideal.span {mu} ^ (n + 1)) := (a.ring n).toAlgebra
  change Module.Basis (Fin r) (O ⧸ Ideal.span {ell} ^ (index n + 1))
    (O' ⧸ Ideal.span {mu} ^ (n + 1)) at b
  let z := levelDerivedAction T O' mu (Quotient.out (b i)) n
  let α : 𝟭 _ ⟶ L.derived ⋙ L.restriction :=
    { app := fun N ↦ ι N i
      naturality := fun N N' f ↦ hι.1 N N' f i }
  let β : 𝟭 _ ⟶ L.derived ⋙ L.restriction :=
    L.derivedAdj.unit ≫ whiskerRight (whiskerLeft L.derived z) L.restriction
  suffices α = β from congr_app this M
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  let E := siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)
  let R := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
  let EC := E.mapHomologicalComplex (.up ℤ)
  let RC := R.mapHomologicalComplex (.up ℤ)
  let t : EC.obj P ⟶ EC.obj P :=
    ((levelAction T O' mu (Quotient.out (b i)) n).mapHomologicalComplex (.up ℤ)).app (EC.obj P)
  let j : P ⟶ RC.obj (EC.obj P) :=
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)).mapHomologicalComplex
      (.up ℤ)).unit.app P
  let : IsIso L.counit :=
    (strictEtaleFiniteFreeScalarExact a T n L ⟨r, ⟨b⟩⟩).2
  obtain ⟨k, hk, hrep⟩ := hι.2.2 P i
  have ht : z.app (DerivedCategory.Q.obj (EC.obj P)) = DerivedCategory.Q.map t :=
    levelDerivedAction_rep T O' mu (Quotient.out (b i)) n (EC.obj P)
  have hz := z.naturality (L.counit.app P)
  change L.counit.app P ≫ z.app (DerivedCategory.Q.obj (EC.obj P)) =
      z.app (L.derived.obj (DerivedCategory.Q.obj P)) ≫ L.counit.app P at hz
  rw [ht] at hz
  have hR := L.restrictionFactors.hom.naturality (t)
  change L.restriction.map (DerivedCategory.Q.map t) ≫
      L.restrictionFactors.hom.app (EC.obj P) =
    L.restrictionFactors.hom.app (EC.obj P) ≫ DerivedCategory.Q.map (RC.map t) at hR
  have hk' : j ≫ RC.map t = k := by
    apply HomologicalComplex.hom_ext
    intro d
    apply SheafOfModules.hom_ext
    ext V x
    change ((j ≫ RC.map t).f d).val.app V x = (k.f d).val.app V x
    rw [hk d V x]
    change (levelScalar T O' mu (Quotient.out (b i)) n (E.obj (P.X d))).val.app V
        (((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)).unit.app
          (P.X d)).val.app V x) = _
    rw [siteTensorUnit_apply, levelScalar_apply]
    simp only [E, scalarSection, Ideal.Quotient.mk_out]
    exact (scalarPure_smul a T n (P.X d) V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj
            (CommRingCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))))).app V (b i)) x).symm
  change ι (DerivedCategory.Q.obj P) i =
    L.derivedAdj.unit.app (DerivedCategory.Q.obj P) ≫
      L.restriction.map (z.app (L.derived.obj (DerivedCategory.Q.obj P)))
  apply (cancel_mono (L.restriction.map (L.counit.app P) ≫
    L.restrictionFactors.hom.app (EC.obj P))).1
  simp only [Category.assoc]
  rw [hrep]
  symm
  calc
    _ = L.derivedAdj.unit.app (DerivedCategory.Q.obj P) ≫
        L.restriction.map (L.counit.app P) ≫
        L.restriction.map (DerivedCategory.Q.map t) ≫
        L.restrictionFactors.hom.app (EC.obj P) := by
      rw [← L.restriction.map_comp_assoc, ← hz, L.restriction.map_comp_assoc]
    _ = (L.derivedAdj.unit.app (DerivedCategory.Q.obj P) ≫
        L.restriction.map (L.counit.app P) ≫
        L.restrictionFactors.hom.app (EC.obj P)) ≫
          DerivedCategory.Q.map (RC.map t) := by rw [Category.assoc, Category.assoc, hR]
    _ = DerivedCategory.Q.map j ≫ DerivedCategory.Q.map (RC.map t) := by
      rw [scalarUnit_rep]
    _ = DerivedCategory.Q.map k := by rw [← DerivedCategory.Q.map_comp, hk']
/-- The restricted proper mate has the columns prescribed by a finite coefficient
basis. This is a map-identification statement; it asserts no invertibility of the
proper mate. The final matrix argument is performed by its consumer.
Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks, Tags 03CZ and 07A6
(blueprint: lem-pur-strict-etale-finite-free-proper-mate-columns).
Proof: conjugate the given inverse-image isomorphism under the composite scalar
and geometric adjunctions; its inverse gives the restriction/direct-image
comparison. The iterated-mate identity and the mate-unit equation show that the
restricted proper mate followed by this comparison takes the scalar unit to direct
image of the scalar unit. Multiplication by every quotient coefficient is preserved
by the algebraic inverse image, hence also by its right adjoint. Localize this
identity for the prescribed derived models. Multiplying the unit equation by b_i
and using naturality of the conjugate comparison gives the ith column. The
pure-tensor normalization of the supplied coordinate families identifies those
inclusions with the unit followed by multiplication by b_i. Their equality on
cochain representatives extends by faithful localization to every derived object.
No nonzero-rank or boundedness hypothesis is used. -/
theorem strictEtaleFiniteFreeProperMateColumns
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
    (n : ℕ)
    (e : (TY.level n).derived ⋙ (SB.properDerived.level n).inverse ≅
      (SA.properDerived.level (index n)).inverse ⋙ (TZ.level n).derived)
    {r : ℕ}
    (b : Module.Basis (Fin r) (O ⧸ Ideal.span {ell} ^ (index n + 1))
      ((ModuleCat.restrictScalars (a.ring n)).obj
        (ModuleCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))
          (O' ⧸ Ideal.span {mu} ^ (n + 1)))))
    (ιZ : StrictEtaleLevelScalarInclusions (TZ.level n) r)
    (ιY : StrictEtaleLevelScalarInclusions (TY.level n) r)
    (hZ : StrictEtaleLevelBasisCoordinates (TZ.level n) b ιZ)
    (hY : StrictEtaleLevelBasisCoordinates (TY.level n) b ιY) :
    ∃ d : (SB.properDerived.level n).direct ⋙ (TY.level n).restriction ≅
        (TZ.level n).restriction ⋙ (SA.properDerived.level (index n)).direct,
      ∀ K i,
        ιY ((SA.properDerived.level (index n)).direct.obj K) i ≫
            (TY.level n).restriction.map
              ((mateEquiv (SA.properDerived.level (index n)).adjunction
                (SB.properDerived.level n).adjunction (.mk _ _ _ _ e.hom)).natTrans.app K) ≫
            d.hom.app ((TZ.level n).derived.obj K) =
          (SA.properDerived.level (index n)).direct.map (ιZ K i) := by
  classical
  let : Algebra (O ⧸ Ideal.span {ell} ^ (index n + 1))
      (O' ⧸ Ideal.span {mu} ^ (n + 1)) := (a.ring n).toAlgebra
  change Module.Basis (Fin r) (O ⧸ Ideal.span {ell} ^ (index n + 1))
    (O' ⧸ Ideal.span {mu} ^ (n + 1)) at b
  refine ⟨strictEtaleProperRestrictionIso SA SB TZ TY n e, ?_⟩
  intro K i
  rw [normalizedInclusion_unit_action (TY.level n) b ιY hY _ i,
    normalizedInclusion_unit_action (TZ.level n) b ιZ hZ _ i]
  exact scalarMate_action_column
    (SA.properDerived.level (index n)).adjunction
    (SB.properDerived.level n).adjunction (TY.level n).derivedAdj (TZ.level n).derivedAdj e
    (levelDerivedAction Y O' mu (Quotient.out (b i)) n)
    (levelDerivedAction c.Z O' mu (Quotient.out (b i)) n)
    (directDerived_preserves_action SB.properImage (Quotient.out (b i)) n
      (SB.properDerived.level n)) K

end AlgebraicGeometry
