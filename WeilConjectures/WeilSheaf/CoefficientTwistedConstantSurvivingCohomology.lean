/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.CanonicalCoefficientWeilCohomology
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import all WeilConjectures.AlgebraicGeometry.FieldWeilShriekShiftData
import all WeilConjectures.AlgebraicGeometry.CompletedUnitPullbackTower
import WeilConjectures.AlgebraicGeometry.CompletedUnitCanonicalWeil
import WeilConjectures.AlgebraicGeometry.CompletedUnitCommonTensorUnitor
import WeilConjectures.AlgebraicGeometry.CommonStagePullbackTensorNaturality
import WeilConjectures.AlgebraicGeometry.CompletedPullbackTensorNaturality
import WeilConjectures.AlgebraicGeometry.CommonStageTensorRightUnitorNaturality

/-! # Surviving cohomology of the coefficient shifted Tate constant -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius

attribute [local instance 1100] CategoryTheory.instOverClass

open CategoryTheory.Endofunctor CategoryTheory.Triangulated

private def pair_truncation_iso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) (F : C ⥤ C) [F.CommShift ℤ]
    (cLE : ∀ n : ℤ, t.truncLE n ⋙ F ≅ F ⋙ t.truncLE n)
    (cGE : ∀ n : ℤ, t.truncGE n ⋙ F ≅ F ⋙ t.truncGE n)
    (hLE : ∀ (n : ℤ) (K : IsoAlgebra F),
      ((IsoAlgebra.mapOfNatIso (cLE n)).obj K).str.hom ≫
        (t.truncLEι n).app K.carrier = F.map ((t.truncLEι n).app K.carrier) ≫ K.str.hom)
    (hGE : ∀ (n : ℤ) (K : IsoAlgebra F),
      K.str.hom ≫ (t.truncGEπ n).app K.carrier =
        F.map ((t.truncGEπ n).app K.carrier) ≫
          ((IsoAlgebra.mapOfNatIso (cGE n)).obj K).str.hom)
    (n : ℤ) (K : IsoAlgebra F) [t.IsLE K.carrier n] [t.IsGE K.carrier n] :
    ((IsoAlgebra.mapOfNatIso (cLE n) ⋙ IsoAlgebra.mapOfNatIso (cGE n)) ⋙
        IsoAlgebra.mapOfNatIso (F.commShiftIso n)).obj K ≅
      (IsoAlgebra.mapOfNatIso (F.commShiftIso n)).obj K := by
  let A := (IsoAlgebra.mapOfNatIso (cLE n)).obj K
  let a : A ≅ K := ObjectProperty.isoMk _
    (Algebra.isoMk (asIso ((t.truncLEι n).app K.carrier)) (hLE n K).symm)
  have ha : t.IsGE A.carrier n := by
    have hk : t.IsGE ((𝟭 C).obj K.carrier) n := ‹t.IsGE K.carrier n›
    exact t.isGE_of_iso (asIso ((t.truncLEι n).app K.carrier)).symm n
  let b : A ≅ (IsoAlgebra.mapOfNatIso (cGE n)).obj A := ObjectProperty.isoMk _
    (Algebra.isoMk (asIso ((t.truncGEπ n).app A.carrier)) (hGE n A).symm)
  exact (IsoAlgebra.mapOfNatIso (F.commShiftIso n)).mapIso (b.symm ≪≫ a)

private def pair_shift_cancel
    {C : Type*} [Category C] [HasShift C ℤ]
    (F : C ⥤ C) [F.CommShift ℤ] (K : IsoAlgebra F)
    (a b : ℤ) (hab : a + b = 0) :
    (IsoAlgebra.mapOfNatIso (F.commShiftIso b)).obj
      ((IsoAlgebra.mapOfNatIso (F.commShiftIso a)).obj K) ≅ K := by
  apply ObjectProperty.isoMk
  refine Algebra.isoMk ((shiftFunctorCompIsoId C a b hab).app K.carrier) ?_
  simp only [← IsoAlgebra.str_hom, IsoAlgebra.mapOfNatIso_obj_str,
    IsoAlgebra.mapOfNatIso_obj_carrier, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rw [F.map_shiftFunctorCompIsoId_hom_app]
  have hn := (shiftFunctorCompIsoId C a b hab).hom.naturality K.str.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]


private def conjugate_tensor_unit_pair
    {C : Type*} [Category C] (F : C ⥤ C) (T : C × C ⥤ C)
    (U : C) (θU : F.obj U ≅ U)
    (μ : ∀ A B, F.obj (T.obj (A, B)) ≅ T.obj (F.obj A, F.obj B))
    (r : ∀ A, T.obj (A, U) ≅ A)
    (hn : ∀ {A B} (f : A ⟶ B),
      T.map (Prod.mkHom f (𝟙 U)) ≫ (r B).hom = (r A).hom ≫ f)
    (hu : ∀ A, (μ A U).hom ≫ T.map (Prod.mkHom (𝟙 _) θU.hom) ≫
      (r (F.obj A)).hom = F.map (r A).hom)
    (M A : C) (a : M ≅ T.obj (A, U)) (θ : F.obj A ≅ A) :
    IsoAlgebra.mk M (F.mapIso a ≪≫ μ A U ≪≫
      T.mapIso (Iso.prod θ θU) ≪≫ a.symm) ≅ IsoAlgebra.mk A θ := by
  apply ObjectProperty.isoMk
  refine Algebra.isoMk (a ≪≫ r A) ?_
  change F.map (a.hom ≫ (r A).hom) ≫ θ.hom =
    (F.map a.hom ≫ (μ A U).hom ≫ T.map (Prod.mkHom θ.hom θU.hom) ≫ a.inv) ≫
      (a.hom ≫ (r A).hom)
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← hu A]
  simp only [Category.assoc]
  apply congrArg (fun z ↦ F.map a.hom ≫ (μ A U).hom ≫ z)
  have ht : Prod.mkHom θ.hom θU.hom =
      Prod.mkHom (𝟙 _) θU.hom ≫ Prod.mkHom θ.hom (𝟙 U) := by
    ext <;> simp
  rw [ht, T.map_comp, Category.assoc, hn θ.hom]

private theorem unit_right_transport
    {C : Type*} [Category C] (F : C ⥤ C) (T : C × C ⥤ C)
    (U V : C) (θ : F.obj U ≅ U) (ε : F.obj V ≅ V) (a : U ≅ V)
    (μ : ∀ A B, F.obj (T.obj (A, B)) ≅ T.obj (F.obj A, F.obj B))
    (hn : ∀ {A A' B B'} (f : A ⟶ A') (g : B ⟶ B'),
      F.map (T.map (Prod.mkHom f g)) ≫ (μ A' B').hom =
        (μ A B).hom ≫ T.map (Prod.mkHom (F.map f) (F.map g)))
    (ρ : (𝟭 C).prod' ((Functor.const C).obj V) ⋙ T ≅ 𝟭 C)
    (hε : ∀ A, (μ A V).hom ≫ T.map (Prod.mkHom (𝟙 _) ε.hom) ≫
      ρ.hom.app (F.obj A) = F.map (ρ.hom.app A))
    (ha : F.map a.hom ≫ ε.hom = θ.hom ≫ a.hom) :
    ∃ r : (𝟭 C).prod' ((Functor.const C).obj U) ⋙ T ≅ 𝟭 C,
      ∀ A, (μ A U).hom ≫ T.map (Prod.mkHom (𝟙 _) θ.hom) ≫
        r.hom.app (F.obj A) = F.map (r.hom.app A) := by
  let b : (𝟭 C).prod' ((Functor.const C).obj U) ⋙ T ≅
      (𝟭 C).prod' ((Functor.const C).obj V) ⋙ T :=
    NatIso.ofComponents (fun A ↦ T.mapIso (Iso.prod (Iso.refl A) a)) (by
      intro A B f
      change T.map (Prod.mkHom f (𝟙 U)) ≫ T.map (Prod.mkHom (𝟙 B) a.hom) =
        T.map (Prod.mkHom (𝟙 A) a.hom) ≫ T.map (Prod.mkHom f (𝟙 V))
      simp only [← T.map_comp]
      congr 1
      ext <;> simp)
  refine ⟨b ≪≫ ρ, fun A ↦ ?_⟩
  change (μ A U).hom ≫ T.map (Prod.mkHom (𝟙 _) θ.hom) ≫
    (T.map (Prod.mkHom (𝟙 _) a.hom) ≫ ρ.hom.app (F.obj A)) =
      F.map (T.map (Prod.mkHom (𝟙 _) a.hom) ≫ ρ.hom.app A)
  have h := hn (𝟙 A) a.hom
  simp only [F.map_id] at h
  have ht : T.map (Prod.mkHom (𝟙 (F.obj A)) θ.hom) ≫
      T.map (Prod.mkHom (𝟙 _) a.hom) =
    T.map (Prod.mkHom (𝟙 _) (F.map a.hom)) ≫ T.map (Prod.mkHom (𝟙 _) ε.hom) := by
    simp only [← T.map_comp, prod_comp, Category.id_comp, ha]
  rw [reassoc_of% ht]
  rw [← reassoc_of% h, hε A, F.map_comp]
  rfl

namespace WeilConjectures

private theorem cast_square_heq
    {C : Type*} [Category C] {A B A' B' X Y : C}
    (f : A ⟶ B) (g : A' ⟶ B') (p : X = A) (q : B = Y)
    (p' : X = A') (q' : B' = Y)
    (h : eqToHom p ≫ f ≫ eqToHom q = eqToHom p' ≫ g ≫ eqToHom q') : HEq f g := by
  have hf : HEq (eqToHom p ≫ f ≫ eqToHom q) f :=
    (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  have hg : HEq (eqToHom p' ≫ g ≫ eqToHom q') g :=
    (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  exact hf.symm.trans ((heq_of_eq h).trans hg)

private theorem localized_shift_heq
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (Q : C ⥤ D) (I : C ⥤ C) (F : D ⥤ D)
    [Q.CommShift ℤ] [I.CommShift ℤ] [F.CommShift ℤ]
    (β : Q ⋙ F ≅ I ⋙ Q) [NatTrans.CommShift β.hom ℤ]
    (hβ : ∀ K, ∃ e : F.obj (Q.obj K) = Q.obj (I.obj K), β.hom.app K = eqToHom e)
    (hQ : ∀ K, ∃ e : Q.obj (K⟦(1 : ℤ)⟧) = (Q.obj K)⟦(1 : ℤ)⟧,
      (Q.commShiftIso (1 : ℤ)).hom.app K = eqToHom e)
    (K : C) : HEq ((F.commShiftIso (1 : ℤ)).hom.app (Q.obj K))
      (Q.map ((I.commShiftIso (1 : ℤ)).hom.app K)) := by
  choose eβ heβ using hβ
  choose eQ heQ using hQ
  have h := NatTrans.shift_app_comm β.hom (1 : ℤ) K
  simp only [Functor.commShiftIso_comp_hom_app, heβ, heQ, eqToHom_map,
    Category.assoc] at h
  exact cast_square_heq _ _ _ _ _ _ h

private def included_shift_pair_iso
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (I : C ⥤ D) (F : C ⥤ C) (G : D ⥤ D)
    [I.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
    (β : F ⋙ I ≅ I ⋙ G) (r : ℤ)
    (hβ : ∀ A, I.map ((F.commShiftIso r).hom.app A) ≫
      (I.commShiftIso r).hom.app (F.obj A) ≫ (shiftFunctor D r).map (β.hom.app A) =
        β.hom.app (A⟦r⟧) ≫ G.map ((I.commShiftIso r).hom.app A) ≫
          (G.commShiftIso r).hom.app (I.obj A))
    (A : C) (θ : F.obj A ≅ A) :
    IsoAlgebra.mk (I.obj (A⟦r⟧))
      (β.symm.app (A⟦r⟧) ≪≫
        I.mapIso ((F.commShiftIso r).app A ≪≫ (shiftFunctor C r).mapIso θ)) ≅
      (IsoAlgebra.mapOfNatIso (G.commShiftIso r)).obj
        (IsoAlgebra.mk (I.obj A) (β.symm.app A ≪≫ I.mapIso θ)) := by
  apply ObjectProperty.isoMk
  refine Algebra.isoMk ((I.commShiftIso r).app A) ?_
  change G.map ((I.commShiftIso r).hom.app A) ≫
      ((G.commShiftIso r).hom.app (I.obj A) ≫
        (shiftFunctor D r).map ((β.inv.app A) ≫ I.map θ.hom)) =
    (β.inv.app (A⟦r⟧) ≫
      I.map (((F.commShiftIso r).hom.app A) ≫ (shiftFunctor C r).map θ.hom)) ≫
        (I.commShiftIso r).hom.app A
  apply (cancel_epi (β.hom.app (A⟦r⟧))).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% (hβ A)]
  have hn := (I.commShiftIso r).hom.naturality θ.hom
  dsimp only [Functor.comp_map] at hn
  simp only [← (shiftFunctor D r).map_comp_assoc, Iso.hom_inv_id_app,
    hn]
  erw [(shiftFunctor D r).map_id]
  simp only [Category.id_comp]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

private theorem rational_normalization
    (s : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ)
    (hs : FixedPairRationalShiftNormalization D l hl Y₀ E s) :
    let := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
    s = fieldRationalPullShift l E (D.geometricFrobenius Y₀).hom := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  obtain ⟨c, d, hd, β, hβ, hshift⟩ := hs
  have hd' : automorphismStageIntegralShiftNormalization l E
      (D.geometricFrobenius Y₀).hom d := by
    refine ⟨c.chainShift, c.derivedShift, c.chainShift_coordinates, c.derivedShift_descent, ?_⟩
    intro K r
    let := d
    let := c.derivedShift
    have h := hd K r
    let ι := (sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι
    have hι (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
        (ι.commShiftIso r).hom.app M = 𝟙 _ := rfl
    dsimp only [ι] at hι
    rw [hι, hι] at h
    change ((Functor.commShiftIso (constructibleIntegralPullback l E
      (D.geometricFrobenius Y₀).hom) r).hom.app K).hom ≫ 𝟙 _ =
      (integralDerivedPullback l E (D.geometricFrobenius Y₀).hom).map (𝟙 _) ≫
        (Functor.commShiftIso (integralDerivedPullback l E
          (D.geometricFrobenius Y₀).hom) r).hom.app K.obj at h
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
    exact heq_of_eq h
  have he := fieldConstructibleShift_normalization l E (D.geometricFrobenius Y₀).hom d hd'
  subst d
  let := s
  let := hshift
  apply (fieldRationalPullShift_existsUnique l E (D.geometricFrobenius Y₀).hom).unique
  · intro K
    apply localized_shift_heq (sfRationalConstructibleLocalization l E
      (D.geometricFiber Y₀).left)
      (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom)
      (sfWeilFrobeniusPullback D l hl Y₀ E) β
    · intro M
      exact ⟨_, hβ M⟩
    · intro M
      let Q := sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left
      have hshift := (sfRationalTriangulationDatum l E (D.geometricFiber Y₀).left)
        |>.choose_spec.choose_spec.1
      have hobj : (Q.obj M)⟦(1 : ℤ)⟧ = Q.obj (M⟦(1 : ℤ)⟧) :=
        congrArg (fun F ↦ F.obj (Q.obj M)) hshift
      refine ⟨hobj.symm, ?_⟩
      have hn : HEq ((Q.commShiftIso (1 : ℤ)).hom.app M)
          (𝟙 (Q.obj (M⟦(1 : ℤ)⟧))) :=
        (sfRationalTriangulationDatum l E (D.geometricFiber Y₀).left)
          |>.choose_spec.choose_spec.2.choose_spec.choose_spec.1 M
      exact eq_of_heq (hn.trans
        (eqToHom_heq_id_dom (Q.obj (M⟦(1 : ℤ)⟧)) ((Q.obj M)⟦(1 : ℤ)⟧)
          hobj.symm).symm)
  · exact (fieldRationalPullShift_existsUnique l E (D.geometricFrobenius Y₀).hom)
      |>.exists.choose_spec

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

omit E in
private theorem normalized_shifted_line (d : ℕ) :
    let h := fixedPairCommonTruncationCohomology D l hl Y₀ Ω
    let := h.choose_spec.choose
    Nonempty (IsoAlgebra.mk (ConstantPurityFrobenius.shiftedLine D l hl Ω Y₀ d)
      (ConstantPurityFrobenius.shiftedLineTheta D l hl Ω Y₀ d) ≅
        (IsoAlgebra.mapOfNatIso ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).commShiftIso
          (2 * (d : ℤ)))).obj
            (FrobeniusCoefficientTwists.commonWeilLine D l hl Y₀ Ω (d : ℤ))) := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  let h := fixedPairCommonTruncationCohomology D l hl Y₀ Ω
  let := h.choose_spec.choose
  let L := Padic.finiteCoefficientBase l Ω
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L
  let F := sfWeilFrobeniusPullback D l hl Y₀ E
  let G := sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω
  let : F.CommShift ℤ := fieldRationalPullShift l E (D.geometricFrobenius Y₀).hom
  let : G.CommShift ℤ := h.choose_spec.choose
  let A := FrobeniusCoefficientTwists.rationalLine l E (D.geometricFiber Y₀).left (d : ℤ)
  let θ := FrobeniusCoefficientTwists.rationalDerivedLineMap l E
    (D.geometricFrobenius Y₀).hom (d : ℤ)
  obtain ⟨β, hb, hβ⟩ := h.choose_spec.choose_spec.2.1 L
  have hs := rational_normalization D l hl Y₀ E (h.choose L)
    (h.choose_spec.choose_spec.1 L)
  rw [hs] at hβ
  have he := included_shift_pair_iso I F G β (2 * (d : ℤ))
    (hβ (2 * (d : ℤ))) A θ
  have hb' (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
      (D.geometricFiber Y₀).left L) : β.symm.app M =
        sfWeilStagePullbackIdentification D l hl Y₀ Ω L M := by
    simpa only [Iso.symm_hom] using Iso.ext (hb M)
  simp only [hb'] at he
  exact ⟨he⟩

end WeilConjectures


namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

local instance tateSurvivingStructureOver : X₀.hom.IsOver (Spec (.of P.field.k₀)) := by
  constructor
  dsimp only [autoParam]
  change X₀.hom ≫ 𝟙 _ = X₀.hom
  rw [Category.comp_id]

local instance survivingPointFiniteType : LocallyOfFiniteType (point P.field).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of P.field.k₀))))
local instance survivingPointQuasiCompact : QuasiCompact (point P.field).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of P.field.k₀))))

local instance survivingSourceUnits : ∀ x : (P.field.geometricFiber X₀).left,
    Invertible (P.coefficients.l : (P.field.geometricFiber X₀).left.residueField x) :=
  fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x

omit [IsSeparated X₀.hom] in
private def shifted_pair_of_unit
    (r : (𝟭 (generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
        P.coefficients.Qbar (P.field.geometricFiber X₀).left)).prod'
      ((Functor.const _).obj (unit P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar (P.field.geometricFiber X₀).left)) ⋙
      commonStageDerivedTensor P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFiber X₀).left ≅ 𝟭 _)
    (hr : ∀ K, (canonicalCommonStagePullbackTensor P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFrobenius X₀).hom K _).hom ≫
      (commonStageDerivedTensor P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFiber X₀).left).map
          (Prod.mkHom (𝟙 _) (constantWeilAlgebraicallyClosedComplex P.coefficients.l
            P.field P.coefficients.different X₀ P.coefficients.Qbar).str.hom) ≫
      r.hom.app ((sourceFrobenius P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀).obj K) =
      (sourceFrobenius P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀).map (r.hom.app K)) (d : ℕ) :
    twistedConstant P X₀ d ≅
      IsoAlgebra.mk (shiftedLine P.field P.coefficients.l P.coefficients.different
        P.coefficients.Qbar X₀ d)
        (shiftedLineTheta P.field P.coefficients.l P.coefficients.different
          P.coefficients.Qbar X₀ d) := by
  let := fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l
    P.coefficients.different X₀ x
  refine conjugate_tensor_unit_pair _ _ _ _ _ (fun A ↦ r.app A) ?_ hr _ _
    (sourceUnit P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar
      X₀ (point P.field) (pointMap P.field X₀) d) _
  intro A B f
  exact r.hom.naturality f

omit [IsSeparated X₀.hom] in
private theorem surviving_of_shifted_pair (d : ℕ)
    (e : let h := fixedPairCommonTruncationCohomology P.field P.coefficients.l
          P.coefficients.different X₀ P.coefficients.Qbar
        let := h.choose_spec.choose
        twistedConstant P X₀ d ≅
          (IsoAlgebra.mapOfNatIso ((sfCommonStageWeilFrobeniusPullback P.field
            P.coefficients.l P.coefficients.different X₀ P.coefficients.Qbar).commShiftIso
              (2 * (d : ℤ)))).obj
            (FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
              P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ))) :
    Nonempty ((canonicalCoefficientWeilCohomology P X₀ (-2 * (d : ℤ))).obj
        (twistedConstant P X₀ d) ≅
      FrobeniusCoefficientTwists.commonWeilSheaf P.field P.coefficients.l
        P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)) := by
  let h := fixedPairCommonTruncationCohomology P.field P.coefficients.l
    P.coefficients.different X₀ P.coefficients.Qbar
  let := h.choose_spec.choose
  let t := fixedPairCommonStageTStructure P.field P.coefficients.l
    P.coefficients.different X₀ P.coefficients.Qbar
  let F := sfCommonStageWeilFrobeniusPullback P.field P.coefficients.l
    P.coefficients.different X₀ P.coefficients.Qbar
  let K := FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
    P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)
  let M := twistedConstant P X₀ d
  have hK := FrobeniusCoefficientTwists.commonWeilLine_heart P.field P.coefficients.l
    P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)
  rw [← (sfCommonStageHeart_properties P.coefficients.l
    (P.field.geometricFiber X₀).left P.coefficients.Qbar P.field
      P.coefficients.different).1] at hK
  change t.heart K.carrier at hK
  rw [t.mem_heart_iff] at hK
  have : t.IsLE K.carrier 0 := hK.1
  have : t.IsGE K.carrier 0 := hK.2
  have : t.IsLE (K.carrier⟦2 * (d : ℤ)⟧) (-2 * (d : ℤ)) :=
    t.isLE_shift K.carrier 0 (2 * (d : ℤ)) (-2 * (d : ℤ)) (by omega)
  have : t.IsGE (K.carrier⟦2 * (d : ℤ)⟧) (-2 * (d : ℤ)) :=
    t.isGE_shift K.carrier 0 (2 * (d : ℤ)) (-2 * (d : ℤ)) (by omega)
  let ec : M.carrier ≅ K.carrier⟦2 * (d : ℤ)⟧ := (IsoAlgebra.forget F).mapIso e
  have : t.IsLE M.carrier (-2 * (d : ℤ)) := t.isLE_of_iso ec.symm _
  have : t.IsGE M.carrier (-2 * (d : ℤ)) := t.isGE_of_iso ec.symm _
  let hc := h.choose_spec.choose_spec.2.2
  let cLE := hc.choose
  let cGE := hc.choose_spec.choose
  let a := pair_truncation_iso t F cLE cGE
    (fun n A ↦ (hc.choose_spec.choose_spec.2.2.1 n A).1)
    (fun n A ↦ (hc.choose_spec.choose_spec.2.2.1 n A).2.1) (-2 * (d : ℤ)) M
  let b := (IsoAlgebra.mapOfNatIso (F.commShiftIso (-2 * (d : ℤ)))).mapIso e
  let c := pair_shift_cancel F K (2 * (d : ℤ)) (-2 * (d : ℤ)) (by omega)
  exact ⟨ObjectProperty.isoMk _ (a ≪≫ b ≪≫ c)⟩

set_option linter.unusedSectionVars false in
/-- The surviving cohomology of the canonical coefficient shifted Tate constant
is the unshifted coefficient root line, with its actual Weil structure.

Source: BBD 1.3, standard truncations; current blueprint,
lem-pur-constant-purity-frobenius-square, canonicalSourceTheta and its even shift.
(blueprint: lem-sf-coefficient-twisted-constant-surviving-cohomology)

Proof: sourceUnit replaces pullback of the point constant by the scalar unit at the
source. Identify the regular coefficient unit with the reconstructed tensor unit,
using the normalized completed unit map, and apply the tensor right unitor. The
finite-stage inclusion shift comparison identifies the carrier with the root line
shifted by 2d. The root line is in the standard heart by commonWeilLine_heart. Hence
truncation at -2d followed by the -2d shift recovers the unshifted root line.
To check the Weil structure, substitute the conjugation formula canonicalSourceTheta.
The completed unit's Frobenius compatibility and right-unitor naturality cancel its
unit factor. The finite-stage signed Roos normalization retained by
canonicalCoefficientWeilCohomology identifies the shift comparison on this root line
with the one in shiftedLineTheta. The normalized truncation-unit and counit equations
then leave precisely commonDerivedLineMap. Thus the carrier isomorphism intertwines
Frobenius and lifts to the full coefficient Weil heart. At d=0 the shift is zero
and the root line is the unit; empty schemes give the unique zero-object comparison. -/
theorem coefficient_twisted_constant_surviving_cohomology (d : ℕ) :
    Nonempty ((canonicalCoefficientWeilCohomology P X₀ (-2 * (d : ℤ))).obj
        (twistedConstant P X₀ d) ≅
      FrobeniusCoefficientTwists.commonWeilSheaf P.field P.coefficients.l
        P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)) := by
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
    (Padic.finiteCoefficientBase l Ω)
  have hU := (automorphismConstructibleStage_units D l hl (D.geometricFiber X₀)).1
  obtain ⟨c⟩ := CompletedUnitPullback.core_exists l E D hl
    (D.geometricFrobenius X₀).hom hU hU
  let X := (D.geometricFiber X₀).left
  let U := unit D l hl Ω X
  let V := pullbackTensorCommonUnit l Ω X
  let F := sourceFrobenius D l hl Ω X₀
  let T := commonStageDerivedTensor l Ω X
  let hunit := pullbackTensorCommonStageUnitCoherence l Ω (D.geometricFrobenius X₀).hom
  let ε := hunit.exists.choose
  obtain ⟨a, ha⟩ := CompletedUnitPullback.completedUnitCommonTensorComparison D l hl X₀ Ω c
  let ρ : (𝟭 _).prod' ((Functor.const _).obj V) ⋙ T ≅ 𝟭 _ :=
    NatIso.ofComponents (fun A ↦ pullbackTensorCommonRightUnitor l Ω X A)
      (fun f ↦ commonStageTensorRightUnitor_naturality l X Ω f)
  have hμ {A A' B B' : generalAlgebraicallyClosedConstructibleCategory l Ω X}
      (f : A ⟶ A') (g : B ⟶ B') :=
    commonStagePullbackTensor_naturality l Ω (D.geometricFrobenius X₀).hom
      (fun E _ _ _ ↦ canonicalRationalPullbackTensor_naturality l E
        (D.geometricFrobenius X₀).hom) f g
  obtain ⟨r, hr⟩ := unit_right_transport F T U V
    (CompletedUnitPullback.commonCoreTheta D l hl X₀ Ω c) ε a
    (canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius X₀).hom) hμ ρ
    (fun A ↦ (hunit.exists.choose_spec A).2) ha
  have hθ : CompletedUnitPullback.commonCoreTheta D l hl X₀ Ω c =
      (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).str := by
    dsimp only [CompletedUnitPullback.commonCoreTheta]
    rw [CompletedUnitPullback.completedUnitCanonicalWeil]
    apply Iso.ext
    rfl
  rw [hθ] at hr
  let pairIso := shifted_pair_of_unit P X₀ r hr d
  obtain ⟨b⟩ := normalized_shifted_line D l hl X₀ Ω d
  exact surviving_of_shifted_pair P X₀ d (pairIso ≪≫ b)

end WeilConjectures.NativeCoefficientCohomology
