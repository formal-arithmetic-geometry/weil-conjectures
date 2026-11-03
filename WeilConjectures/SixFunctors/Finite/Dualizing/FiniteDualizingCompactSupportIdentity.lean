/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCompactQuotientCocycle
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison

/-! Compact-support normalization at an identity finite coefficient quotient. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
private theorem derived_comp_unit
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) (c : F ⋙ F ≅ F)
    (hc : c = Functor.isoWhiskerRight e F ≪≫ F.leftUnitor) :
    (Functor.mapDerivedCategoryCompIso F F).symm ≪≫
        Functor.mapDerivedCategoryNatIso c =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C)
        F.mapDerivedCategory ≪≫ F.mapDerivedCategory.leftUnitor := by
  subst c
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [Functor.mapDerivedCategoryNatIso_trans]
  have hu : (Functor.mapDerivedCategoryNatIso F.leftUnitor).hom = 𝟙 _ := by
    exact Functor.mapDerivedCategoryNatIso_refl
  rw [hu, Category.comp_id]
  apply (cancel_mono (Functor.mapDerivedCategoryCompIso (𝟭 C) F).hom).mp
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_comp, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_isoWhiskerRight,
    Iso.inv_hom_id_assoc]
  have h := Functor.mapDerivedCategoryCompIso_id_comp F
  have hh : (Functor.mapDerivedCategoryCompIso (𝟭 C) F).inv =
      Functor.whiskerRight (Functor.mapDerivedCategoryIdIso C).hom
        F.mapDerivedCategory := by
    apply (cancel_epi (Functor.mapDerivedCategoryCompIso (𝟭 C) F).hom).mp
    rw [Iso.hom_inv_id, h]
    rfl
  rw [← hh]
  have hu' : F.mapDerivedCategory.leftUnitor.hom = 𝟙 F.mapDerivedCategory := by rfl
  rw [hu']
  erw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem scalar_comp_unit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A] :
    ProEtale.pbcFixedScalarExtensionComp J (RingHom.id A) (RingHom.id A)
        (RingHom.id A) (by ext; rfl) =
      Functor.isoWhiskerLeft (ProEtale.pbcFixedScalarExtension J (RingHom.id A))
        (ProEtale.normalizedOriginScalarUnit J (RingHom.id A) rfl) ≪≫
      (ProEtale.pbcFixedScalarExtension J (RingHom.id A)).rightUnitor := by
  apply Adjunction.leftAdjointCompIso_comp_id
  exact derived_comp_unit _ _ _ (by
    apply Iso.ext
    ext M U x
    rfl)

private theorem cocycle_unit
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (S : C ⥤ C) (T : D ⥤ D)
    (uS : S ≅ 𝟭 C) (uT : T ≅ 𝟭 D)
    (b : F ⋙ T ⟶ S ⋙ F) (K : C) [IsIso (b.app K)]
    (hc : uT.hom.app (T.obj (F.obj K)) ≫ b.app K =
      T.map (b.app K) ≫ b.app (S.obj K) ≫ F.map (uS.hom.app (S.obj K))) :
    b.app K = uT.hom.app (F.obj K) ≫ F.map (uS.inv.app K) := by
  have hs : uS.hom.app (S.obj K) = S.map (uS.hom.app K) := by
    apply (cancel_mono (uS.hom.app K)).mp
    exact (uS.hom.naturality (uS.hom.app K)).symm
  rw [hs, ← Functor.comp_map, ← b.naturality] at hc
  simp only [Functor.comp_map, ← T.map_comp, ← Category.assoc] at hc
  have hh := (cancel_mono (b.app K)).mp hc
  have hn := uT.hom.naturality (b.app K ≫ F.map (uS.hom.app K))
  dsimp only [Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  have he : b.app K ≫ F.map (uS.hom.app K) = uT.hom.app (F.obj K) := by
    apply (cancel_epi (uT.hom.app (T.obj (F.obj K)))).mp
    simpa only [Category.assoc, hh] using hn.symm
  apply (cancel_mono (F.map (uS.hom.app K))).mp
  rw [Category.assoc, ← F.map_comp, Iso.inv_hom_id_app]
  erw [F.map_id, Category.comp_id]
  exact he

private theorem compact_identity
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y} (c : Compactification f)
    (φ : A →+* A) (hφ : φ = RingHom.id A) (K : Etale.DerivedCategoryModule A X) :
    Etale.ExceptionalCoefficients.compactSupportMap φ c K =
      (ProEtale.normalizedOriginScalarUnit Y.smallEtaleTopology φ hφ).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology φ hφ).inv.app K) := by
  subst φ
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let b := Etale.compactScalarMap (RingHom.id A) c
  have : IsIso (b.app K) :=
    Etale.ExceptionalCoefficients.compactSupport_isIso (RingHom.id A) c K
  have hc := Etale.FiniteSmoothPurity.compact_chain (RingHom.id A) (RingHom.id A)
    (RingHom.id A) (by ext; rfl) c K
  rw [scalar_comp_unit, scalar_comp_unit] at hc
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.id_obj] at hc
  exact cocycle_unit F (Etale.scalarExtension (RingHom.id A) X)
    (Etale.scalarExtension (RingHom.id A) Y)
    (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology (RingHom.id A) rfl)
    (ProEtale.normalizedOriginScalarUnit Y.smallEtaleTopology (RingHom.id A) rfl) b K (by
      simpa only [Etale.FiniteSmoothPurity.ordinaryScalar, F, b, Etale.compactScalarMap,
        Functor.comp_obj, Functor.id_obj, Category.comp_id] using hc)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/--
The compact-support coefficient comparison for an identity quotient is the
normalized scalar unit at the output followed by the image of the inverse unit.
This is the first mate-pasting step in the proof of
`finiteDualizing_compact_normalization`.  Expand the fixed compactification as
proper direct image after extension by zero, identify both factors with their
canonical scalar mates, and apply the identity triangle for the scalar
adjunction.  Naturality of the open balancing map and of the proper scalar mate
then gives the displayed equality for every derived etale object, including
zero objects and non-flat coefficient presentations.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md`, paragraphs 1--3.
(blueprint: lem-coef-dualizing-compact-normalization)
-/
theorem finiteDualizing_compact_support_identity :
    ∀ (n : ℕ) (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X),
      Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E
          (le_refl n)) (finiteDualizingCompactification D X) K =
        (ProEtale.normalizedOriginScalarUnit (Spec (.of D.k)).smallEtaleTopology _
          (finiteDualizingQuotient_id l E n)).hom.app
            ((finiteDualizingEtaleSupport l E D X n).obj K) ≫
        (finiteDualizingEtaleSupport l E D X n).map
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
            (finiteDualizingQuotient_id l E n)).inv.app K) := by
  intro n K
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  exact compact_identity (finiteDualizingCompactification D X)
    (finiteDualizingQuotient l E (le_refl n)) (finiteDualizingQuotient_id l E n) K

end WeilConjectures
