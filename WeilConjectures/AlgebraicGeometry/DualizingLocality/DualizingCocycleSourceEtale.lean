/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import all WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorCompositionEquation
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc

/-! # Dualizing tensor associativity and normalized etale source compatibility

Source: thm-pur-composition-coherence, proof Step 1, and the indicated steps
of lem-pur-dualizing-sigma-cocycle-locality. The statement expands the existing
locality predicates to keep this proof dependency independent of its consumer.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale.DualizingLocality
open FiniteEtaleNormalization
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  Etale.openImmersionLowerShriek Etale.upperStar Etale.lowerStar

-- The tensor equation uses the inverse of our specified support compositor.
private theorem support_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    [IsNoetherian Y] [IsNoetherian Z] [IsSeparated g] [LocallyOfFiniteType g] :
    smoothCompactSupportCompIso A f g =
      (Etale.unboundedEtaleLowerShriekCompIso A f g).symm := by
  simp [smoothCompactSupportCompIso, Etale.unboundedEtaleLowerShriekCompIso,
    Etale.rightDerivedLowerShriekIso, Functor.isoWhiskerRight_symm,
    (Etale.unboundedEtaleCompactSupport_comparison_coherence A g).1]
  rfl

-- Right-adjoint uniqueness agrees with adjunction conjugation of that compositor.
private theorem exceptional_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    [IsNoetherian Y] [IsNoetherian Z] [IsSeparated g] [LocallyOfFiniteType g] :
    smoothExceptionalCompIso A f g =
      conjugateIsoEquiv
        (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g))
        ((Etale.rightDerivedUpperShriekAdjunction A f).comp
          (Etale.rightDerivedUpperShriekAdjunction A g))
        (Etale.unboundedEtaleLowerShriekCompIso A f g) := by
  rw [smoothExceptionalCompIso, support_eq]
  apply Iso.ext
  ext K
  simp only [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.map_comp, Iso.refl_hom, NatTrans.id_app,
    Functor.whiskerLeft_app, Iso.symm_inv]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

-- Equality transport and its reverse use the same compactification comparison.
private theorem support_congr_symm
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    (Etale.unboundedEtaleLowerShriekCongr A w.symm).inv =
      (Etale.unboundedEtaleLowerShriekCongr A w).hom := by
  cases w
  rfl

-- Absorb the first tensor factor through its specified comparison with the unit.
private theorem tensor_unit_assoc
    {C : Type*} [Category C] [MonoidalCategory C]
    {W B C' D : C} (eta : W ≅ 𝟙_ C) (q : B ⊗ C' ⟶ D) :
    (α_ W B C').hom ≫ W ◁ q ≫ eta.hom ▷ D ≫ (λ_ D).hom =
      (eta.hom ▷ B ≫ (λ_ B).hom) ▷ C' ≫ q := by
  rw [whisker_exchange_assoc, leftUnitor_naturality,
    ← associator_naturality_left_assoc, leftUnitor_tensor_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]

-- Naturality of the counit/projection tensor mate in its coefficient object.
private theorem theta_nat
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {K K' : Etale.DerivedCategoryModule A Y} (q : K ⟶ K') :
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      (Etale.dualizingComplex A f)).map
        ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map q) ≫
      Etale.dualizingComplexTensorMap A f K' =
      Etale.dualizingComplexTensorMap A f K ≫
        (Etale.rightDerivedUpperShriek A f).map q := by
  exact unitTensorNaturality (hπiso := fun M N ↦ by infer_instance)
    (Etale.rightDerivedUpperShriekAdjunction A f) _
    (Etale.projectionMap_app_app_naturality_right f) q

section Geometric
variable (P : WeilConjectures.PurityFiniteSetting.{u})
  {S X Y Z : Scheme.{u}}
  [S.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
  [QuasiCompact (S ↘ Spec (.of P.field.k))]
  [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  (f : S ⟶ X) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
  [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]

-- Conjugate the specified support associativity equation and evaluate it at K.
private theorem comp_assoc (K : Etale.DerivedCategoryModule P.Coefficient Z) :
    (comp P (f ≫ g) h).hom.app K ≫
        (comp P f g).hom.app ((exceptional P h).obj K) =
      (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
        (Category.assoc f g h)).hom.app K ≫
        (comp P f (g ≫ h)).hom.app K ≫
        (exceptional P f).map ((comp P g h).hom.app K) := by
  let := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of P.field.k))
  let : IsNoetherian S := {}
  let := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  let : IsNoetherian X := {}
  let := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  let : IsNoetherian Y := {}
  let := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of P.field.k))
  let : IsNoetherian Z := {}
  let := compactification P f
  let := compactification P g
  let := compactification P h
  let := compactification P (f ≫ g)
  let := compactification P (g ≫ h)
  let := compactification P ((f ≫ g) ≫ h)
  let := compactification P (f ≫ g ≫ h)
  let af := Etale.rightDerivedUpperShriekAdjunction P.Coefficient f
  let ag := Etale.rightDerivedUpperShriekAdjunction P.Coefficient g
  let ah := Etale.rightDerivedUpperShriekAdjunction P.Coefficient h
  let afg := Etale.rightDerivedUpperShriekAdjunction P.Coefficient (f ≫ g)
  let agh := Etale.rightDerivedUpperShriekAdjunction P.Coefficient (g ≫ h)
  let al := Etale.rightDerivedUpperShriekAdjunction P.Coefficient ((f ≫ g) ≫ h)
  let ar := Etale.rightDerivedUpperShriekAdjunction P.Coefficient (f ≫ g ≫ h)
  have hs := Etale.unboundedEtaleLowerShriekCompIso_assoc P.Coefficient f g h
  have hc := congrArg (conjugateEquiv ar ((af.comp ag).comp ah)) hs
  rw [← conjugateEquiv_comp ar (afg.comp ah),
    ← conjugateEquiv_comp ar al,
    ← conjugateEquiv_comp ar (af.comp (ag.comp ah)),
    ← conjugateEquiv_comp ar (af.comp agh),
    conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    conjugateEquiv_associator_hom] at hc
  have hk := NatTrans.congr_app hc K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at hk
  have hj :
      (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
        (Category.assoc f g h)).inv =
      conjugateEquiv ar al
        (Etale.unboundedEtaleLowerShriekCongr P.Coefficient
          (Category.assoc f g h)).hom := by
    change conjugateEquiv ar al _ = _
    rw [support_congr_symm]
  apply (cancel_epi
    ((FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
      (Category.assoc f g h)).inv.app K)).1
  simp only [Iso.inv_hom_id_app_assoc]
  rw [NatTrans.congr_app hj K]
  simpa only [comp, conjugateIsoEquiv_apply_hom,
    exceptional, af, ag, ah, afg, agh, al, ar, Category.assoc] using hk

end Geometric

-- The cocycle follows from the existing etale tensor composition equation.
private theorem dualizing_cocycle_source_etale_core
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    (∀
    {S X Y Z : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : S ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h],
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) (𝟙 ((pull P (f ≫ g)).obj (omega P h))) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      (f ≫ g) h (cf := compactification P (f ≫ g))
      (cg := compactification P h)
      (cfg := compactification P ((f ≫ g) ≫ h))
      (comp P (f ≫ g) h)) ≫
        (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
          (Category.assoc f g h)).hom.app
            (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) =
    (Etale.derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) S
      (omega P f) ((pull P f).obj (omega P g))
        ((pull P (f ≫ g)).obj (omega P h))).hom ≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) S).obj (omega P f)).map
      (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) (𝟙 _)
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
            (omega P h)) ≫
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f
          (omega P g) ((pull P g).obj (omega P h))).inv ≫
        (pull P f).map ((FiniteEtaleNormalization.sigma P.Coefficient
      g h (cf := compactification P g)
      (cg := compactification P h)
      (cfg := compactification P (g ≫ h))
      (comp P g h)))) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      f (g ≫ h) (cf := compactification P f)
      (cg := compactification P (g ≫ h))
      (cfg := compactification P (f ≫ (g ≫ h)))
      (comp P f (g ≫ h)))) := by
  intro S X Y Z iS lS qS iX lX qX iY lY qY iZ lZ qZ
    f iof sf lf qf df sdf g iog sg lg qg dg sdg h ioh sh lh qh dh sdh
  let := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of P.field.k))
  let : IsNoetherian S := {}
  let := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  let : IsNoetherian X := {}
  let := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  let : IsNoetherian Y := {}
  let := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of P.field.k))
  let := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of P.field.k))
  let : IsNoetherian Z := {}
  let := compactification P f
  let := compactification P g
  let := compactification P h
  let := compactification P (f ≫ g)
  let := compactification P (g ≫ h)
  let := compactification P ((f ≫ g) ≫ h)
  let := compactification P (f ≫ g ≫ h)
  have hc := comp_assoc P f g h (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z)
  have ht := smoothTensorCompositionEquation P.Coefficient f g (omega P h)
  have hn := theta_nat P.Coefficient f
    ((comp P g h).hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z))
  simp only [smoothDualizingCompMap, exceptional_eq] at ht
  apply (cancel_mono
    ((comp P f (g ≫ h)).hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) ≫
      (exceptional P f).map
        ((comp P g h).hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z)))).1
  simp only [Etale.derivedTensorHom_eq_tensorHom, tensorHom_id,
    id_tensorHom, Etale.derivedTensorAssociator_eq, Etale.derivedTensor_obj_map,
    Category.assoc]
  rw [← hc]
  simp only [sigma, Category.assoc, Iso.inv_hom_id_app_assoc]
  dsimp only [omega, pull, exceptional, coefficientUnit, Etale.dualizingComplex,
    Functor.comp_obj] at hn ⊢
  rw [← hn]
  simpa only [sigma, comp, omega, pull, exceptional,
    Etale.dualizingComplex, coefficientUnit, Functor.comp_obj,
    Etale.derivedTensor_obj_map, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using ht

/-- For a smooth triple the canonical sigma maps satisfy the cocycle, and for
an etale first arrow the cocycle induces the normalized source-etale identity.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Steps 1--2;
lem-pur-dualizing-sigma-cocycle-locality, proof Steps 1--3.

Proof: Identify the comparisons in the proved etale tensor composition equation
with the specified finite-normalization compositors. Conjugate compact-support
associativity to obtain exceptional compositor associativity. Postcompose both
cocycle routes with the common exceptional compositor, expand sigma, and use
naturality of the tensor mate at the compositor for g and h. Cancelling the
inverse compositors reduces the result to the tensor composition equation at
omega_h. Cancel the common isomorphism to obtain the cocycle.

If f is etale, normalization says sigma_f,b followed by E_f,b is the unit map
U_f(omega_b). In particular sigma_f,g is invertible. Precompose the desired
source-etale equation with sigma_f,g tensored with an identity. Substitute the
cocycle and both normalization equations; tensor interchange, unitor naturality
and the left-unitor tensor identity identify the two sides. Cancel that
precomposition. The argument uses the same identities for identity maps,
relative dimension zero and empty schemes, with no nonemptiness assumption.
(blueprint: lem-route-dualizing-cocycle-source-etale). -/
theorem dualizing_cocycle_source_etale
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    (∀
    {S X Y Z : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : S ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h],
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) (𝟙 ((pull P (f ≫ g)).obj (omega P h))) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      (f ≫ g) h (cf := compactification P (f ≫ g))
      (cg := compactification P h)
      (cfg := compactification P ((f ≫ g) ≫ h))
      (comp P (f ≫ g) h)) ≫
        (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
          (Category.assoc f g h)).hom.app
            (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) =
    (Etale.derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) S
      (omega P f) ((pull P f).obj (omega P g))
        ((pull P (f ≫ g)).obj (omega P h))).hom ≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) S).obj (omega P f)).map
      (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) (𝟙 _)
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
            (omega P h)) ≫
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f
          (omega P g) ((pull P g).obj (omega P h))).inv ≫
        (pull P f).map ((FiniteEtaleNormalization.sigma P.Coefficient
      g h (cf := compactification P g)
      (cg := compactification P h)
      (cfg := compactification P (g ≫ h))
      (comp P g h)))) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      f (g ≫ h) (cf := compactification P f)
      (cg := compactification P (g ≫ h))
      (cfg := compactification P (f ≫ (g ≫ h)))
      (comp P f (g ≫ h)))) ∧
    (∀
    {S X Y Z : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : S ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    [Etale f],
    (FiniteEtaleNormalization.sigma P.Coefficient
      (f ≫ g) h (cf := compactification P (f ≫ g))
      (cg := compactification P h)
      (cfg := compactification P ((f ≫ g) ≫ h))
      (comp P (f ≫ g) h)) ≫
      (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
        (Category.assoc f g h)).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) ≫
      (sourceEtale P f (g ≫ h)).hom =
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        (sourceEtale P f g).hom
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
          (omega P h)) ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f
        (omega P g) ((pull P g).obj (omega P h))).inv ≫
      (pull P f).map ((FiniteEtaleNormalization.sigma P.Coefficient
      g h (cf := compactification P g)
      (cg := compactification P h)
      (cfg := compactification P (g ≫ h))
      (comp P g h)))) := by
  constructor
  · exact dualizing_cocycle_source_etale_core P
  · intros S X Y Z iS lS qS iX lX qX iY lY qY iZ lZ qZ
      f iof sf lf qf df sdf g iog sg lg qg dg sdg h ioh sh lh qh dh sdh etf
    let : Smooth g := SmoothOfRelativeDimension.smooth dg g
    let : Smooth h := SmoothOfRelativeDimension.smooth dh h
    let : SmoothOfRelativeDimension (dg + dh) (g ≫ h) := inferInstance
    let : Smooth (g ≫ h) := SmoothOfRelativeDimension.smooth (dg + dh) (g ≫ h)
    let := compactification P f
    let := compactification P g
    let := compactification P h
    let := compactification P (f ≫ g)
    let := compactification P (g ≫ h)
    let := compactification P ((f ≫ g) ≫ h)
    let := compactification P (f ≫ g ≫ h)
    have hfg := (finite_etale_dualizing_normalization P f).source_etale g
    have hfgh := (finite_etale_dualizing_normalization P f).source_etale (g ≫ h)
    change sigma P.Coefficient f g (comp P f g) ≫ (sourceEtale P f g).hom =
      tensorUnitMap (ModuleCat.{u + 1} P.Coefficient) S (omega P f)
        ((pull P f).obj (omega P g)) (eta P f) at hfg
    change sigma P.Coefficient f (g ≫ h) (comp P f (g ≫ h)) ≫
        (sourceEtale P f (g ≫ h)).hom =
      tensorUnitMap (ModuleCat.{u + 1} P.Coefficient) S (omega P f)
        ((pull P f).obj (omega P (g ≫ h))) (eta P f) at hfgh
    have hσ : IsIso (sigma P.Coefficient f g (comp P f g)) := by
      have hi : IsIso (sigma P.Coefficient f g (comp P f g) ≫
          (sourceEtale P f g).hom) := by
        rw [hfg]
        dsimp [tensorUnitMap]
        infer_instance
      exact (isIso_comp_right_iff _ _).1 hi
    have he : IsIso (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        (sigma P.Coefficient f g (comp P f g))
        (𝟙 ((pull P (f ≫ g)).obj (omega P h)))) := by
      rw [Etale.derivedTensorHom_eq_tensorHom]
      infer_instance
    have hc := dualizing_cocycle_source_etale_core P (f := f) (g := g) (h := h) df dg dh
    apply (cancel_epi (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      (sigma P.Coefficient f g (comp P f g))
      (𝟙 ((pull P (f ≫ g)).obj (omega P h))))).1
    rw [reassoc_of% hc, hfgh]
    simp only [Etale.derivedTensorHom_eq_tensorHom, tensorHom_id,
      id_tensorHom, Etale.derivedTensorAssociator_eq, Etale.derivedTensor_obj_map]
    rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp, hfg]
    simp only [tensorUnitMap, Etale.derivedTensor_map_app, Etale.derivedTensorLeftUnitor]
    rw [tensor_unit_assoc]
    simp only [MonoidalCategory.tensorHom_def, Category.assoc]

end AlgebraicGeometry.ProEtale.DualizingLocality
