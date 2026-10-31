/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

import all WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefFiniteDualizingMixedQuotient
import all WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefFiniteRealizationRestrictionSquare

/-! # Composition of the finite counit comparisons

Source: lem-coef-integral-finite-extension.proof.md, final paragraph, the u equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

private theorem compose_of_adjuncts
    {A B C : Type*} [Category A] [Category B] [Category C]
    {T₁ : A ⥤ B} {R₁ : B ⥤ A} {T₂ : B ⥤ C} {R₂ : C ⥤ B}
    {T₃ : A ⥤ C} {R₃ : C ⥤ A}
    (a₁ : T₁ ⊣ R₁) (a₂ : T₂ ⊣ R₂) (a₃ : T₃ ⊣ R₃)
    (c : R₂ ⋙ R₁ ≅ R₃) {K : A} {H : B} {N : C}
    (v : T₁.obj K ⟶ H) (w : T₂.obj H ⟶ N) (z : T₃.obj K ⟶ N)
    (h : a₃.homEquiv K N z ≫ c.inv.app N =
      a₁.homEquiv K H v ≫ R₁.map (a₂.homEquiv H N w)) :
    T₂.map v ≫ w = (a₁.leftAdjointCompIso a₂ a₃ c).hom.app K ≫ z := by
  apply ((a₁.comp a₂).homEquiv K N).injective
  rw [adjunct_conjugate a₃ (a₁.comp a₂)]
  simp only [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
    Equiv.apply_symm_apply]
  rw [Adjunction.comp_homEquiv]
  change (a₁.homEquiv K _) ((a₂.homEquiv _ _) (T₂.map v ≫ w)) = _
  rw [a₂.homEquiv_naturality_left, a₁.homEquiv_naturality_right]
  exact h.symm

private theorem realize_composition
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    (FA : A ⥤ A') (FB : B ⥤ B') (FC : C ⥤ C')
    (RAB : B ⥤ A) (RBC : C ⥤ B) (RAC : C ⥤ A)
    (RAB' : B' ⥤ A') (RBC' : C' ⥤ B') (RAC' : C' ⥤ A')
    (cAB : FB ⋙ RAB' ≅ RAB ⋙ FA) (cBC : FC ⋙ RBC' ≅ RBC ⋙ FB)
    (cAC : FC ⋙ RAC' ≅ RAC ⋙ FA)
    (η : RBC ⋙ RAB ≅ RAC) (θ : RBC' ⋙ RAB' ≅ RAC')
    {KA : A} {KB : B} {KC : C}
    (sAB : KA ⟶ RAB.obj KB) (sBC : KB ⟶ RBC.obj KC) (sAC : KA ⟶ RAC.obj KC)
    (hs : sAC ≫ η.inv.app KC = sAB ≫ RAB.map sBC)
    (hc : FA.map (η.inv.app KC) ≫ cAB.inv.app (RBC.obj KC) ≫
        RAB'.map (cBC.inv.app KC) =
      cAC.inv.app KC ≫ θ.inv.app (FC.obj KC)) :
    (FA.map sAC ≫ cAC.inv.app KC) ≫ θ.inv.app (FC.obj KC) =
      (FA.map sAB ≫ cAB.inv.app KB) ≫ RAB'.map (FB.map sBC ≫ cBC.inv.app KC) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← hc, ← FA.map_comp_assoc, hs, FA.map_comp]
  have hn := cAB.inv.naturality sBC
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, reassoc_of% hn]

private theorem conjugate_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    (RAB : B ⥤ A) (RBC : C ⥤ B) (RAC : C ⥤ A) (θ : RBC ⋙ RAB ≅ RAC)
    {KA LA : A} {KB LB : B} {KC LC : C}
    (eA : KA ≅ LA) (eB : KB ≅ LB) (eC : KC ≅ LC)
    (sAB : KA ⟶ RAB.obj KB) (sBC : KB ⟶ RBC.obj KC) (sAC : KA ⟶ RAC.obj KC)
    (hs : sAC ≫ θ.inv.app KC = sAB ≫ RAB.map sBC) :
    (eA.inv ≫ sAC ≫ RAC.map eC.hom) ≫ θ.inv.app LC =
      (eA.inv ≫ sAB ≫ RAB.map eB.hom) ≫
        RAB.map (eB.inv ≫ sBC ≫ RBC.map eC.hom) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← RAB.map_comp_assoc eB.hom eB.inv, Iso.hom_inv_id, RAB.map_id,
    Category.id_comp]
  have hn := θ.inv.naturality eC.hom
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ eA.inv ≫ f ≫ RAB.map (RBC.map eC.hom)) hs

/-- Finite dualizing coefficient counits compose through the scalar associator.
This is entirely a finite-level assertion, independent of integral dualizing data.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-integral-finite-extension.proof.md, second and final paragraphs.
(blueprint: lem-sf-finite-dualizing-scalar-composition)

Proof: on the etale site transpose both paths under the exceptional adjunction.
Expand finiteEtaleU: both transposes are the compact-support comparison inverse,
extension of the original exceptional counit, and the scalar unit at the regular
coefficient object. Mate pasting for the compact-support comparisons and their
scalar composition identity identify these paths. Counit naturality and the
triangle identities cancel the intermediate exceptional adjunction. Both scalar
unit maps send 1 to 1, so they agree through the same scalar associator. Transport
this etale equation through finiteDualizingOrigin and the scalar-normalized
realization restriction square defining finiteU. The intermediate realization
isomorphisms cancel, and pasting the restriction squares gives the inverse mate
of tensorComposition. This is the displayed equation. It includes level zero
(exponent one), identity field inclusions, ramified inclusions and empty X;
no invertibility of these finite maps is used. -/
theorem finiteU_scalar_composition
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u}) (D : FiniteFieldDatum.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (j : L →ₐ[Padic l] F) (n : ℕ)
    (h : integralScalarQuotientSheafMap l E L ι X n ≫
      integralScalarQuotientSheafMap l L F j X n =
        integralScalarQuotientSheafMap l E F (j.comp ι) X n) :
    (pbcDerivedExtend (integralScalarQuotientSheafMap l L F j X n)).map
        (finiteU l E L ι X D n) ≫ finiteU l L F j X D n =
      (PurCompactSupport.tensorComposition
        (integralScalarQuotientSheafMap l E L ι X n)
        (integralScalarQuotientSheafMap l L F j X n)
        (integralScalarQuotientSheafMap l E F (j.comp ι) X n) h).hom.app
          (integralDualizingFiniteTerm l E D X n) ≫
        finiteU l E F (j.comp ι) X D n := by
  let i := integralScalarQuotientMap l E L ι n
  let q := integralScalarQuotientMap l L F j n
  let k := integralScalarQuotientMap l E F (j.comp ι) n
  have hk : k = q.comp i := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  let i' := RingHom.ulift.{u + 1, u + 1} i
  let q' := RingHom.ulift.{u + 1, u + 1} q
  let k' := RingHom.ulift.{u + 1, u + 1} k
  let hk' : k' = q'.comp i' := ulift_comp i q k hk
  let a := integralScalarQuotientSheafMap l E L ι X n
  let b := integralScalarQuotientSheafMap l L F j X n
  let d := integralScalarQuotientSheafMap l E F (j.comp ι) X n
  let R (A B : Type (u + 1)) [CommRing A] [CommRing B] (φ : A →+* B) :=
    Sheaf.derivedRestrictScalars X.smallEtaleTopology φ
  let adj (A B : Type (u + 1)) [CommRing A] [CommRing B] (φ : A →+* B) :=
    Adjunction.ofIsRightAdjoint (R A B φ)
  let sAB := (adj _ _ i').homEquiv _ _ (finiteEtaleU l E L ι X D n)
  let sBC := (adj _ _ q').homEquiv _ _ (finiteEtaleU l L F j X D n)
  let sAC := (adj _ _ k').homEquiv _ _ (finiteEtaleU l E F (j.comp ι) X D n)
  let η := Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hk'
  let θ := pbcDerivedRestrictComp a b d h
  let := (finiteDualizingCompactification D X).hasCompactification
  have hs := coefficientU_restrict_comp i' q' k' hk' (X ↘ Spec (.of D.k))
  change sAC ≫ η.inv.app (finiteDualizingEtaleTerm l F D X n) =
    sAB ≫ (R _ _ i').map sBC at hs
  have hc := realizationRestriction_comp X i q k hk (finiteDualizingEtaleTerm l F D X n)
  have hc' :
      (finiteDualizingRealization l E X n).map
          (η.inv.app (finiteDualizingEtaleTerm l F D X n)) ≫
        (finiteRealizationRestriction l E L ι X n).inv.app
          ((R _ _ q').obj (finiteDualizingEtaleTerm l F D X n)) ≫
        (pbcDerivedRestrict a).map
          ((finiteRealizationRestriction l L F j X n).inv.app
            (finiteDualizingEtaleTerm l F D X n)) =
      (finiteRealizationRestriction l E F (j.comp ι) X n).inv.app
          (finiteDualizingEtaleTerm l F D X n) ≫
        θ.inv.app ((finiteDualizingRealization l F X n).obj
          (finiteDualizingEtaleTerm l F D X n)) := hc
  have hr := realize_composition
    (finiteDualizingRealization l E X n) (finiteDualizingRealization l L X n)
    (finiteDualizingRealization l F X n)
    (R _ _ i') (R _ _ q') (R _ _ k')
    (pbcDerivedRestrict a) (pbcDerivedRestrict b) (pbcDerivedRestrict d)
    (finiteRealizationRestriction l E L ι X n)
    (finiteRealizationRestriction l L F j X n)
    (finiteRealizationRestriction l E F (j.comp ι) X n)
    η θ sAB sBC sAC hs hc'
  have ht := conjugate_composition
    (pbcDerivedRestrict a) (pbcDerivedRestrict b) (pbcDerivedRestrict d) θ
    (finiteDualizingOrigin l E D X n) (finiteDualizingOrigin l L D X n)
    (finiteDualizingOrigin l F D X n) _ _ _ hr
  have he : PurCompactSupport.tensorComposition a b d h =
      (pbcDerivedScalarAdjunction a).leftAdjointCompIso
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction d) θ := by
    apply Iso.ext
    ext K
    simp [PurCompactSupport.tensorComposition, Adjunction.leftAdjointCompIso,
      Adjunction.leftAdjointUniq, θ]
  rw [he]
  apply compose_of_adjuncts (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction d) θ
  simpa only [finiteU, a, b, d, Equiv.apply_symm_apply, sAB, sBC, sAC, adj, R,
    Category.assoc] using ht

end WeilConjectures.IntegralFiniteExtension
