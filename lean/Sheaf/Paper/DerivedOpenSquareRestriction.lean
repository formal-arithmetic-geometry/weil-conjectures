/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import Mathlib.CategoryTheory.HomCongr
import Sheaf.Paper.CondensedOpenSquareScalarComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift

/-! # Unbounded open restriction of condensed-module direct image

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sf-comp-composition/det-sf-comp-composition-interchange.proof.md, Proof (2)
(blueprint: lem-sfb-derived-open-square-restriction).

The helpers spell out the canonical inverse-image comparison, its open mate, exact
termwise derivation, and the five Hom bijections. All categories are the ordinary
unbounded derived categories of internal modules over the pulled-back condensed ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {W Y Ybar : Scheme.{u}} (r : W ⟶ Ybar) (i : Y ⟶ Ybar) [IsOpenImmersion i]

/-- The pullback-square comparison on internal modules, using the recorded coefficient
composition comparisons; the square is the chosen scheme fibre product.
Source: det-sf-comp-composition-interchange, Proof (2), coefficient coherence in steps 3--4
of the expanded DAG proof (blueprint: lem-sfb-derived-open-square-restriction). -/
def moduleOpenSquarePullbackComparison :
    upperStar Λ i ⋙ upperStar Λ (pullback.snd r i) ≅
      upperStar Λ r ⋙ upperStar Λ (pullback.fst r i) :=
  (upperStarComp Λ (pullback.snd r i) i).symm ≪≫
    eqToIso (congrArg (upperStar Λ) (pullback.condition (f := r) (g := i)).symm) ≪≫
    upperStarComp Λ (pullback.fst r i) r

/-- Apply an underived open base-change isomorphism termwise and localize, with the
canonical exact-composition identifications on both sides.
Source: det-sf-comp-composition-interchange, Proof (2), step 4 of the expanded DAG proof
(blueprint: lem-sfb-derived-open-square-restriction). -/
def moduleOpenSquareDerivedExtensionIso
    (e : openImmersionLowerShriek Λ i ⋙ upperStar Λ r ≅
      upperStar Λ (pullback.snd r i) ⋙ openImmersionLowerShriek Λ (pullback.fst r i)) :
    (openImmersionLowerShriek Λ i).mapDerivedCategory ⋙ (upperStar Λ r).mapDerivedCategory ≅
      (upperStar Λ (pullback.snd r i)).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ (pullback.fst r i)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (openImmersionLowerShriek Λ i) (upperStar Λ r)).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryCompIso (upperStar Λ (pullback.snd r i))
      (openImmersionLowerShriek Λ (pullback.fst r i))

/-- The five natural Hom bijections defining open restriction of derived direct image.
The middle bijection precomposes with the inverse of the termwise open comparison.
Source: det-sf-comp-composition-interchange, Proof (2), steps 5--6 of the expanded DAG proof
(blueprint: lem-sfb-derived-open-square-restriction). -/
def moduleOpenSquareHomEquiv
    (e : openImmersionLowerShriek Λ i ⋙ upperStar Λ r ≅
      upperStar Λ (pullback.snd r i) ⋙ openImmersionLowerShriek Λ (pullback.fst r i))
    (T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W))) :
    (T ⟶ (upperStar Λ i).mapDerivedCategory.obj (((lowerStar Λ r).rightDerivedFunctor).obj B)) ≃
      (T ⟶ ((lowerStar Λ (pullback.snd r i)).rightDerivedFunctor).obj
        ((upperStar Λ (pullback.fst r i)).mapDerivedCategory.obj B)) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _).symm |>.trans
    (((upperStarLowerStarAdjunction Λ r).mapDerivedCategoryRightDerivedAdjunction.homEquiv
      _ _).symm) |>.trans
    (Iso.homCongr ((moduleOpenSquareDerivedExtensionIso Λ r i e).app T) (Iso.refl B)) |>.trans
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r i)).homEquiv
      _ _) |>.trans
    ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction Λ (pullback.snd r i))).homEquiv _ _)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The derived open unit is the localization of the termwise sheaf unit, using the
canonical exact-functor factorizations. The derived adjunction itself is the recorded one.
Source: det-sf-comp-composition-interchange, Proof (2), step 2 of the expanded DAG proof
(blueprint: lem-sfb-derived-open-square-restriction). -/
def moduleOpenUnitIsTermwise
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} (h : U ⟶ X) [IsOpenImmersion h] : Prop :=
  ∀ K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)) ℤ,
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ h).unit.app
        (DerivedCategory.Q.obj K) ≫
      (upperStar Λ h).mapDerivedCategory.map
        ((openImmersionLowerShriek Λ h).mapDerivedCategoryFactors.hom.app K) ≫
      (upperStar Λ h).mapDerivedCategoryFactors.hom.app
        (((openImmersionLowerShriek Λ h).mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map
        (((openImmersionLowerShriekUpperStarAdjunction Λ h).mapHomologicalComplex
          (.up ℤ)).unit.app K)

private theorem square_comparison_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {W Y X : Scheme.{u}} (r : W ⟶ X) (i : Y ⟶ X) [IsOpenImmersion i] :
    moduleOpenSquarePullbackComparison Λ r i = openSquareModulePullbackIso Λ r i := by
  unfold moduleOpenSquarePullbackComparison openSquareModulePullbackIso
  rfl

private theorem open_unit_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} (h : U ⟶ X) [IsOpenImmersion h] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ h).unit := by
  let ff := Adjunction.fullyFaithfulMapModLeft
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} h)
    (B := condensedRingObj Λ X)
  have : (linearOpenImmersionLowerShriek Λ h).Full := ff.full
  have : (linearOpenImmersionLowerShriek Λ h).Faithful := ff.faithful
  have : (Mod.comap (condensedPullbackHom Λ h)).Full :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ h)).fullyFaithfulFunctor.full
  have : (openImmersionLowerShriek Λ h).Full :=
    inferInstanceAs (Functor.Full (Mod.comap (condensedPullbackHom Λ h) ⋙
      linearOpenImmersionLowerShriek Λ h))
  have : (openImmersionLowerShriek Λ h).Faithful :=
    inferInstanceAs (Functor.Faithful (Mod.comap (condensedPullbackHom Λ h) ⋙
      linearOpenImmersionLowerShriek Λ h))
  infer_instance

private theorem factorsh_complex
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [F.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem open_unit_termwise
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} (h : U ⟶ X) [IsOpenImmersion h] :
    moduleOpenUnitIsTermwise Λ h := by
  intro K
  have hu := Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj
    (openImmersionLowerShriekUpperStarAdjunction Λ h)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hu
  erw [factorsh_complex, factorsh_complex] at hu
  exact hu

private theorem conjugate_hom
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁)
    (T : C) (B : D) (f : T ⟶ R₁.obj B) :
    f ≫ ((conjugateIsoEquiv a₁ a₂ e).hom.app B) =
      a₂.homEquiv T B (e.hom.app T ≫ (a₁.homEquiv T B).symm f) := by
  apply (a₂.homEquiv T B).symm.injective
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc]
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_counit]
  rw [← e.hom.naturality_assoc]

private theorem composite_conjugate_hom
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂}
    {L₃ : C₁ ⥤ C₄} {R₃ : C₄ ⥤ C₁} {L₄ : C₄ ⥤ C₃} {R₄ : C₃ ⥤ C₄}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (e : L₃ ⋙ L₄ ≅ L₁ ⋙ L₂) (T : C₁) (B : C₃)
    (f : T ⟶ (R₂ ⋙ R₁).obj B) :
    f ≫ ((conjugateIsoEquiv (a₁.comp a₂) (a₃.comp a₄) e).hom.app B) =
      (((((a₁.homEquiv _ _).symm.trans (a₂.homEquiv _ _).symm).trans
        (Iso.homCongr (e.symm.app T) (Iso.refl B))).trans
        (a₄.homEquiv _ _)).trans (a₃.homEquiv _ _)) f := by
  have hh := conjugate_hom (a₁.comp a₂) (a₃.comp a₄) e T B f
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv] at hh
  erw [Equiv.trans_apply, Equiv.symm_trans_apply] at hh
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  convert hh using 1
  congr 3

private theorem exchangeLeft_homEquiv
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    {H : A ⥤ A'} {H' : B ⥤ B'} (a : L ⊣ R) (b : L' ⊣ R')
    (e : R ⋙ H ≅ H' ⋙ R') (T : A) :
    b.homEquiv _ _ ((Adjunction.exchangeLeft a b e).app T) =
      H.map (a.unit.app T) ≫ e.hom.app (L.obj T) := by
  rw [Adjunction.exchangeLeft_app, ← L'.map_comp_assoc]
  exact (b.homEquiv _ _).apply_symm_apply _

private theorem exchangeLeft_eq_of_homEquiv
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    {H : A ⥤ A'} {H' : B ⥤ B'} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : R ⋙ H ≅ H' ⋙ R') (e : L ⋙ H' ≅ H ⋙ L')
    (he : ∀ T, b.homEquiv _ _ (e.inv.app T) =
      H.map (a.unit.app T) ≫ θ.hom.app (L.obj T)) :
    e.inv = Adjunction.exchangeLeft a b θ := by
  apply NatTrans.ext
  funext T
  apply (b.homEquiv _ _).injective
  rw [he, exchangeLeft_homEquiv]

private theorem derived_extension_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {W Y X : Scheme.{u}} (r : W ⟶ X) (i : Y ⟶ X) [IsOpenImmersion i]
    (e : openImmersionLowerShriek Λ i ⋙ upperStar Λ r ≅
      upperStar Λ (pullback.snd r i) ⋙ openImmersionLowerShriek Λ (pullback.fst r i)) :
    NatTrans.CommShift (moduleOpenSquareDerivedExtensionIso Λ r i e).hom ℤ := by
  unfold moduleOpenSquareDerivedExtensionIso
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- Open restriction commutes with total derived direct image on all unbounded
internal-module complexes, with the specified open units, Hom chain and canonical shifts.
Source: blueprint main-20261015, det-sf-comp-composition-interchange.proof.md, Proof (2)
(blueprint: lem-sfb-derived-open-square-restriction).

Proof:
1. Linearize the fully faithful abelian open extension by zero. Restriction of scalars
along the coefficient isomorphism is an equivalence, so the module open unit is invertible.
2. The existing exact-derived adjunction formulas give the actual derived open units,
their termwise normalization, and compatibility of these adjunctions with shifts.
3. Use the coefficient-compatible open-square comparison. Its adjunct characterization
identifies its inverse with the specified open exchange mate. Derive this comparison
termwise, using the canonical exact-composition identifications and their shift instances.
4. Compose the i and r adjunctions, and the p and j adjunctions. Conjugating the inverse
comparison of their left adjoints gives the required isomorphism of right adjoints.
5. The conjugate's counit formula identifies postcomposition with the five Hom bijections.
6. Canonical right-derived adjunctions and conjugation commute with shifts, giving the
specified shift square on arbitrary unbounded complexes. No properness is used. -/
theorem derived_open_square_restriction
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {W Y Ybar : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    (r : W ⟶ Ybar) (i : Y ⟶ Ybar) [IsOpenImmersion i.left] [QuasiCompact i.left] :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).unit ∧
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
      (pullback.fst r.left i.left)).unit ∧
    moduleOpenUnitIsTermwise Λ i.left ∧
    moduleOpenUnitIsTermwise Λ (pullback.fst r.left i.left) ∧
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).CommShift ℤ ∧
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
      (pullback.fst r.left i.left)).CommShift ℤ ∧
    (upperStarLowerStarAdjunction Λ r.left).mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ ∧
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction Λ (pullback.snd r.left i.left))).CommShift ℤ ∧
    ∃ e : openImmersionLowerShriek Λ i.left ⋙ upperStar Λ r.left ≅
        upperStar Λ (pullback.snd r.left i.left) ⋙
          openImmersionLowerShriek Λ (pullback.fst r.left i.left),
      e.inv = Adjunction.exchangeLeft
        (openImmersionLowerShriekUpperStarAdjunction Λ i.left)
        (openImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r.left i.left))
        (moduleOpenSquarePullbackComparison Λ r.left i.left) ∧
      NatTrans.CommShift (moduleOpenSquareDerivedExtensionIso Λ r.left i.left e).hom ℤ ∧
      ∃ ρ : (lowerStar Λ r.left).rightDerivedFunctor ⋙ (upperStar Λ i.left).mapDerivedCategory ≅
          (upperStar Λ (pullback.fst r.left i.left)).mapDerivedCategory ⋙
            (lowerStar Λ (pullback.snd r.left i.left)).rightDerivedFunctor,
        (∀ (T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
            (condensedRingObj Λ Y.left)))
          (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
            (condensedRingObj Λ W.left)))
          (a : T ⟶ (upperStar Λ i.left).mapDerivedCategory.obj
            (((lowerStar Λ r.left).rightDerivedFunctor).obj B)),
          a ≫ ρ.hom.app B = moduleOpenSquareHomEquiv Λ r.left i.left e T B a) ∧
        NatTrans.CommShift ρ.hom ℤ := by
  have := open_unit_iso Λ i.left
  have := open_unit_iso Λ (pullback.fst r.left i.left)
  have hi : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).unit := by
    exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have hj : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
      (pullback.fst r.left i.left)).unit := by
    exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have hsi : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).CommShift ℤ :=
    Adjunction.commShift_mapDerivedCategoryAdjunction _
  have hsj : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
      (pullback.fst r.left i.left)).CommShift ℤ :=
    Adjunction.commShift_mapDerivedCategoryAdjunction _
  have hsr := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ r.left)
  have hsp := canonicalRightDerivedAdjunctionShift
    (upperStarLowerStarAdjunction Λ (pullback.snd r.left i.left))
  refine ⟨hi, hj, open_unit_termwise Λ i.left,
    open_unit_termwise Λ (pullback.fst r.left i.left), hsi, hsj, hsr, hsp, ?_⟩
  obtain ⟨e, he, _⟩ :=
    (condensed_open_square_scalar_comparison ℓ Λ _hΛ r i).2.2.2.2.2.2.2.2.2
  have hse := derived_extension_commShift Λ r.left i.left e
  refine ⟨e, ?_, hse, ?_⟩
  · rw [square_comparison_eq]
    exact exchangeLeft_eq_of_homEquiv _ _ _ e he
  · let a₁ := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).comp
      (upperStarLowerStarAdjunction Λ r.left).mapDerivedCategoryRightDerivedAdjunction
    let a₂ := Adjunction.comp
      (upperStarLowerStarAdjunction Λ
        (pullback.snd r.left i.left)).mapDerivedCategoryRightDerivedAdjunction
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r.left i.left))
    let ρ := conjugateIsoEquiv a₁ a₂ (moduleOpenSquareDerivedExtensionIso Λ r.left i.left e).symm
    refine ⟨ρ, ?_, ?_⟩
    · intro T B f
      exact composite_conjugate_hom
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left)
        (upperStarLowerStarAdjunction Λ r.left).mapDerivedCategoryRightDerivedAdjunction
        (upperStarLowerStarAdjunction Λ
          (pullback.snd r.left i.left)).mapDerivedCategoryRightDerivedAdjunction
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r.left i.left))
        (moduleOpenSquareDerivedExtensionIso Λ r.left i.left e).symm T B f
    · change NatTrans.CommShift
        (conjugateEquiv a₁ a₂ (moduleOpenSquareDerivedExtensionIso Λ r.left i.left e).inv) ℤ
      have : a₁.CommShift ℤ := by dsimp [a₁]; infer_instance
      have : a₂.CommShift ℤ := by dsimp [a₂]; infer_instance
      infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
