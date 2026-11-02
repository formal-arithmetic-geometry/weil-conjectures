/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # Generic transition calculus for tensor presentations of strict systems

Source: Stacks 03CZ, 03EK, 07A4 and 0941.

Given two levels of a strict coefficient system, presentations of two system complexes
by scalar extensions of completed-coefficient complexes, and the ordinary evaluation and
scalar tensor comparisons, the induced presentation of the system tensor product is again
compatible with the strict transition maps. Everything here is stated for arbitrary ring
sheaves, so that kernel checking never compares the concrete coefficient rings.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures
namespace OrdinaryReductionTensor

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}

/-- Forgetting a restriction of scalars on sections is injective.
Source: Stacks 03CZ. -/
theorem restrictionSection_injective {A B : Sheaf J RingCat.{r}} (φ : A ⟶ B)
    (N : SheafOfModules.{r} B) (U : Cᵒᵖ) :
    Function.Injective (coefficientRestrictionSection φ N U) := fun _ _ h ↦ h

/-- Sections of a map out of an adjunction unit.
Source: Stacks 03CZ. -/
theorem unit_comp_section {A B : Sheaf J RingCat.{r}} (p : A ⟶ B)
    {F : SheafOfModules.{r} A ⥤ SheafOfModules.{r} B}
    (a : F ⊣ SheafOfModules.restrictScalars p) {X : SheafOfModules.{r} A}
    {Y : SheafOfModules.{r} B} (φ : F.obj X ⟶ Y) (U : Cᵒᵖ) (x : X.val.obj U) :
    coefficientRestrictionSection p Y U
      ((a.unit.app X ≫ (SheafOfModules.restrictScalars p).map φ).val.app U x) =
      φ.val.app U (coefficientRestrictionSection p (F.obj X) U ((a.unit.app X).val.app U x)) :=
  rfl

/-- Restriction of scalars does not change the section map.
Source: Stacks 03CZ. -/
theorem restrict_map_section {A B : Sheaf J RingCat.{r}} (q : A ⟶ B)
    {M N : SheafOfModules.{r} B} (g : M ⟶ N) (U : Cᵒᵖ)
    (w : ((SheafOfModules.restrictScalars q).obj M).val.obj U) :
    coefficientRestrictionSection q N U (((SheafOfModules.restrictScalars q).map g).val.app U w) =
      g.val.app U (coefficientRestrictionSection q M U w) :=
  rfl

/-- Sections of a composite of module-sheaf maps.
Source: Stacks 03CZ. -/
theorem comp_section {R : Sheaf J RingCat.{r}} {M N P : SheafOfModules.{r} R}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) (x : M.val.obj U) :
    (f ≫ g).val.app U x = g.val.app U (f.val.app U x) := rfl

/-- The inverse of an isomorphism of complexes undoes it on sections.
Source: Stacks 03CZ. -/
theorem iso_inv_hom_section {R : Sheaf J RingCat.{r}}
    {P Q : CochainComplex (SheafOfModules.{r} R) ℤ} (e : P ≅ Q)
    (k : ℤ) (U : Cᵒᵖ) (x : (Q.X k).val.obj U) :
    (e.hom.f k).val.app U ((e.inv.f k).val.app U x) = x :=
  congrArg (fun (f : Q ⟶ Q) ↦ (f.f k).val.app U x) e.inv_hom_id

/-- The inverse of an isomorphism of complexes undoes it on sections.
Source: Stacks 03CZ. -/
theorem iso_hom_inv_section {R : Sheaf J RingCat.{r}}
    {P Q : CochainComplex (SheafOfModules.{r} R) ℤ} (e : P ≅ Q)
    (k : ℤ) (U : Cᵒᵖ) (x : (P.X k).val.obj U) :
    (e.inv.f k).val.app U ((e.hom.f k).val.app U x) = x :=
  congrArg (fun (f : P ⟶ P) ↦ (f.f k).val.app U x) e.hom_inv_id

/-- An eqToHom of module sheaves is the identity on sections.
Source: Stacks 03CZ. -/
theorem eqToHom_section_heq {R : Sheaf J RingCat.{r}}
    {M N : SheafOfModules.{r} R} (p : M = N) (U : Cᵒᵖ) (y : M.val.obj U) :
    HEq ((eqToHom p).val.app U y) y := by
  subst p
  rfl

/-- Maps out of a left adjoint are determined by their composites with the unit.
Source: Stacks 03CZ. -/
theorem hom_ext_of_unit {X' Y' : Type*} [Category X'] [Category Y'] {F : X' ⥤ Y'}
    {G : Y' ⥤ X'} (a : F ⊣ G) {X : X'} {Y : Y'} {f g : F.obj X ⟶ Y}
    (h : a.unit.app X ≫ G.map f = a.unit.app X ≫ G.map g) : f = g := by
  apply (a.homEquiv X Y).injective
  rw [a.homEquiv_unit, a.homEquiv_unit]
  exact h

/-- The mate of an equality of composite restrictions sends unit sections to unit sections.
Source: Stacks 03CZ, 03D7. -/
theorem quotientNatTrans_unitSection {A Bm Bn : Sheaf J RingCat.{r}}
    (pm : A ⟶ Bm) (pn : A ⟶ Bn) (q : Bm ⟶ Bn)
    (hres : SheafOfModules.restrictScalars.{r} q ⋙ SheafOfModules.restrictScalars.{r} pm =
      SheafOfModules.restrictScalars.{r} pn)
    {Fm : SheafOfModules.{r} A ⥤ SheafOfModules.{r} Bm}
    {Fn : SheafOfModules.{r} A ⥤ SheafOfModules.{r} Bn}
    (am : Fm ⊣ SheafOfModules.restrictScalars pm) (an : Fn ⊣ SheafOfModules.restrictScalars pn)
    (quot : Fm ⟶ Fn ⋙ SheafOfModules.restrictScalars q)
    (hquot : ∀ X, quot.app X = (coefficientQuotientNatTrans am an
      (SheafOfModules.restrictScalars q) (eqToIso hres)).app X)
    (X : SheafOfModules.{r} A) (U : Cᵒᵖ) (x : X.val.obj U) :
    coefficientRestrictionSection q (Fn.obj X) U
      ((quot.app X).val.app U
        (coefficientRestrictionSection pm (Fm.obj X) U ((am.unit.app X).val.app U x))) =
      coefficientRestrictionSection pn (Fn.obj X) U ((an.unit.app X).val.app U x) := by
  let t := an.unit.app X ≫ (eqToIso hres).inv.app (Fn.obj X)
  have ht : am.unit.app X ≫ (SheafOfModules.restrictScalars pm).map (quot.app X) = t := by
    rw [hquot]
    exact (am.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  refine (congrArg (fun k ↦ k.val.app U x) ht).trans ?_
  dsimp only [t]
  rw [comp_section, eqToIso.inv, eqToHom_app]
  exact eq_of_heq (eqToHom_section_heq (Functor.congr_obj hres.symm (Fn.obj X)) U _)
/-- Sections of the inverse of a threefold composite isomorphism ending in a symmetric one.
Source: Stacks 03CZ. -/
theorem trans_symm_inv_section {R : Sheaf J RingCat.{r}}
    {X Y Z W : CochainComplex (SheafOfModules.{r} R) ℤ} (e₁ : X ≅ Y) (e₂ : Y ≅ Z) (s : W ≅ Z)
    (k : ℤ) (U : Cᵒᵖ) (z : (W.X k).val.obj U) :
    ((e₁ ≪≫ e₂ ≪≫ s.symm).inv.f k).val.app U z =
      (e₁.inv.f k).val.app U ((e₂.inv.f k).val.app U ((s.hom.f k).val.app U z)) := rfl

/-- Sections of a threefold composite isomorphism ending in a symmetric one.
Source: Stacks 03CZ. -/
theorem trans_symm_hom_section {R : Sheaf J RingCat.{r}}
    {X Y Z W : CochainComplex (SheafOfModules.{r} R) ℤ} (e₁ : X ≅ Y) (e₂ : Y ≅ Z) (s : W ≅ Z)
    (k : ℤ) (U : Cᵒᵖ) (z : (X.X k).val.obj U) :
    ((e₁ ≪≫ e₂ ≪≫ s.symm).hom.f k).val.app U z =
      (s.inv.f k).val.app U ((e₂.hom.f k).val.app U ((e₁.hom.f k).val.app U z)) := rfl

/-- A composite through a restriction of scalars, computed one map at a time on sections.
Source: Stacks 03CZ. -/
theorem comp_restrict_section {Bm Bn : Sheaf J RingCat.{r}} (q : Bm ⟶ Bn)
    {X Y : SheafOfModules.{r} Bm} {Z W : SheafOfModules.{r} Bn}
    (a : X ⟶ Y) (b : Y ⟶ (SheafOfModules.restrictScalars q).obj Z) (g : Z ⟶ W) (U : Cᵒᵖ)
    (z : X.val.obj U) (z₁ : Y.val.obj U) (z₂ : Z.val.obj U) (z₃ : W.val.obj U)
    (h₁ : a.val.app U z = z₁) (h₂ : coefficientRestrictionSection q Z U (b.val.app U z₁) = z₂)
    (h₃ : g.val.app U z₂ = z₃) :
    coefficientRestrictionSection q W U
      ((a ≫ b ≫ (SheafOfModules.restrictScalars q).map g).val.app U z) = z₃ := by
  subst h₁ h₂ h₃
  rfl

section Generators

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The total tensor of a product isomorphism acts factorwise on pure generators.
Source: Stacks 03EK, 07A4. -/
theorem mapIso_prod_hom_generator {R : Sheaf J CommRingCat.{max c v r}}
    {P P' Q Q' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (a : P ≅ P') (b : Q ≅ Q') (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((coefficientTotalTensor.{r, c, v} J R).mapIso (a.prod b)).hom.f k).val.app U
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x y)) =
      coefficientTensorGenerator.{r, c, v} J R P' Q' p q k h U
        ((a.hom.f p).val.app U x) ((b.hom.f q).val.app U y) :=
  CategoryTheory.ScalarHomTensor.tensor_generator_map.{c, v, r} a.hom b.hom p q k h U x y

/-- The total tensor of a product isomorphism acts factorwise on pure generators.
Source: Stacks 03EK, 07A4. -/
theorem mapIso_prod_inv_generator {R : Sheaf J CommRingCat.{max c v r}}
    {P P' Q Q' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (a : P ≅ P') (b : Q ≅ Q') (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P'.X p).val.obj U) (y : (Q'.X q).val.obj U) :
    ((((coefficientTotalTensor.{r, c, v} J R).mapIso (a.prod b)).inv.f k).val.app U
        (coefficientTensorGenerator.{r, c, v} J R P' Q' p q k h U x y)) =
      coefficientTensorGenerator.{r, c, v} J R P Q p q k h U
        ((a.inv.f p).val.app U x) ((b.inv.f q).val.app U y) :=
  CategoryTheory.ScalarHomTensor.tensor_generator_map.{c, v, r} a.inv b.inv p q k h U x y

/-- Pure tensor generators are compatible with restriction along the site.
Source: Stacks 03EK. -/
theorem generator_presheaf_restrict (R : Sheaf J CommRingCat.{max c v r})
    (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (p q k : ℤ) (h : p + q = k) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X k).val.presheaf.map f
      (coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x y) =
    coefficientTensorGenerator.{r, c, v} J R P Q p q k h V
      ((P.X p).val.presheaf.map f x) ((Q.X q).val.presheaf.map f y) :=
  CategoryTheory.ringedSiteTensorGenerator_restrict.{c, v, r} J R P Q p q k h f x y

end Generators

section TensorTransition

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{max c v r}]
  [(coefficientSequenceTopology J).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

/-- The tensor product of two presentations of strict system complexes is again a
presentation: its finite comparison commutes with the strict transitions.
Source: Stacks 03EK, 07A4 and 0941. -/
theorem tensorPresentation_transition
    {A Bm Bn : Sheaf J CommRingCat.{max c v r}}
    {R : Sheaf (coefficientSequenceTopology J) CommRingCat.{max c v r}}
    (pm : (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A ⟶
      (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bm)
    (pn : (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A ⟶
      (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bn)
    (q : (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bm ⟶
      (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bn)
    (hres : SheafOfModules.restrictScalars.{max c v r} q ⋙
      SheafOfModules.restrictScalars.{max c v r} pm =
        SheafOfModules.restrictScalars.{max c v r} pn)
    {Em : SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⥤
      SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bm)}
    {En : SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A) ⥤
      SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bn)}
    [Em.Additive] [En.Additive]
    (am : Em ⊣ SheafOfModules.restrictScalars pm) (an : En ⊣ SheafOfModules.restrictScalars pn)
    (quot : Em ⟶ En ⋙ SheafOfModules.restrictScalars q)
    (hquot : ∀ X, quot.app X = (coefficientQuotientNatTrans am an
      (SheafOfModules.restrictScalars q) (eqToIso hres)).app X)
    {evm : SheafOfModules.{max c v r} ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⥤
      SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bm)}
    {evn : SheafOfModules.{max c v r} ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⥤
      SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj Bn)}
    [evm.Additive] [evn.Additive]
    (τ : evm ⟶ evn ⋙ SheafOfModules.restrictScalars q)
    {m n : ℕ} (hmn : n ≤ m)
    (σm : ∀ (M : SheafOfModules.{max c v r} ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) (U : Cᵒᵖ),
      M.val.obj (op (m, U.unop)) → (evm.obj M).val.obj U)
    (σn : ∀ (M : SheafOfModules.{max c v r} ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) (U : Cᵒᵖ),
      M.val.obj (op (n, U.unop)) → (evn.obj M).val.obj U)
    (hσm : ∀ M U, Function.Surjective (σm M U))
    (hτ : ∀ M U x, coefficientRestrictionSection q (evn.obj M) U
      ((τ.app M).val.app U (σm M U x)) =
        σn M U (M.val.presheaf.map (Prod.mkHom (homOfLE hmn) (𝟙 U.unop)).op x))
    (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ)
    (CP CQ : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose (coefficientSequenceTopology J)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (κPm : (evm.mapHomologicalComplex (.up ℤ)).obj CP ≅ (Em.mapHomologicalComplex (.up ℤ)).obj P)
    (κPn : (evn.mapHomologicalComplex (.up ℤ)).obj CP ≅ (En.mapHomologicalComplex (.up ℤ)).obj P)
    (κQm : (evm.mapHomologicalComplex (.up ℤ)).obj CQ ≅ (Em.mapHomologicalComplex (.up ℤ)).obj Q)
    (κQn : (evn.mapHomologicalComplex (.up ℤ)).obj CQ ≅ (En.mapHomologicalComplex (.up ℤ)).obj Q)
    (hP : ∀ p, τ.app (CP.X p) ≫ (SheafOfModules.restrictScalars q).map (κPn.hom.f p) =
      κPm.hom.f p ≫ quot.app (P.X p))
    (hQ : ∀ p, τ.app (CQ.X p) ≫ (SheafOfModules.restrictScalars q).map (κQn.hom.f p) =
      κQm.hom.f p ≫ quot.app (Q.X p))
    (evTm : (evm.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj (CP, CQ)) ≅
      (coefficientTotalTensor.{r, c, v} J Bm).obj
        ((evm.mapHomologicalComplex (.up ℤ)).obj CP, (evm.mapHomologicalComplex (.up ℤ)).obj CQ))
    (hevTm : ∀ (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
      (x : (CP.X p).val.obj (op (m, U.unop))) (y : (CQ.X q).val.obj (op (m, U.unop))),
      (evTm.hom.f k).val.app U (σm _ U
        (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J) R CP CQ p q k hpq
          (op (m, U.unop)) x y)) =
        coefficientTensorGenerator.{r, c, v} J Bm ((evm.mapHomologicalComplex (.up ℤ)).obj CP)
          ((evm.mapHomologicalComplex (.up ℤ)).obj CQ) p q k hpq U (σm _ U x) (σm _ U y))
    (evTn : (evn.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj (CP, CQ)) ≅
      (coefficientTotalTensor.{r, c, v} J Bn).obj
        ((evn.mapHomologicalComplex (.up ℤ)).obj CP, (evn.mapHomologicalComplex (.up ℤ)).obj CQ))
    (hevTn : ∀ (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
      (x : (CP.X p).val.obj (op (n, U.unop))) (y : (CQ.X q).val.obj (op (n, U.unop))),
      (evTn.hom.f k).val.app U (σn _ U
        (coefficientTensorGenerator.{r, c, v} (coefficientSequenceTopology J) R CP CQ p q k hpq
          (op (n, U.unop)) x y)) =
        coefficientTensorGenerator.{r, c, v} J Bn ((evn.mapHomologicalComplex (.up ℤ)).obj CP)
          ((evn.mapHomologicalComplex (.up ℤ)).obj CQ) p q k hpq U (σn _ U x) (σn _ U y))
    (sm : (Em.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J Bm).obj
        ((Em.mapHomologicalComplex (.up ℤ)).obj P, (Em.mapHomologicalComplex (.up ℤ)).obj Q))
    (hsm : CoefficientScalarTensorGenerators.{r, c, v} J A Bm Em
      (fun X U x ↦ coefficientRestrictionSection pm (Em.obj X) U ((am.unit.app X).val.app U x))
      P Q sm)
    (sn : (En.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J Bn).obj
        ((En.mapHomologicalComplex (.up ℤ)).obj P, (En.mapHomologicalComplex (.up ℤ)).obj Q))
    (hsn : CoefficientScalarTensorGenerators.{r, c, v} J A Bn En
      (fun X U x ↦ coefficientRestrictionSection pn (En.obj X) U ((an.unit.app X).val.app U x))
      P Q sn) :
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app
        ((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj (CP, CQ)) ≫
      ((SheafOfModules.restrictScalars q).mapHomologicalComplex (.up ℤ)).map
        (evTn ≪≫ (coefficientTotalTensor.{r, c, v} J Bn).mapIso (κPn.prod κQn) ≪≫ sn.symm).hom =
    (evTm ≪≫ (coefficientTotalTensor.{r, c, v} J Bm).mapIso (κPm.prod κQm) ≪≫ sm.symm).hom ≫
      (NatTrans.mapHomologicalComplex quot (.up ℤ)).app
        ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) := by
  have key (k : ℤ) :
      (evTm ≪≫ (coefficientTotalTensor.{r, c, v} J Bm).mapIso (κPm.prod κQm) ≪≫ sm.symm).inv.f k ≫
        τ.app (((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj
          (CP, CQ)).X k) ≫ (SheafOfModules.restrictScalars q).map
          ((evTn ≪≫ (coefficientTotalTensor.{r, c, v} J Bn).mapIso (κPn.prod κQn) ≪≫
            sn.symm).hom.f k) =
      quot.app (((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)).X k) := by
    apply hom_ext_of_unit am
    apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{c, v, r} P Q k
    intro p p' hpq V x y
    apply restrictionSection_injective pm _ V
    erw [unit_comp_section, unit_comp_section]
    apply restrictionSection_injective q _ V
    refine Eq.trans ?_ (quotientNatTrans_unitSection pm pn q hres am an quot hquot
      (((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)).X k) V
      (coefficientTensorGenerator.{r, c, v} J A P Q p p' k hpq V x y)).symm
    set_option trace.Meta.isDefEq true in
    obtain ⟨x0, hx0⟩ := hσm (CP.X p) V ((κPm.inv.f p).val.app V
      (coefficientRestrictionSection pm (Em.obj (P.X p)) V ((am.unit.app (P.X p)).val.app V x)))
    obtain ⟨y0, hy0⟩ := hσm (CQ.X p') V ((κQm.inv.f p').val.app V
      (coefficientRestrictionSection pm (Em.obj (Q.X p')) V ((am.unit.app (Q.X p')).val.app V y)))
    have hb := comp_restrict_section q
      ((evTm ≪≫ (coefficientTotalTensor.{r, c, v} J Bm).mapIso (κPm.prod κQm) ≪≫ sm.symm).inv.f k)
      (τ.app (((coefficientTotalTensor.{r, c, v} (coefficientSequenceTopology J) R).obj
          (CP, CQ)).X k))
      ((evTn ≪≫ (coefficientTotalTensor.{r, c, v} J Bn).mapIso (κPn.prod κQn) ≪≫
            sn.symm).hom.f k) V
    done
    done
  refine (Iso.inv_comp_eq _).1 ?_
  apply HomologicalComplex.Hom.ext
  funext k
  exact key k

end TensorTransition

end OrdinaryReductionTensor
end WeilConjectures
