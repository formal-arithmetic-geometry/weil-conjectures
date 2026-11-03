/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Universal scalar extension for arbitrary ring sheaves

Source: current blueprint, scalar extension clauses (1) and (4); Stacks 06YY.
The ordinary objects are sheafified sectionwise tensors. The universal left-derived
pair fixes the functor and all comparisons; there is no completed coefficient datum.
(blueprint: lem-sp-scalar-extension-site-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v w u' v' w' u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme

/-- A normalized tensor adjunction determines scalar multiplication on pure tensors.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem normalizedTensor_smul (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
    (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
    (h : N = SheafOfModules.changeOfRings φ M)
    (U : T.ProEtᵒᵖ) (s z : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom h.symm).val.app U
      ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
          ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      s • (eqToHom h.symm).val.app U
        ((toSheafify (ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := by
  let η := ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (R := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)
    (𝟙 _)).unit.app (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app U
  let e := eqToHom h.symm
  change e.val.app U (η ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    s • e.val.app U (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  clear_value e η
  have ht := ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom s z x
  have hη := η.hom.map_smul s (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  have he := (e.val.app U).hom.map_smul s
    (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  exact (congrArg (fun w ↦ e.val.app U (η w)) ht.symm).trans
    ((congrArg (fun w ↦ e.val.app U w) hη).trans he)

open scoped ChangeOfRings in
open CategoryTheory.Functor

/-- Compose the homotopy counit with complex localization to obtain its Kan property.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem kan_precomp_quotient
    {A B D H : Type*} [Category A] [Category B] [Category D] [Category H]
    (q : A ⥤ B) [((whiskeringLeft A B H).obj q).Full]
    [((whiskeringLeft A B H).obj q).Faithful]
    (L : B ⥤ D) (G : B ⥤ H) (F : D ⥤ H)
    (α : L ⋙ F ⟶ G) [F.IsRightKanExtension α] :
    F.IsRightKanExtension ((Functor.associator q L F).hom ≫ whiskerLeft q α) := by
  let P := RightExtension.precomp L G q
  have : P.IsEquivalence := by
    dsimp only [P, RightExtension.precomp]
    apply CostructuredArrow.isEquivalenceMap₂
  let β := (Functor.associator q L F).hom ≫ whiskerLeft q α
  let e : P.obj (RightExtension.mk F α) ≅ RightExtension.mk F β :=
    CostructuredArrow.isoMk (Iso.refl _)
  exact ⟨⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) e⟩⟩

/-- The natural counit on cochain representatives.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def complexCounitNat
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  let q := HomotopyCategory.quotient B (.up ℤ)
  let j : q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  whiskerRight (DerivedCategory.quotientCompQhIso B).inv L ≫
    (Functor.associator q DerivedCategory.Qh L).hom ≫ whiskerLeft q ε ≫ j.hom

/-- Derived natural transformations agree if they agree on K-flat counit representatives.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem derived_natTrans_ext
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type u'} [Category.{v'} D] (F G : DerivedCategory B ⥤ D)
    (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (p : P ⟶ X),
      S P ∧ QuasiIso p)
    (α β : F ⟶ G) (h : ∀ P, S P → α.app (DerivedCategory.Q.obj P) =
      β.app (DerivedCategory.Q.obj P)) : α = β := by
  apply NatTrans.ext
  funext X
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q X
  obtain ⟨P, p, hP, hp⟩ := hres K
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso B p).2 hp
  let i : DerivedCategory.Q.obj P ≅ X := asIso (DerivedCategory.Q.map p) ≪≫ e
  apply (cancel_epi (F.map i.hom)).1
  rw [α.naturality, β.naturality, h P hP]

/-- A derived transformation is invertible when its K-flat components are invertible.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem derived_natTrans_isIso
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type u'} [Category.{v'} D] (F G : DerivedCategory B ⥤ D)
    (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (p : P ⟶ X),
      S P ∧ QuasiIso p)
    (α : F ⟶ G) (h : ∀ P, S P → IsIso (α.app (DerivedCategory.Q.obj P))) :
    IsIso α := by
  have hi (X : DerivedCategory B) : IsIso (α.app X) := by
    obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q X
    obtain ⟨P, p, hP, hp⟩ := hres K
    have : IsIso (DerivedCategory.Q.map p) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso B p).2 hp
    have := h P hP
    let i : DerivedCategory.Q.obj P ≅ X := asIso (DerivedCategory.Q.map p) ≪≫ e
    have eq : α.app X = inv (F.map i.hom) ≫ α.app (DerivedCategory.Q.obj P) ≫
        G.map i.hom := by
      rw [← α.naturality, IsIso.inv_hom_id_assoc]
    rw [eq]
    infer_instance
  exact NatIso.isIso_of_isIso_app α

end AlgebraicGeometry.Scheme
