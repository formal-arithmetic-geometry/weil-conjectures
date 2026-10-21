/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Data.ZMod.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.Sites.TorsionSheafConstantModule
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.DerivedCategory.CokernelAdjointExchange
import Sheaf.CategoryTheory.DerivedCategory.NormalizedScalarBoundaryNaturality

/-!
# Derived reduction of an extension by a divisible sheaf

Source: the Cartier unit proof, paragraphs 4 and 5, in blueprint main-20261015;
Stacks Tags 06YU, 06YV, 06YY, 0152, 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Kernel and quotient objects are specified by their short exact sequences, including
existence of their residue-coefficient structures. The normalized identifications are
unique, so the definition of the reduced boundary makes no arbitrary choice of map.
The normalized sheaf scalar adjunction is an item helper; the general internal-module
derived extension of scalars remains the recorded dependency interface.
-/

@[expose] public section
set_option autoImplicit false
universe u v r wZ wR u' v' wZ' wR'
open CategoryTheory CategoryTheory.Limits

/-- An extension together with its residue kernel and quotient presentations.
Source: Cartier proof, paragraph 4
(blueprint: def-sfb-scalar-reduction-presentation).
The three short exact sequences specify the extension, the kernel of multiplication
by n on its first term, and the cokernel of multiplication by n on its last term. -/
structure CategoryTheory.ScalarReductionPresentation
    {A B : Type*} [Category* A] [Category* B] [Preadditive A]
    (R : B ⥤ A) (n : ℕ) where
  S : ShortComplex A
  exact : S.ShortExact
  H : B
  Q : B
  i : R.obj H ⟶ S.X₁
  p : S.X₃ ⟶ R.obj Q
  wi : i ≫ (n • 𝟙 S.X₁) = 0
  wp : (n • 𝟙 S.X₃) ≫ p = 0
  kummer : (ShortComplex.mk i (n • 𝟙 S.X₁) wi).ShortExact
  quotient : (ShortComplex.mk (n • 𝟙 S.X₃) p wp).ShortExact

/-- Two scalar-reduction identifications characterized by their adjunction units.
Source: Cartier proof, paragraph 4
(blueprint: def-sfb-normalized-reduction-identifications).
The quotient unit and Kummer unit equations record the complete normalization,
including the degree-one target and its sign. -/
structure CategoryTheory.NormalizedReductionIdentifications
    {A B : Type*} [Category* A] [Category* B] [HasShift B ℤ]
    (L : A ⥤ B) (R : B ⥤ A) (X₁ X₃ : A) (H Q : B) (Z : A)
    (c : R.obj Q ⟶ Z) (eta₁ : X₁ ⟶ R.obj (L.obj X₁))
    (eta₃ : X₃ ⟶ R.obj (L.obj X₃)) (p : X₃ ⟶ Z)
    (k : X₁ ⟶ R.obj (H⟦(1 : ℤ)⟧)) where
  alphaF : L.obj X₃ ≅ Q
  alphaB : L.obj X₁ ≅ H⟦(1 : ℤ)⟧
  quotient_unit : eta₃ ≫ R.map alphaF.hom ≫ c = p
  kummer_unit : eta₁ ≫ R.map alphaB.hom = k

section GeneralBoundaryNaturality
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (res : B ⥤ A) [res.Additive]
  [PreservesFiniteLimits res] [PreservesFiniteColimits res]
  (L : DerivedCategory A ⥤ DerivedCategory B) [L.CommShift ℤ]
  (ad : L ⊣ res.mapDerivedCategory) (n : ℕ)

private noncomputable def generic_kappa (P : ScalarReductionPresentation res n) :=
  P.kummer.singleδ ≫
    ((res.mapDerivedCategorySingleFunctor 0).inv.app P.H)⟦(1 : ℤ)⟧' ≫
    (res.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.singleFunctor B 0).obj P.H)

private noncomputable abbrev generic_identifications (P : ScalarReductionPresentation res n) :=
  NormalizedReductionIdentifications L res.mapDerivedCategory
    ((DerivedCategory.singleFunctor A 0).obj P.S.X₁)
    ((DerivedCategory.singleFunctor A 0).obj P.S.X₃)
    ((DerivedCategory.singleFunctor B 0).obj P.H)
    ((DerivedCategory.singleFunctor B 0).obj P.Q)
    ((DerivedCategory.singleFunctor A 0).obj (res.obj P.Q))
    ((res.mapDerivedCategorySingleFunctor 0).hom.app P.Q)
    (ad.unit.app ((DerivedCategory.singleFunctor A 0).obj P.S.X₁))
    (ad.unit.app ((DerivedCategory.singleFunctor A 0).obj P.S.X₃))
    ((DerivedCategory.singleFunctor A 0).map P.p) (generic_kappa res n P)

private noncomputable def generic_boundary (P : ScalarReductionPresentation res n)
    (I : generic_identifications res L ad n P) :=
  I.alphaF.inv ≫ L.map P.exact.singleδ ≫
    (L.commShiftIso (1 : ℤ)).hom.app ((DerivedCategory.singleFunctor A 0).obj P.S.X₁) ≫
    I.alphaB.hom⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd (DerivedCategory B) (1 : ℤ) 1).inv.app
      ((DerivedCategory.singleFunctor B 0).obj P.H)

private theorem normalized_boundary_natural
    (P P' : ScalarReductionPresentation res n)
    (I : generic_identifications res L ad n P)
    (I' : generic_identifications res L ad n P')
    (f : P.S ⟶ P'.S) (h : P.H ⟶ P'.H) (q : P.Q ⟶ P'.Q)
    (hi : res.map h ≫ P'.i = P.i ≫ f.τ₁)
    (hp : f.τ₃ ≫ P'.p = P.p ≫ res.map q) :
    L.map ((DerivedCategory.singleFunctor A 0).map f.τ₃) ≫ I'.alphaF.hom =
      I.alphaF.hom ≫ (DerivedCategory.singleFunctor B 0).map q ∧
    L.map ((DerivedCategory.singleFunctor A 0).map f.τ₁) ≫ I'.alphaB.hom =
      I.alphaB.hom ≫ ((DerivedCategory.singleFunctor B 0).map h)⟦(1 : ℤ)⟧' ∧
    (DerivedCategory.singleFunctor B 0).map q ≫ generic_boundary res L ad n P' I' =
      generic_boundary res L ad n P I ≫
        ((DerivedCategory.singleFunctor B 0).map h)⟦(2 : ℤ)⟧' := by
  let F := DerivedCategory.singleFunctor A 0
  let G := DerivedCategory.singleFunctor B 0
  let R := res.mapDerivedCategory
  let c := res.mapDerivedCategorySingleFunctor 0
  have hF : L.map (F.map f.τ₃) ≫ I'.alphaF.hom =
      I.alphaF.hom ≫ G.map q := by
    apply ad.homEquiv _ _ |>.injective
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
    change ad.unit.app (F.obj P.S.X₃) ≫ R.map (L.map (F.map f.τ₃)) ≫ R.map I'.alphaF.hom =
      ad.unit.app (F.obj P.S.X₃) ≫ R.map I.alphaF.hom ≫ R.map (G.map q)
    apply (cancel_mono (c.hom.app P'.Q)).1
    rw [← Category.assoc (ad.unit.app (F.obj P.S.X₃)),
      show ad.unit.app (F.obj P.S.X₃) ≫ R.map (L.map (F.map f.τ₃)) =
        F.map f.τ₃ ≫ ad.unit.app (F.obj P'.S.X₃) from
          (ad.unit.naturality
            (F.map f.τ₃)).symm]
    simp only [Category.assoc]
    rw [I'.quotient_unit]
    rw [show R.map (G.map q) ≫ c.hom.app P'.Q =
      c.hom.app P.Q ≫ F.map (res.map q) from c.hom.naturality q]
    rw [reassoc_of% I.quotient_unit,
      ← F.map_comp, ← F.map_comp, hp]
  have hk : F.map f.τ₁ ≫ generic_kappa res n P' =
      generic_kappa res n P ≫ R.map ((G.map h)⟦(1 : ℤ)⟧') := by
    let k : ShortComplex.mk P.i (n • 𝟙 P.S.X₁) P.wi ⟶
        ShortComplex.mk P'.i (n • 𝟙 P'.S.X₁) P'.wi :=
      { τ₁ := res.map h
        τ₂ := f.τ₁
        τ₃ := f.τ₁
        comm₁₂ := hi
        comm₂₃ := by simp }
    have hk := (ShortComplex.ShortExact.singleTriangle.map P.kummer P'.kummer k).comm₃
    change P.kummer.singleδ ≫ (F.map (res.map h))⟦(1 : ℤ)⟧' =
      F.map f.τ₁ ≫ P'.kummer.singleδ at hk
    dsimp only [generic_kappa]
    rw [← reassoc_of% hk]
    simp only [Category.assoc]
    rw [← (shiftFunctor (DerivedCategory A) (1 : ℤ)).map_comp_assoc]
    rw [show F.map (res.map h) ≫ c.inv.app P'.H =
      c.inv.app P.H ≫ R.map (G.map h) from c.inv.naturality h]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [CategoryTheory.Functor.commShiftIso_inv_naturality]
  have hB : L.map (F.map f.τ₁) ≫ I'.alphaB.hom =
      I.alphaB.hom ≫ (G.map h)⟦(1 : ℤ)⟧' := by
    apply ad.homEquiv _ _ |>.injective
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
    change ad.unit.app (F.obj P.S.X₁) ≫ R.map (L.map (F.map f.τ₁)) ≫ R.map I'.alphaB.hom =
      ad.unit.app (F.obj P.S.X₁) ≫ R.map I.alphaB.hom ≫ R.map ((G.map h)⟦(1 : ℤ)⟧')
    rw [← Category.assoc (ad.unit.app (F.obj P.S.X₁)),
      show ad.unit.app (F.obj P.S.X₁) ≫ R.map (L.map (F.map f.τ₁)) =
        F.map f.τ₁ ≫ ad.unit.app (F.obj P'.S.X₁) from
          (ad.unit.naturality
            (F.map f.τ₁)).symm]
    rw [Category.assoc, I'.kummer_unit, ← Category.assoc, I.kummer_unit]
    exact hk
  refine ⟨hF, hB, ?_⟩
  have hFi : G.map q ≫ I'.alphaF.inv = I.alphaF.inv ≫ L.map (F.map f.τ₃) := by
    apply (cancel_epi I.alphaF.hom).1
    rw [← Category.assoc, ← hF]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hδ : F.map f.τ₃ ≫ P'.exact.singleδ =
      P.exact.singleδ ≫ (F.map f.τ₁)⟦(1 : ℤ)⟧' :=
    (ShortComplex.ShortExact.singleTriangle.map P.exact P'.exact f).comm₃.symm
  dsimp only [generic_boundary]
  simp only [Category.assoc]
  rw [reassoc_of% hFi]
  rw [← L.map_comp_assoc, hδ, L.map_comp]
  simp only [Category.assoc]
  rw [CategoryTheory.Functor.commShiftIso_hom_naturality_assoc]
  rw [← (shiftFunctor (DerivedCategory B) (1 : ℤ)).map_comp_assoc, hB]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hshift : ((G.map h)⟦(1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory B) (1 : ℤ) 1).inv.app (G.obj P'.H) =
      (shiftFunctorAdd (DerivedCategory B) (1 : ℤ) 1).inv.app (G.obj P.H) ≫
        (G.map h)⟦(2 : ℤ)⟧' :=
    (shiftFunctorAdd (DerivedCategory B) (1 : ℤ) 1).inv.naturality (G.map h)
  rw [hshift]

end GeneralBoundaryNaturality

section AbstractCokernel
set_option backward.isDefEq.respectTransparency false
variable {A₀ B₀ : Type*} [Category A₀] [Category B₀] [Abelian A₀]
  (E : A₀ ⥤ B₀) (R : B₀ ⥤ A₀) [R.Full] [R.Faithful]
  (a : E ⊣ R) (A : A₀) (g : A ⟶ A)
  (hz : g ≫ a.unit.app A = 0) (Q : B₀) (eQ : cokernel g ≅ R.obj Q)
private noncomputable def abstractUnitCokernel :
    IsColimit (CokernelCofork.ofπ (a.unit.app A) hz) := by
  let b := (a.homEquiv A Q).symm (cokernel.π g ≫ eQ.hom)
  have hb : a.unit.app A ≫ R.map b = cokernel.π g ≫ eQ.hom := by
    exact (Adjunction.homEquiv_unit a _ _ b).symm.trans (Equiv.apply_symm_apply _ _)
  let k := cokernel.desc g (a.unit.app A) hz
  let c := R.preimage (eQ.inv ≫ k)
  have hc : R.map c = eQ.inv ≫ k := CategoryTheory.Functor.map_preimage _ _
  have hbc : b ≫ c = 𝟙 _ := by
    apply (a.homEquiv A (E.obj A)).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    rw [← Category.assoc, hb, hc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    erw [Category.comp_id]
    exact cokernel.π_desc g (a.unit.app A) hz
  have hcb : c ≫ b = 𝟙 _ := by
    apply R.map_injective
    apply (cancel_epi (cokernel.π g ≫ eQ.hom)).1
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, cokernel.π_desc]
    exact hb
  let eb : E.obj A ≅ Q := ⟨b, c, hbc, hcb⟩
  let e := eQ ≪≫ (R.mapIso eb).symm
  have he : cokernel.π g ≫ e.hom = a.unit.app A := by
    change cokernel.π g ≫ eQ.hom ≫ R.map c = _
    rw [← Category.assoc, ← hb, Category.assoc, ← CategoryTheory.Functor.map_comp, hbc,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  let ei : CokernelCofork.ofπ (cokernel.π g) (cokernel.condition g) ≅
      CokernelCofork.ofπ (a.unit.app A) hz :=
    Cofork.ext e he
  exact IsColimit.ofIsoColimit (cokernelIsCokernel g) ei

end AbstractCokernel

section UnitTriangle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.Pretriangulated
variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : E ⊣ R) (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (n : ℕ) (P K : CochainComplex A ℤ) (p : P ⟶ K) [QuasiIso p] [IsIso (ε.app P)]
  (hz : (n • 𝟙 P) ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app P = 0)
  (hS : (ShortComplex.mk (n • 𝟙 P) ((a.mapHomologicalComplex (.up ℤ)).unit.app P)
    hz).ShortExact)
  (hnormal : ad.unit.app (DerivedCategory.Q.obj P) ≫ R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
include p hS hnormal in
private theorem unit_triangle :
    ∃ δ, Triangle.mk (n • 𝟙 (DerivedCategory.Q.obj K))
      (ad.unit.app (DerivedCategory.Q.obj K)) δ ∈ distTriang (DerivedCategory A) := by
  let e₁ : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K :=
    asIso (DerivedCategory.Q.map p)
  let e₃ : DerivedCategory.Q.obj
      ((R.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      R.mapDerivedCategory.obj (L.obj (DerivedCategory.Q.obj K)) :=
    (R.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
      R.mapDerivedCategory.mapIso (asIso (ε.app P)).symm ≪≫
      R.mapDerivedCategory.mapIso (L.mapIso e₁)
  let T := DerivedCategory.triangleOfSES hS
  let δ := e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
  let T' := Triangle.mk (n • 𝟙 (DerivedCategory.Q.obj K))
    (ad.unit.app (DerivedCategory.Q.obj K)) δ
  have he₂ : T.mor₂ ≫ e₃.hom = e₁.hom ≫ ad.unit.app (DerivedCategory.Q.obj K) := by
    have hnat := ad.unit.naturality e₁.hom
    change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      R.mapDerivedCategory.map (inv (ε.app P)) ≫
      R.mapDerivedCategory.map (L.map e₁.hom) = _
    erw [← hnormal]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← R.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact hnat.symm
  let eT : T ≅ T' := Triangle.isoMk T T' e₁ e₁ e₃ (by
    change DerivedCategory.Q.map (n • 𝟙 P) ≫ e₁.hom = e₁.hom ≫ (n • 𝟙 _)
    rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id]) he₂ (by
    change T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' =
      e₃.hom ≫ e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
    simp only [Iso.hom_inv_id_assoc])
  exact ⟨δ, isomorphic_distinguished T (DerivedCategory.triangleOfSES_distinguished hS)
    T' eT.symm⟩
end UnitTriangle


section Generic
universe a b c d e f
set_option backward.isDefEq.respectTransparency false
variable {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{c} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasDerivedCategory.{f} B]
  (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [R.Full] [R.Faithful]

omit [R.Faithful] in
private theorem pure_lift (n : ℤ) (X Y : DerivedCategory B)
    [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (t : R.mapDerivedCategory.obj X ⟶ R.mapDerivedCategory.obj Y) :
    ∃ u : X ⟶ Y, R.mapDerivedCategory.map u = t := by
  classical
  obtain ⟨M, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  obtain ⟨N, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n
  let c := R.mapDerivedCategorySingleFunctor n
  let eX' := R.mapDerivedCategory.mapIso eX ≪≫ c.app M
  let eY' := R.mapDerivedCategory.mapIso eY ≪≫ c.app N
  let f := (DerivedCategory.singleFunctor A n).preimage (eX'.inv ≫ t ≫ eY'.hom)
  let g := R.preimage f
  refine ⟨eX.hom ≫ (DerivedCategory.singleFunctor B n).map g ≫ eY.inv, ?_⟩
  have hf : (DerivedCategory.singleFunctor A n).map (R.map g) =
      eX'.inv ≫ t ≫ eY'.hom := by
    rw [R.map_preimage]
    exact (DerivedCategory.singleFunctor A n).map_preimage _
  simp only [Functor.map_comp]
  have hnat := c.hom.naturality g
  change R.mapDerivedCategory.map ((DerivedCategory.singleFunctor B n).map g) ≫
      c.hom.app N = c.hom.app M ≫
        (DerivedCategory.singleFunctor A n).map (R.map g) at hnat
  apply (cancel_mono (R.mapDerivedCategory.map eY.hom ≫ c.hom.app N)).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [hnat, hf]
  simp [eX', eY', Category.assoc]

omit [R.Full] [R.Faithful] in
private theorem reflect_derived_iso [R.ReflectsIsomorphisms] :
    R.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (R.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (R.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ R

private theorem normalized_pure_iso (L : DerivedCategory A ⥤ DerivedCategory B)
    (a : L ⊣ R.mapDerivedCategory) (n : ℤ) (X : DerivedCategory A) (Y : DerivedCategory B)
    [Y.IsGE n] [Y.IsLE n]
    (f : X ⟶ R.mapDerivedCategory.obj Y)
    (e : R.mapDerivedCategory.obj (L.obj X) ≅ R.mapDerivedCategory.obj Y)
    (he : a.unit.app X ≫ e.hom = f) :
    ∃! u : L.obj X ≅ Y, a.unit.app X ≫ R.mapDerivedCategory.map u.hom = f := by
  have : (R.mapDerivedCategory.obj Y).IsGE n := R.isGE_mapDerivedCategory_obj Y n
  have : (R.mapDerivedCategory.obj Y).IsLE n := R.isLE_mapDerivedCategory_obj Y n
  have hge : (R.mapDerivedCategory.obj (L.obj X)).IsGE n :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm n
  have hle : (R.mapDerivedCategory.obj (L.obj X)).IsLE n :=
    DerivedCategory.TStructure.t.isLE_of_iso e.symm n
  obtain ⟨hge', hle'⟩ :=
    R.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj ⟨hge, hle⟩
  let := hge'
  let := hle'
  obtain ⟨u, hu⟩ := pure_lift R n (L.obj X) Y e.hom
  have : R.ReflectsIsomorphisms := by infer_instance
  have : R.mapDerivedCategory.ReflectsIsomorphisms := reflect_derived_iso R
  have : IsIso (R.mapDerivedCategory.map u) := by rw [hu]; infer_instance
  have : IsIso u := isIso_of_reflects_iso u R.mapDerivedCategory
  refine ⟨asIso u, ?_, ?_⟩
  · simpa only [asIso_hom, hu] using he
  · intro u' hu'
    apply Iso.ext
    apply (a.homEquiv X Y).injective
    simp only [Adjunction.homEquiv_unit]
    exact hu'.trans (by simpa only [asIso_hom, hu] using he.symm)

end Generic

section DerivedSingle
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : E ⊣ R)
  (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (X : A) (Y : B) (b : E.obj X ⟶ Y) [IsIso b] (f : X ⟶ R.obj Y)
  (hb : a.unit.app X ≫ R.map b = f)
  (hε : IsIso (ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj X)))
  (hu : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj X) ≫
    R.mapDerivedCategory.map (ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj X)) ≫
      R.mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single A (.up ℤ) 0).obj X)) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app
      ((HomologicalComplex.single A (.up ℤ) 0).obj X)))
include E a ε b hb hε hu in
private theorem derived_single_iso : ∃ e : L.obj ((DerivedCategory.singleFunctor A 0).obj X) ≅
      (DerivedCategory.singleFunctor B 0).obj Y,
    ad.unit.app ((DerivedCategory.singleFunctor A 0).obj X) ≫
      R.mapDerivedCategory.map e.hom ≫ (R.mapDerivedCategorySingleFunctor 0).hom.app Y =
        (DerivedCategory.singleFunctor A 0).map f := by
  let K := (HomologicalComplex.single A (.up ℤ) 0).obj X
  let K' := (HomologicalComplex.single B (.up ℤ) 0).obj Y
  let cE := HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0
  let cR := HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0
  let β := cE.hom.app X ≫ (HomologicalComplex.single B (.up ℤ) 0).map b
  have hc : (a.mapHomologicalComplex (.up ℤ)).unit.app K ≫
      (R.mapHomologicalComplex (.up ℤ)).map β ≫ cR.hom.app Y =
      (HomologicalComplex.single A (.up ℤ) 0).map f := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        Adjunction.mapHomologicalComplex_unit_app_f, β,
        HomologicalComplex.single_map_f_self, cE, cR,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        Functor.map_comp, Category.assoc]
      erw [← a.unit.naturality_assoc]
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
      simp only [Iso.inv_hom_id_assoc, Category.comp_id, Functor.id_map]
      simpa only [Category.assoc] using congrArg
        (fun g ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫
          g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (R.obj Y)).inv) hb
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi).eq_of_src _ _
  let : IsIso (ε.app K) := hε
  let e : L.obj ((DerivedCategory.singleFunctor A 0).obj X) ≅
      (DerivedCategory.singleFunctor B 0).obj Y :=
    asIso (ε.app K) ≪≫ DerivedCategory.Q.mapIso (cE.app X) ≪≫
      (DerivedCategory.singleFunctor B 0).mapIso (asIso b)
  refine ⟨e, ?_⟩
  have hβ : e.hom = ε.app K ≫ DerivedCategory.Q.map β := by
    simp only [e, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, β, Functor.map_comp]
    rfl
  have hR : (R.mapDerivedCategorySingleFunctor 0).hom.app Y =
      R.mapDerivedCategoryFactors.hom.app K' ≫ DerivedCategory.Q.map (cR.hom.app Y) := by
    erw [← R.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app Y]
    erw [Iso.hom_inv_id_app_assoc]
  erw [hβ, hR, R.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  erw [R.mapDerivedCategoryFactors.hom.naturality_assoc β]
  erw [reassoc_of% hu]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫
    DerivedCategory.Q.map _ = DerivedCategory.Q.map _
  erw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp]
  exact DerivedCategory.Q.congr_map ((Category.assoc _ _ _).trans hc)

end DerivedSingle

section ShiftedComposition
variable {A : Type*} [Category* A] [HasShift A ℤ] {X Y Z : A}
private theorem shifted_comp_one_one (f : ShiftedHom X Y (1 : ℤ))
    (g : ShiftedHom Y Z (1 : ℤ)) :
    f.comp g (show (1 : ℤ) + 1 = 2 from rfl) =
      f ≫ g⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd A (1 : ℤ) 1).inv.app Z := by
  dsimp only [ShiftedHom.comp, shiftFunctorAdd']
  simp only [eqToIso_refl, Iso.refl_trans]
end ShiftedComposition

section ShiftedAdjunct
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Category* A] [Category* B]
  [HasShift A ℤ] [HasShift B ℤ] (L : A ⥤ B) (R : B ⥤ A)
  [L.CommShift ℤ] [R.CommShift ℤ] (ad : L ⊣ R) [ad.CommShift ℤ]
  {X Y : A} {H : B} (f : X ⟶ Y⟦(1 : ℤ)⟧)
  (a : L.obj Y ⟶ H⟦(1 : ℤ)⟧) (k : Y ⟶ R.obj (H⟦(1 : ℤ)⟧))
  (ha : ad.unit.app Y ≫ R.map a = k)
include ha in
private theorem shifted_boundary_adjunct :
    ad.homEquiv _ _ (L.map f ≫ (L.commShiftIso (1 : ℤ)).hom.app Y ≫ a⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd B (1 : ℤ) 1).inv.app H) =
    f ≫ k⟦(1 : ℤ)⟧' ≫ (R.commShiftIso (1 : ℤ)).inv.app (H⟦(1 : ℤ)⟧) ≫
      R.map ((shiftFunctorAdd B (1 : ℤ) 1).inv.app H) := by
  rw [Adjunction.homEquiv_unit, R.map_comp]
  erw [← Category.assoc, ← ad.unit.naturality f]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hu : ad.unit.app (Y⟦(1 : ℤ)⟧) ≫
      R.map ((L.commShiftIso (1 : ℤ)).hom.app Y) =
    (ad.unit.app Y)⟦(1 : ℤ)⟧' ≫ (R.commShiftIso (1 : ℤ)).inv.app (L.obj Y) := by
    apply (cancel_mono ((R.commShiftIso (1 : ℤ)).hom.app _)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    simpa only [CategoryTheory.Functor.commShiftIso_comp_hom_app, Category.assoc] using!
      ad.unit_app_commShiftIso_hom_app ℤ (1 : ℤ) Y
  rw [reassoc_of% hu]
  rw [← reassoc_of% R.commShiftIso_inv_naturality a (1 : ℤ)]
  rw [← (shiftFunctor A (1 : ℤ)).map_comp_assoc, ha]
  rfl
end ShiftedAdjunct

namespace SheafOfModules

section UnitKFlat
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})
private theorem unit_kflat : CochainComplex.IsKFlatIndependentCoefficients (R := R)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj
      (unit (derivedChangeRingIndependentCoefficients J R))) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF
  exact hF.of_iso (HomologicalComplex.rightUnitor F).symm
end UnitKFlat

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {Z R : Sheaf J CommRingCat.{r}} (q : Z ⟶ R)

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem scalarForget_preservesFiniteColimits (A : Sheaf J RingCat.{r}) :
    PreservesFiniteColimits (toSheaf.{r} A) := by
  constructor
  intro K _ _
  constructor
  intro F
  let L := PresheafOfModules.sheafification.{r} (𝟙 A.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r} (𝟙 A.obj)
  let G := F ⋙ (SheafOfModules.forget A ⋙ PresheafOfModules.restrictScalars (𝟙 A.obj))
  let e : G ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
  have : PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{r}) :=
    (sheafificationAdjunction J AddCommGrpCat.{r}).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimit G (L ⋙ toSheaf.{r} A) :=
    preservesColimit_of_natIso G (PresheafOfModules.sheafificationCompToSheaf (𝟙 A.obj)).symm
  let hc := colimit.isColimit G
  have : PreservesColimit (G ⋙ L) (toSheaf.{r} A) :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hc)
      (isColimitOfPreserves (L ⋙ toSheaf.{r} A) hc)
  exact preservesColimit_of_iso_diagram (toSheaf.{r} A) e

set_option linter.unusedSectionVars false in
/-- Restriction is exact: it retains the underlying abelian sheaf.
Source: Stacks 03D7 and 015F (blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: kernels are sectionwise kernels with restricted action. Cokernels are the
sheafifications of the same abelian presheaf quotients on both sides. Restriction
therefore preserves kernels and cokernels, hence all finite limits and colimits. -/
theorem sheafScalarRestriction_exact :
    PreservesFiniteLimits (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)) ∧
    PreservesFiniteColimits (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)) := by
  let Z' := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj Z
  let R' := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let res := restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)
  have := scalarForget_preservesFiniteColimits Z'
  have := scalarForget_preservesFiniteColimits R'
  have : PreservesFiniteLimits (res ⋙ toSheaf Z') :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{r} R'))
  have : PreservesFiniteColimits (res ⋙ toSheaf Z') :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{r} R'))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves res (toSheaf Z'),
    preservesFiniteColimits_of_reflects_of_preserves res (toSheaf Z')⟩

/-- Exact restriction preserves finite limits.
Source: Stacks 015F (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable instance sheafScalarRestrictionLimits :
    PreservesFiniteLimits (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)) :=
  (sheafScalarRestriction_exact q).1

/-- Exact restriction preserves finite colimits.
Source: Stacks 015F (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable instance sheafScalarRestrictionColimits :
    PreservesFiniteColimits (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)) :=
  (sheafScalarRestriction_exact q).2

private noncomputable abbrev sr {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (A : Sheaf K CommRingCat.{r}) := derivedChangeRingIndependentCoefficients K A

private noncomputable abbrev scalarRes
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :=
  restrictScalars.{r} ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency false

private theorem tensorRestriction_tmul
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) (M : SheafOfModules.{r} (sr K A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{v, u, r} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{v, u, r} c M i) s m

private noncomputable def tensorPresheafFunctor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (sr K A) ⥤ PresheafOfModules.{r} (sr K S).obj where
  obj M := changeOfRingsPresheaf.{v, u, r} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{v, u, r} c M ⟶
      changeOfRingsPresheaf.{v, u, r} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{v, u, r} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (sr K A) ⥤ SheafOfModules.{r} (sr K S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (sr K S).obj)

private noncomputable def tensorToRestriction
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S))
    (f : changeOfRingsPresheaf.{v, u, r} c M ⟶ H.val) : M ⟶ (scalarRes c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S))
    (g : M ⟶ (scalarRes c).obj H) : changeOfRingsPresheaf.{v, u, r} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{v, u, r} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S)) :
    (changeOfRingsPresheaf.{v, u, r} c M ⟶ H.val) ≃ (M ⟶ (scalarRes c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (scalarRes c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    {M N : SheafOfModules.{r} (sr K A)} (a : M ⟶ N)
    (H : SheafOfModules.{r} (sr K S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (sr K S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv
    (changeOfRingsPresheaf.{v, u, r} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A))
    {H H' : SheafOfModules.{r} (sr K S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (scalarRes c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) : tensorFunctor c ⊣
      scalarRes c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }


private theorem tensorAdjunction_homEquiv
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S)) :
    (tensorAdjunction c).homEquiv M H = tensorHomEquiv c M H := by
  unfold tensorAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]

attribute [irreducible] tensorAdjunction


private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]
  rfl

-- Bound unfolding while checking the denominator cone.
private theorem exactRestriction_denominator_constancy
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : HomotopyCategory A (.up ℤ)) :
    ∃ X : DerivedCategory B, IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (.up ℤ)) ⊤ K ⋙
        Under.forget K ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) X := by
  classical
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let G := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let H := MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ G
  have hG {X Y : HomotopyCategory A (.up ℤ)} (f : X ⟶ Y) (hf : W f) :
      IsIso (G.map f) := by
    have := Localization.inverts DerivedCategory.Qh W f hf
    let e := F.mapDerivedCategoryFactorsh
    change IsIso ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map f)
    rw [← NatIso.naturality_2 e.symm f]
    dsimp
    infer_instance
  let z : W.Under ⊤ K := MorphismProperty.Under.mk ⊤ (𝟙 K) (W.id_mem K)
  let p : H ⟶ (Functor.const _).obj (G.obj K) :=
    { app := fun j ↦ by
        have := hG j.hom j.prop
        exact inv (G.map j.hom)
      naturality := by
        intro i j f
        have := hG i.hom i.prop
        have := hG j.hom j.prop
        change G.map f.right ≫ inv (G.map j.hom) = inv (G.map i.hom) ≫ 𝟙 _
        rw [Category.comp_id]
        apply (cancel_epi (G.map i.hom)).1
        rw [← Category.assoc, ← G.map_comp, MorphismProperty.Under.w f]
        simp }
  have hfiltered : IsFiltered (W.Under ⊤ K) := by
    refine { nonempty := ⟨z⟩, cocone_objs := ?_, cocone_maps := ?_ }
    · intro i j
      obtain ⟨t, ht⟩ :=
        (MorphismProperty.RightFraction.mk i.hom i.prop j.hom).exists_leftFraction
      let k : W.Under ⊤ K := MorphismProperty.Under.mk ⊤
        (j.hom ≫ t.s) (W.comp_mem _ _ j.prop t.hs)
      exact ⟨k, MorphismProperty.Under.homMk t.f ht.symm,
        MorphismProperty.Under.homMk t.s, trivial⟩
    · intro i j f g
      obtain ⟨T, t, ht, hfg⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
        f.right g.right i.hom i.prop (f.w.symm.trans g.w)
      let k : W.Under ⊤ K := MorphismProperty.Under.mk ⊤
        (j.hom ≫ t) (W.comp_mem _ _ j.prop ht)
      exact ⟨k, MorphismProperty.Under.homMk t,
        MorphismProperty.Under.Hom.ext hfg⟩
  refine ⟨G.obj K, hfiltered, p, z, 𝟙 _, ?_, ?_⟩
  · simp [p, z]
  · intro j
    let f : z ⟶ j := MorphismProperty.Under.homMk j.hom (by simp [z])
    have := hG j.hom j.prop
    refine ⟨j, f, 𝟙 j, ?_⟩
    change G.map (𝟙 j.right) = inv (G.map j.hom) ≫ 𝟙 _ ≫ G.map j.hom
    simp


private theorem quotient_homotopy_iso_hom
    (A : Type*) [Category* A] [Abelian A] [HasDerivedCategory A]
    (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).hom.app K = 𝟙 _ := rfl

private theorem map_homotopy_iso_hom
    {A : Type*} [Category* A] [Abelian A]
    {B : Type*} [Category* B] [Abelian B] (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := rfl

private theorem map_derived_factorsh_component
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj K)) ≫
    F.mapDerivedCategoryFactors.hom.app K ≫ 𝟙 _ ≫
      DerivedCategory.Qh.map (𝟙 ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K))) = _
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
  erw [Category.id_comp, Category.comp_id, Category.comp_id]

private theorem derived_unit_from_compatibility
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : E ⊣ R)
    (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
    (α : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hc : ∀ (M : HomotopyCategory A (.up ℤ)) (N : HomotopyCategory B (.up ℤ))
      (f : (E.mapHomotopyCategory (.up ℤ)).obj M ⟶ N),
      ad.homEquiv _ _ (α.app M ≫ DerivedCategory.Qh.map f) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).homEquiv _ _ f) ≫
          R.mapDerivedCategoryFactorsh.inv.app N)
    (M : HomotopyCategory A (.up ℤ)) :
    ad.unit.app (DerivedCategory.Qh.obj M) ≫ R.mapDerivedCategory.map (α.app M) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((E.mapHomotopyCategory (.up ℤ)).obj M) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app M) := by
  have hh := hc M ((E.mapHomotopyCategory (.up ℤ)).obj M) (𝟙 _)
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_id] at hh
  have h := congrArg (fun f ↦ f ≫ R.mapDerivedCategoryFactorsh.hom.app
    ((E.mapHomotopyCategory (.up ℤ)).obj M)) hh
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
  exact h

set_option backward.isDefEq.respectTransparency true in
private theorem resolving_derived_adjunction
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (res : B ⥤ A) [res.Additive]
    [PreservesFiniteLimits res] [PreservesFiniteColimits res] (a : E ⊣ res)
    (H : CochainComplex A ℤ → Prop)
    (hresolve : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), H P ∧ QuasiIso p)
    (hpres : ∀ {P Q : CochainComplex A ℤ} (f : P ⟶ Q),
      H P → H Q → QuasiIso f → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f))
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (huniv : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))) :
    ∃ ad : L ⊣ res.mapDerivedCategory, ∀ K : CochainComplex A ℤ,
      ad.unit.app (DerivedCategory.Q.obj K) ≫ res.mapDerivedCategory.map (ε.app K) ≫
        res.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ,
      H K ∧
        (HomotopyCategory.quotient A (.up ℤ)).obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, hf⟩ := hresolve K
    exact ⟨_, (HomotopyCategory.quotient A (.up ℤ)).map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s →
        IsIso (F.map s) := by
    rintro X X' s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective s
    have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := hpres f hK hL hf
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨hpw, LF, α, hLF, _, _⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F P hres hinv
  have hL (M : HomotopyCategory A (.up ℤ)) :
      ∃ X : DerivedCategory B, IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (.up ℤ)) ⊤ M ⋙
          Over.forget M ⋙ F) X := by
    obtain ⟨X, _, hX, _⟩ := Functor.resolvingClass_essentialConstancy
      (HomotopyCategory.quasiIso A (.up ℤ)) F P hres hinv M
    exact ⟨X, hX⟩
  have hRF := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso B (.up ℤ)) res.mapDerivedCategory
    res.mapDerivedCategoryFactorsh
  obtain ⟨ad, had⟩ := exists_derived_adjunction_compatibility res E a
    (exactRestriction_denominator_constancy res) hL res.mapDerivedCategory LF
    res.mapDerivedCategoryFactorsh.inv α hRF hLF
  let qA := HomotopyCategory.quotient A (.up ℤ)
  let i := DerivedCategory.quotientCompQhIso A
  let j : qA ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let αc := Functor.whiskerRight i.inv LF ≫
    ((Functor.associator qA DerivedCategory.Qh LF).hom ≫ Functor.whiskerLeft qA α) ≫
      j.hom
  let := hpw
  let := hLF
  have hα := pointwise_precomp_full qA DerivedCategory.Qh F LF α
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF α
      (HomotopyCategory.quasiIso A (.up ℤ)))
  have hαc := pointwise_change_iso LF i j _ hα
  let : LF.IsLeftDerivedFunctor αc (HomologicalComplex.quasiIso A (.up ℤ)) :=
    ⟨hαc.isRightKanExtension⟩
  let := huniv
  let l : LF ≅ L := Functor.leftDerivedUnique L LF αc ε
    (HomologicalComplex.quasiIso A (.up ℤ))
  have hcomp (K : CochainComplex A ℤ) :
      l.hom.app (DerivedCategory.Q.obj K) ≫ ε.app K = αc.app K := by
    simp only [l, Functor.leftDerivedNatIso,
      Functor.leftDerivedNatTrans_app, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  clear_value l
  refine ⟨ad.ofNatIsoLeft l, ?_⟩
  intro K
  have hηh := derived_unit_from_compatibility E res a LF ad α had
  simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [← res.mapDerivedCategory.map_comp_assoc, hcomp]
  change ad.unit.app (DerivedCategory.Q.obj K) ≫ res.mapDerivedCategory.map (αc.app K) ≫
    res.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) = _
  have hi : i.inv.app K = 𝟙 _ := rfl
  have hj : j.hom.app K = 𝟙 _ := by
    simp only [j, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      map_homotopy_iso_hom, quotient_homotopy_iso_hom,
      ]
    erw [DerivedCategory.Qh.map_id]
    repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
    rfl
  have hαcK : αc.app K = α.app (qA.obj K) := by
    simp only [αc, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, hi, hj]
    change LF.map (𝟙 _) ≫ (𝟙 _ ≫ α.app (qA.obj K)) ≫ 𝟙 _ = _
    rw [LF.map_id]
    simp only [Category.id_comp, Category.comp_id]
  rw [hαcK]
  have hh := hηh (qA.obj K)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hh
  have hfac := map_derived_factorsh_component res
    ((E.mapHomologicalComplex (.up ℤ)).obj K)
  erw [hfac] at hh
  exact hh

variable [HasDerivedCategory.{wZ} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J Z))]
  [HasDerivedCategory.{wR} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J R))]
  (D : DerivedChangeOfRingsCochainModel q)

private theorem ordinary_scalar_adjunction_exists :
    ∃ a : D.E ⊣ restrictScalars.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q),
      (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J Z))
        (U : Cᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x =
          (eqToHom (D.obj_eq M).symm).val.app U
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).unit.app
                (changeOfRingsPresheaf q M)).app U
                  ((ModuleCat.extendRestrictScalarsAdj (q.hom.app U).hom).unit.app
                    (M.val.obj U) x))) := by
  classical
  let e : D.E ≅ tensorFunctor q := NatIso.ofComponents
    (fun M ↦ eqToIso (D.obj_eq M)) (by
      intro M N f
      change D.E.map f ≫ eqToHom (D.obj_eq N) =
        eqToHom (D.obj_eq M) ≫ changeOfRingsHom q M f
      rw [D.map_eq]
      simp)
  let a := (tensorAdjunction q).ofNatIsoLeft e.symm
  refine ⟨a, ?_⟩
  · intro M U x
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoLeft_apply,
      tensorAdjunction_homEquiv]
    change (tensorHomEquiv q M (D.E.obj M) (e.inv.app M ≫ 𝟙 _)).val.app U x = _
    simp only [Category.comp_id]
    rfl

-- Keep normalization comparisons from unfolding the sheafification implementation.
set_option backward.isDefEq.respectTransparency true in
/-- The ordinary and derived adjunctions, including both unit normalizations.
Source: Stacks 03D7, 015F, 09T5, 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: the sectionwise tensor/restriction adjunction sends m to 1 tensor m;
sheafification extends it uniquely and gives the first equation. Exactness of
restriction identifies its right derived functor with termwise restriction.
Apply the derived-adjoint-functors theorem to the universal pair D. On a K-flat
complex the ordinary unit has ordinary adjunct the identity. The pre-derived
adjunction formula therefore has derived adjunct the identity as well. This is
exactly the second equation, using D's universal counit and the localization
comparison for restriction. K-flat resolutions extend this formula to every
object, independently of its representative. -/
theorem sheafDerivedScalarAdjunction_exists :
    ∃ a : D.E ⊣ restrictScalars.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q),
      (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J Z))
        (U : Cᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x =
          (eqToHom (D.obj_eq M).symm).val.app U
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).unit.app
                (changeOfRingsPresheaf q M)).app U
                  ((ModuleCat.extendRestrictScalarsAdj (q.hom.app U).hom).unit.app
                    (M.val.obj U) x))) ∧
      ∃ ad : D.T ⊣ (restrictScalars.{r}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)).mapDerivedCategory,
        ∀ P : CochainComplex
          (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J Z)) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := Z) P →
          ad.unit.app (DerivedCategory.Q.obj P) ≫
            (restrictScalars.{r} ((sheafCompose J
              (forget₂ CommRingCat.{r} RingCat.{r})).map q)).mapDerivedCategory.map
                (D.ε.app P) ≫
            (restrictScalars.{r} ((sheafCompose J
              (forget₂ CommRingCat.{r} RingCat.{r})).map q)).mapDerivedCategoryFactors.hom.app
                ((D.E.mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P)  := by
  obtain ⟨a, ha⟩ := ordinary_scalar_adjunction_exists q D
  refine ⟨a, ha, ?_⟩
  obtain ⟨ad, had⟩ := resolving_derived_adjunction D.E (scalarRes q) a
    (fun K ↦ CochainComplex.IsKFlatIndependentCoefficients (R := Z) K)
    (fun K ↦ by
      obtain ⟨P, p, hP, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := Z) K
      exact ⟨P, p, hP, hp⟩)
    D.preserves D.T D.ε D.universal
  exact ⟨ad, fun K _ ↦ had K⟩


/-- The ordinary adjunction determined by its sectionwise unit.
Source: Stacks 03D7 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def sheafScalarOrdinaryAdjunction : D.E ⊣ restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q) :=
  Classical.choose (sheafDerivedScalarAdjunction_exists q D)

/-- The derived adjunction determined by its K-flat unit normalization.
Source: Stacks 09T5 and 0FND (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def sheafScalarDerivedAdjunction : D.T ⊣ (restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)).mapDerivedCategory :=
  Classical.choose (Classical.choose_spec (sheafDerivedScalarAdjunction_exists q D)).2

/-- The canonical shift comparison, induced from exact restriction by the normalized
adjunction. This fixes compatibility with its unit, instead of choosing an unrelated
triangulated shift structure. Source: Stacks 06YY and 09T5
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable instance sheafScalarModelCommShift : D.T.CommShift ℤ :=
  (sheafScalarDerivedAdjunction q D).leftAdjointCommShift ℤ


private theorem scalar_derived_unit
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J Z)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := Z) P) :
    (sheafScalarDerivedAdjunction q D).unit.app (DerivedCategory.Q.obj P) ≫
      (scalarRes q).mapDerivedCategory.map (D.ε.app P) ≫
      (scalarRes q).mapDerivedCategoryFactors.hom.app
        ((D.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((sheafScalarOrdinaryAdjunction q D).mapHomologicalComplex (.up ℤ)).unit.app P) :=
  Classical.choose_spec (Classical.choose_spec
    (sheafDerivedScalarAdjunction_exists q D)).2 P hP

set_option backward.isDefEq.respectTransparency true

end SheafOfModules

namespace SheafOfModules
namespace DivisibleReduction

attribute [local irreducible] sheafScalarOrdinaryAdjunction sheafScalarDerivedAdjunction


variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The constant integer ring sheaf. Source: Stacks 06YU and the Cartier proof,
paragraph 4 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev integers :=
  (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of (ULift.{r} ℤ))

/-- The constant residue ring sheaf. Source: Stacks 06YU and the Cartier proof,
paragraph 4 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev residues (n : ℕ) :=
  (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of (ULift.{r} (ZMod n)))

/-- The actual constant coefficient projection, induced by integer reduction.
Source: Stacks 06YU (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def projection (n : ℕ) : integers J ⟶ residues J n :=
  (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Int.castRingHom (ZMod n)).comp ULift.ringEquiv.toRingHom)))

/-- Integer module sheaves, using the recorded general ringed-site category.
Source: Stacks 06YU (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev Integral :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J (integers J))

/-- Residue module sheaves, using the recorded general ringed-site category.
Source: Stacks 06YU (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev Residue (n : ℕ) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J (residues J n))

/-- Ordinary restriction along the actual coefficient projection.
Source: Stacks 06YY (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev restriction (n : ℕ) : Residue J n ⥤ Integral J :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
    (projection J n))

/-- The unit integer sheaf, as a module over itself.
Source: Cartier proof, paragraph 5 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev integerUnit : Integral J :=
  unit (derivedChangeRingIndependentCoefficients J (integers J))

/-- The unit residue sheaf, as a module over itself.
Source: Cartier proof, paragraph 5 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev residueUnit (n : ℕ) : Residue J n :=
  unit (derivedChangeRingIndependentCoefficients J (residues J n))

/-- The ordinary coefficient unit sends 1 to 1 and is induced by the constant ring map.
Source: Stacks 06YU (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def coefficientUnit (n : ℕ) :
    integerUnit J ⟶ (restriction J n).obj (residueUnit J n) :=
  ((restriction J n).obj (residueUnit J n)).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : (residues J n).obj.obj U))
      (fun {_ _} f ↦ ((residues J n).obj.map f).hom.map_one))

variable {J} (n : ℕ)

/-- An extension and presentations of its torsion and quotient sheaves.
The two additional short exact sequences specify precisely ker(n on B), its natural
residue action, and coker(n on F); they also express epimorphy on B and monicity on F.
Source: Cartier proof, paragraph 4
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
abbrev Presentation := CategoryTheory.ScalarReductionPresentation (restriction J n) n

set_option backward.isDefEq.respectTransparency false

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem extension_unit_isIso (E : Integral J ⥤ Residue J n)
    (a : E ⊣ restriction J n) : IsIso ((a.homEquiv _ _).symm (coefficientUnit J n)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← (a.homEquiv _ _).bijective.of_comp_iff',
    ← (unitHomEquiv _).bijective.of_comp_iff']
  convert! M.unitHomEquiv.bijective using 1
  ext f : 1
  dsimp
  rw [a.homEquiv_naturality_right, Equiv.apply_symm_apply]
  ext U
  change (coefficientUnit J n ≫ (restriction J n).map f).val.app U
    (1 : (integers J).obj.obj U) = _
  change f.val.app U ((coefficientUnit J n).val.app U (1 : (integers J).obj.obj U)) = _
  have hc : (coefficientUnit J n).val.app U (1 : (integers J).obj.obj U) =
      (1 : (residues J n).obj.obj U) := by
    exact congrArg (fun s ↦ s.val U)
      (((restriction J n).obj (residueUnit J n)).unitHomEquiv.apply_symm_apply _)
  rw [hc]
  rfl

attribute [local irreducible] coefficientUnit

section PresentationConstruction

open CategoryTheory.Functor

private instance ringLocallyBijective : J.WEqualsLocallyBijective CommRingCat.{r} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, r, u, r+1, r, r, r} J

private noncomputable def ringUnit (A : CommRingCat.{r}) :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat).obj A)).obj :=
  whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) (forget₂ CommRingCat RingCat)

private instance ringUnit_ls (A : CommRingCat.{r}) :
    Presheaf.IsLocallySurjective J (ringUnit (J := J) A) :=
  ⟨fun x ↦ Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x⟩

private instance ringUnit_li (A : CommRingCat.{r}) :
    Presheaf.IsLocallyInjective J (ringUnit (J := J) A) :=
  ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x y h⟩

private instance integerForget_full :
    (toSheaf (derivedChangeRingIndependentCoefficients J (integers J))).Full where
  map_surjective {M N} f := by
    let α := ringUnit (J := J) (CommRingCat.of (ULift.{r} ℤ))
    let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
        (PresheafOfModules.restrictScalars α).obj N.val :=
      PresheafOfModules.homMk f.hom (by
        intro U z x
        obtain ⟨z⟩ := z
        change f.hom.app U ((α.app U).hom (z : ULift.{r} ℤ) • (show M.val.obj U from x)) =
          (α.app U).hom (z : ULift.{r} ℤ) • (show N.val.obj U from f.hom.app U x)
        rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact map_zsmul (f.hom.app U).hom z x)
    let g' := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).symm g
    refine ⟨⟨g'⟩, ?_⟩
    have h := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).apply_symm_apply g
    ext U x
    exact congrArg (fun k ↦ k.app U x) h

private noncomputable def liftTorsion (n : ℕ) (M : Integral J)
    (hM : ∀ (U : Cᵒᵖ) (x : M.val.obj U), n • x = 0) : Residue J n :=
  PresheafOfModules.sheafify (ringUnit (J := J) (CommRingCat.of (ULift.{r} (ZMod n))))
    (M₀ := CategoryTheory.Sheaf.presheafOfModulesOfNsmul M.val.presheaf hM)
    (A := (toSheaf _).obj M) (𝟙 _)

private noncomputable def liftTorsionIso (n : ℕ) (M : Integral J)
    (hM : ∀ (U : Cᵒᵖ) (x : M.val.obj U), n • x = 0) :
    M ≅ (restriction J n).obj (liftTorsion n M hM) :=
  (toSheaf (derivedChangeRingIndependentCoefficients J (integers J))).preimageIso (Iso.refl _)
attribute [irreducible] liftTorsion liftTorsionIso

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem nsmul_sections_of_id (n : ℕ) (M : Integral J)
    (h : n • 𝟙 M = 0) (U : Cᵒᵖ) (x : M.val.obj U) : n • x = 0 := by
  let ev := toSheaf (derivedChangeRingIndependentCoefficients J (integers J)) ⋙
    sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U
  have he := ev.congr_map h
  rw [ev.map_nsmul, ev.map_id, ev.map_zero] at he
  have hx := ConcreteCategory.congr_hom he x
  simpa using hx


omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem residue_nsmul_zero (n : ℕ) (M : Residue J n)
    (U : Cᵒᵖ) (x : M.val.obj U) : n • x = 0 := by
  have h : (n : ULift.{r} (ZMod n)) = 0 :=
    ULift.ext _ _ (by rw [ULift.down_natCast, ZMod.natCast_self]; rfl)
  let α := ringUnit (J := J) (CommRingCat.of (ULift.{r} (ZMod n)))
  have h' : (α.app U).hom (n : ULift.{r} (ZMod n)) =
      (n : (residues J n).obj.obj U) := map_natCast _ n
  rw [← Nat.cast_smul_eq_nsmul (R := (residues J n).obj.obj U),
    ← h', h, map_zero, zero_smul]

private instance restriction_faithful (n : ℕ) : (restriction J n).Faithful := by
  refine ⟨fun {M N} f g h ↦ ?_⟩
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) h

private instance restriction_full (n : ℕ) [NeZero n] : (restriction J n).Full where
  map_surjective {M N} f := by
    let α := ringUnit (J := J) (CommRingCat.of (ULift.{r} (ZMod n)))
    let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
        (PresheafOfModules.restrictScalars α).obj N.val :=
      PresheafOfModules.homMk
        ((toSheaf (derivedChangeRingIndependentCoefficients J (integers J))).map f).hom (by
        intro U z x
        obtain ⟨z⟩ := z
        have hz : (⟨z⟩ : ULift.{r} (ZMod n)) = (z.val : ULift.{r} (ZMod n)) :=
          ULift.ext _ _ (by rw [ULift.down_natCast, ZMod.natCast_zmod_val])
        change f.val.app U ((α.app U).hom (⟨z⟩ : ULift.{r} (ZMod n)) •
          (show M.val.obj U from x)) =
          (α.app U).hom (⟨z⟩ : ULift.{r} (ZMod n)) •
            (show N.val.obj U from f.val.app U x)
        rw [hz, map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        exact map_nsmul (f.val.app U).hom z.val x)
    let g' := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).symm g
    refine ⟨⟨g'⟩, ?_⟩
    have h := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).apply_symm_apply g
    ext U x
    exact congrArg (fun k ↦ k.app U x) h

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem ordinaryUnit_zero (n : ℕ) (E : Integral J ⥤ Residue J n)
    (a : E ⊣ restriction J n) (A : Integral J) :
    (n • 𝟙 A) ≫ a.unit.app A = 0 := by
  ext U x
  change (a.unit.app A).val.app U ((n • 𝟙 A).val.app U x) = 0
  have hx : (n • 𝟙 A).val.app U x = n • x := by
    let ev := toSheaf (derivedChangeRingIndependentCoefficients J (integers J)) ⋙
      sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U
    have he := ev.map_nsmul (f := 𝟙 A) (n := n)
    rw [ev.map_id] at he
    exact ConcreteCategory.congr_hom he x
  rw [hx]
  rw [_root_.map_nsmul]
  exact residue_nsmul_zero n (E.obj A) U _

private noncomputable def ordinaryUnit_cokernel (n : ℕ) [NeZero n]
    (E : Integral J ⥤ Residue J n) (a : E ⊣ restriction J n) (A : Integral J) :
    IsColimit (CokernelCofork.ofπ (a.unit.app A) (ordinaryUnit_zero n E a A)) := by
  let g := n • 𝟙 A
  have hnQ : n • 𝟙 (cokernel g) = 0 := by
    apply (cancel_epi (cokernel.π g)).1
    simpa only [g, Preadditive.nsmul_comp, Category.id_comp,
      Preadditive.comp_nsmul, Category.comp_id, comp_zero] using cokernel.condition g
  let Q := liftTorsion n (cokernel g) (nsmul_sections_of_id n _ hnQ)
  let eQ : cokernel g ≅ (restriction J n).obj Q :=
    liftTorsionIso n (cokernel g) (nsmul_sections_of_id n _ hnQ)
  exact abstractUnitCokernel E (restriction J n) a A g
    (ordinaryUnit_zero n E a A) Q eQ

private theorem integerUnit_mono (n : ℕ) (hn : n ≠ 0) :
    Mono (n • 𝟙 (integerUnit J)) := by
  let F := toSheaf (derivedChangeRingIndependentCoefficients J (integers J))
  let FF := forget₂ CommRingCat.{r} RingCat.{r} ⋙ forget₂ RingCat.{r} AddCommGrpCat.{r}
  have : J.PreservesSheafification FF := by
    constructor
    intro P Q f hf
    change J.W (CategoryTheory.Functor.whiskerRight f FF)
    rw [J.W_iff_isLocallyBijective] at hf ⊢
    let := hf.1
    let := hf.2
    exact ⟨⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩,
      ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩⟩
  let e : F.obj (integerUnit J) ≅
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{r} ℤ)) :=
    (constantCommuteCompose J
      (forget₂ CommRingCat.{r} RingCat.{r} ⋙ forget₂ RingCat.{r} AddCommGrpCat.{r})).app
      (CommRingCat.of (ULift.{r} ℤ))
  have hm : Mono (n • 𝟙 (AddCommGrpCat.of (ULift.{r} ℤ))) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y h
    change n • x = n • y at h
    exact ULift.ext _ _ (nsmul_right_injective hn (congrArg ULift.down h))
  have hm' : Mono (n • 𝟙 ((constantSheaf J AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{r} ℤ)))) := by
    have : Mono ((CategoryTheory.Functor.const Cᵒᵖ).map
        (n • 𝟙 (AddCommGrpCat.of (ULift.{r} ℤ)))) := NatTrans.mono_of_mono_app _
    have : Mono ((presheafToSheaf J AddCommGrpCat).map
        ((CategoryTheory.Functor.const Cᵒᵖ).map
          (n • 𝟙 (AddCommGrpCat.of (ULift.{r} ℤ))))) := inferInstance
    simpa only [constantSheaf, CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using this
  have hm'' : Mono (n • 𝟙 (F.obj (integerUnit J))) := by
    have he : (n • 𝟙 (F.obj (integerUnit J))) ≫ e.hom =
        e.hom ≫ (n • 𝟙 _) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    exact mono_of_mono_fac he
  apply F.mono_of_mono_map
  simpa only [F.map_nsmul, F.map_id] using hm''

private theorem flat_multiplication_mono (n : ℕ) (hn : n ≠ 0) (M : Integral J)
    (hM : letI := SheafOfModules.isMonoidal_W_independentCoefficients (integers J)
      exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (monoidalCategory (integers J)) M)) :
    Mono (n • 𝟙 M) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (integers J)
  let := monoidalCategory (integers J)
  let := symmetricCategory (integers J)
  let F := MonoidalCategory.tensorRight M
  have : PreservesFiniteLimits F := hM.1
  have : Mono (n • 𝟙 (integerUnit J)) := integerUnit_mono n hn
  have : Mono (F.map (n • 𝟙 (integerUnit J))) := inferInstance
  have hm : Mono (n • 𝟙 (F.obj (integerUnit J))) := by
    simpa only [F.map_nsmul, F.map_id] using this
  have he : (n • 𝟙 M) ≫ (MonoidalCategory.leftUnitor M).inv =
      (MonoidalCategory.leftUnitor M).inv ≫ (n • 𝟙 (F.obj (integerUnit J))) := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp]
    erw [Category.comp_id]
  exact mono_of_mono_fac he

private theorem multiplication_resolving (n : ℕ) [NeZero n]
    (K : CochainComplex (Integral J) ℤ) :
    ∃ (P : CochainComplex (Integral J) ℤ) (p : P ⟶ K),
      CochainComplex.IsKFlatIndependentCoefficients (R := integers J) P ∧
        (∀ i : ℤ, Mono (n • 𝟙 (P.X i))) ∧ QuasiIso p := by
  obtain ⟨P, p, hP, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := integers J) K
  exact ⟨P, p, hP, fun i ↦ flat_multiplication_mono n (NeZero.ne n) (P.X i) (hf i), hp⟩

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem multiplication_complex_zero (n : ℕ)
    (E : Integral J ⥤ Residue J n) [E.Additive] (a : E ⊣ restriction J n)
    (P : CochainComplex (Integral J) ℤ) :
    (n • 𝟙 P) ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app P = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, HomologicalComplex.nsmul_f_apply,
    HomologicalComplex.id_f, HomologicalComplex.zero_f,
    Adjunction.mapHomologicalComplex_unit_app_f]
  exact ordinaryUnit_zero n E a (P.X i)

private theorem multiplication_complex_shortExact (n : ℕ) [NeZero n]
    (E : Integral J ⥤ Residue J n) [E.Additive] (a : E ⊣ restriction J n)
    (P : CochainComplex (Integral J) ℤ)
    (hmono : ∀ i : ℤ, Mono (n • 𝟙 (P.X i))) :
    (ShortComplex.mk (n • 𝟙 P) ((a.mapHomologicalComplex (.up ℤ)).unit.app P)
      (multiplication_complex_zero n E a P)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let g := n • 𝟙 (P.X i)
  have : Mono g := hmono i
  let hc := ordinaryUnit_cokernel n E a (P.X i)
  have : Epi (a.unit.app (P.X i)) :=
    Cofork.IsColimit.epi hc
  have hs : (ShortComplex.mk g (a.unit.app (P.X i))
      (ordinaryUnit_zero n E a (P.X i))).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ hc }
  convert! hs using 1



set_option backward.isDefEq.respectTransparency true in
/-- Every extension under the node's hypotheses has these coefficient presentations.
Source: Cartier proof, paragraph 4; Stacks 06YU
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: take the kernel of n on B and the sheaf cokernel of n on F. Multiplication
by n vanishes on each; locally integer scalar multiplication therefore factors
uniquely through Z/n, and these actions glue through constant sheafification.
The kernel inclusion and quotient projection are integer-linear. Epi on B and
mono on F give the two displayed short exact sequences. The universal properties
of kernel and cokernel identify any two presentations uniquely. -/
theorem presentation_exists [HasTerminal C] (hn : 1 ≤ n)
    (S : ShortComplex (Integral J)) (hS : S.ShortExact)
    (hB : Epi (n • 𝟙 S.X₁)) (hF : Mono (n • 𝟙 S.X₃)) :
    ∃ P : Presentation (J := J) n, P.S = S := by
  have _ := hn
  let gB := n • 𝟙 S.X₁
  let gF := n • 𝟙 S.X₃
  have hnK : n • 𝟙 (kernel gB) = 0 := by
    apply (cancel_mono (kernel.ι gB)).1
    simpa only [gB, Preadditive.nsmul_comp, Category.id_comp,
      Preadditive.comp_nsmul, Category.comp_id, zero_comp] using kernel.condition gB
  have hnQ : n • 𝟙 (cokernel gF) = 0 := by
    apply (cancel_epi (cokernel.π gF)).1
    simpa only [gF, Preadditive.nsmul_comp, Category.id_comp,
      Preadditive.comp_nsmul, Category.comp_id, comp_zero] using cokernel.condition gF
  have hK (U : Cᵒᵖ) (x : (kernel gB).val.obj U) : n • x = 0 := by
    exact nsmul_sections_of_id n _ hnK U x
  have hQ (U : Cᵒᵖ) (x : (cokernel gF).val.obj U) : n • x = 0 := by
    exact nsmul_sections_of_id n _ hnQ U x
  let H := liftTorsion n (kernel gB) hK
  let Q := liftTorsion n (cokernel gF) hQ
  let eH := liftTorsionIso n (kernel gB) hK
  let eQ := liftTorsionIso n (cokernel gF) hQ
  let i := eH.inv ≫ kernel.ι gB
  let p := cokernel.π gF ≫ eQ.hom
  have wi : i ≫ (n • 𝟙 S.X₁) = 0 := by
    change i ≫ gB = 0
    simp only [i, Category.assoc, kernel.condition, comp_zero]
  have wp : (n • 𝟙 S.X₃) ≫ p = 0 := by
    change gF ≫ p = 0
    simp only [p, ← Category.assoc, cokernel.condition, zero_comp]
  have : Epi gB := hB
  have : Mono gF := hF
  have hk : (ShortComplex.mk (kernel.ι gB) gB (kernel.condition gB)).ShortExact :=
    { exact := ShortComplex.exact_kernel gB }
  have hq : (ShortComplex.mk gF (cokernel.π gF) (cokernel.condition gF)).ShortExact :=
    { exact := ShortComplex.exact_cokernel gF }
  have hik : (ShortComplex.mk i (n • 𝟙 S.X₁) wi).ShortExact := by
    let e : ShortComplex.mk (kernel.ι gB) gB (kernel.condition gB) ≅
        ShortComplex.mk i (n • 𝟙 S.X₁) wi :=
      ShortComplex.isoMk eH (Iso.refl _) (Iso.refl _) (by
        simp only [Iso.refl_hom, Category.comp_id, i, Iso.hom_inv_id_assoc]) (by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl)
    exact (ShortComplex.shortExact_iff_of_iso e).1 hk
  have hpq : (ShortComplex.mk (n • 𝟙 S.X₃) p wp).ShortExact := by
    let e : ShortComplex.mk gF (cokernel.π gF) (cokernel.condition gF) ≅
        ShortComplex.mk (n • 𝟙 S.X₃) p wp :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) eQ (by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        rfl) (by
        simp only [Iso.refl_hom, Category.id_comp, p])
    exact (ShortComplex.shortExact_iff_of_iso e).1 hq
  exact ⟨{
    S := S
    exact := hS
    H := H
    Q := Q
    i := i
    p := p
    wi := wi
    wp := wp
    kummer := hik
    quotient := hpq }, rfl⟩

end PresentationConstruction

variable [HasDerivedCategory.{wZ} (Integral J)]
  [HasDerivedCategory.{wR} (Residue J n)]
  (D : DerivedChangeOfRingsCochainModel (projection J n))

/-- Termwise derived restriction.
Source: Stacks 015F (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev derivedRestriction := (restriction J n).mapDerivedCategory

/-- The normalized derived scalar unit on an integer module sheaf.
Source: Stacks 09T5, 0FND (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def eta (A : Integral J) :=
  (sheafScalarDerivedAdjunction (projection J n) D).unit.app
    ((DerivedCategory.singleFunctor (Integral J) 0).obj A)

/-- The canonical Kummer boundary, with termwise restriction and single comparison.
Source: Stacks 0152 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def kappa (P : Presentation (J := J) n) :=
  P.kummer.singleδ ≫
    (((restriction J n).mapDerivedCategorySingleFunctor 0).inv.app P.H)⟦(1 : ℤ)⟧' ≫
    ((derivedRestriction n).commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)

/-- Normalized reduction identifications. The quotient isomorphism induces the actual
quotient projection on units; the torsion isomorphism induces the Kummer boundary.
Source: Cartier proof, paragraphs 4 and 5; Stacks 06YY and 0152
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
abbrev Identifications (P : Presentation (J := J) n) :=
  CategoryTheory.NormalizedReductionIdentifications D.T (derivedRestriction n)
    ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₁)
    ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₃)
    ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)
    ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.Q)
    ((DerivedCategory.singleFunctor (Integral J) 0).obj ((restriction J n).obj P.Q))
    (((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app P.Q)
    (eta n D P.S.X₁) (eta n D P.S.X₃)
    ((DerivedCategory.singleFunctor (Integral J) 0).map P.p) (kappa n P)

open CategoryTheory.Pretriangulated

private theorem multiplication_triangle [NeZero n] (A : Integral J) :
    ∃ δ, Triangle.mk (n • 𝟙 ((DerivedCategory.singleFunctor (Integral J) 0).obj A))
      (eta n D A) δ ∈ distTriang (DerivedCategory (Integral J)) := by
  classical
  let R := restriction J n
  let a := sheafScalarOrdinaryAdjunction (projection J n) D
  let ad := sheafScalarDerivedAdjunction (projection J n) D
  let K := (CochainComplex.singleFunctor (Integral J) 0).obj A
  obtain ⟨P, p, hP, hm, hp⟩ := multiplication_resolving n K
  have : QuasiIso p := hp
  have : IsIso (D.ε.app P) := D.computes P hP
  have hnormal := scalar_derived_unit (projection J n) D P hP
  exact unit_triangle D.E R a D.T ad D.ε n P K p
    (multiplication_complex_zero n D.E a P)
    (multiplication_complex_shortExact n D.E a P hm) hnormal


set_option backward.isDefEq.respectTransparency true in
/-- The two reduction isomorphisms, with their canonical unit normalization.
Source: Cartier proof, paragraphs 4 and 5; Stacks 06YU, 06YY, 0152, 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof:
1. Use the normalized scalar adjunction (sk-def-sfb-derived-extension-of-scalars).
   Exact restriction is termwise, and its derived unit on a K-flat representative
   is the ordinary coefficient unit; this formula commutes with shifts.
2. The constant sequence Z --n--> Z --> R is exact, and A tensor R = coker(n on A).
   Both assertions follow locally from integers and their residue classes.
3. Resolve A by a flat-term K-flat complex P (lem-pc-kflat-resolution).
   The termwise multiplication sequence gives the distinguished triangle
   A --n--> A --eta--> Res Lq(A) --> A[1]
   (lem-pur-derived-change-of-rings; lem-weil-pbc-complex-ses-triangle).
4. Its long exact cohomology sequence gives only degrees -1 and 0, the kernel
   and cokernel of n (lem-sf-derived-homology-long-exact). Use the rotated triangle
   to fix the map to A, rather than an unspecified cohomology boundary.
5. Canonical truncation in residue modules identifies a complex with its sole
   cohomology sheaf in the appropriate degree (def-sbc-standard-tstructure-derived-category).
6. Compare the multiplication triangle for B with the rotated Kummer triangle
   B --n--> B --kappa--> H[1] ---i[1]--> B[1]. TR3 fixes the identification by
   (-i) H^-1(alphaB) = H^-1(delta). Monicity of i fixes its sign uniquely.
   Shifted single-object full faithfulness identifies its restriction with that
   triangle map (lem-weil-pbc-derived-single-fully-faithful).
7. The quotient unit fixes alphaF uniquely because p is epi. The Kummer unit
   fixes alphaB uniquely: Hom(B,H)=0 by n-divisibility, and the Kummer exact
   Hom sequence makes precomposition with kappa injective on End(H[1]).
   Residue-linearity is automatic for integer-linear maps of n-annihilated sheaves.
   These facts give uniqueness, not an unspecified choice of either isomorphism. -/
theorem divisible_extension_derived_reduction [HasTerminal C] (hn : 1 ≤ n)
    (P : Presentation (J := J) n) : Nonempty (Unique (Identifications n D P)) := by
  classical
  let : NeZero n := ⟨by omega⟩
  let R := restriction J n
  let F := DerivedCategory.singleFunctor (Integral J) 0
  let G := DerivedCategory.singleFunctor (Residue J n) 0
  let c := R.mapDerivedCategorySingleFunctor 0
  let a := sheafScalarDerivedAdjunction (projection J n) D
  obtain ⟨δF, hδF⟩ := multiplication_triangle n D P.S.X₃
  let TF := Triangle.mk (n • 𝟙 (F.obj P.S.X₃)) (eta n D P.S.X₃) δF
  let tF := Pretriangulated.isoTriangleOfIso₁₂ TF P.quotient.singleTriangle
    hδF P.quotient.singleTriangle_distinguished (Iso.refl _) (Iso.refl _) (by
      change (n • 𝟙 (F.obj P.S.X₃)) ≫ 𝟙 _ =
        (𝟙 _) ≫ F.map (n • 𝟙 P.S.X₃)
      simp only [Category.comp_id, Category.id_comp,
        CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id])
  let eF : R.mapDerivedCategory.obj (D.T.obj (F.obj P.S.X₃)) ≅
      R.mapDerivedCategory.obj (G.obj P.Q) :=
    Triangle.π₃.mapIso tF ≪≫ (c.app P.Q).symm
  have heF : a.unit.app (F.obj P.S.X₃) ≫ eF.hom = F.map P.p ≫ c.inv.app P.Q := by
    have h := tF.hom.comm₂
    dsimp only [tF] at h
    set_option backward.isDefEq.respectTransparency false in
      simp only [Pretriangulated.isoTriangleOfIso₁₂_hom_hom₂, Iso.refl_hom,
        Category.id_comp] at h
    change eta n D P.S.X₃ ≫ _ = F.map P.p at h
    change eta n D P.S.X₃ ≫ (Triangle.π₃.mapIso tF).hom = F.map P.p at h
    change eta n D P.S.X₃ ≫ (Triangle.π₃.mapIso tF).hom ≫ c.inv.app P.Q = _
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ c.inv.app P.Q) h)
  obtain ⟨αF, hαF, huniqF⟩ := normalized_pure_iso R D.T a 0 (F.obj P.S.X₃)
    (G.obj P.Q) (F.map P.p ≫ c.inv.app P.Q) eF heF
  obtain ⟨δB, hδB⟩ := multiplication_triangle n D P.S.X₁
  let TB := Triangle.mk (n • 𝟙 (F.obj P.S.X₁)) (eta n D P.S.X₁) δB
  let tB := Pretriangulated.isoTriangleOfIso₁₂ TB P.kummer.singleTriangle.rotate
    hδB (Pretriangulated.rot_of_distTriang _ P.kummer.singleTriangle_distinguished)
    (Iso.refl _) (Iso.refl _) (by
      change (n • 𝟙 (F.obj P.S.X₁)) ≫ 𝟙 _ =
        (𝟙 _) ≫ F.map (n • 𝟙 P.S.X₁)
      simp only [Category.comp_id, Category.id_comp,
        CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id])
  let eB : R.mapDerivedCategory.obj (D.T.obj (F.obj P.S.X₁)) ≅
      R.mapDerivedCategory.obj ((G.obj P.H)⟦(1 : ℤ)⟧) :=
    Triangle.π₃.mapIso tB ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso (c.app P.H).symm ≪≫
    (R.mapDerivedCategory.commShiftIso (1 : ℤ)).symm.app (G.obj P.H)
  have heB : a.unit.app (F.obj P.S.X₁) ≫ eB.hom = kappa n P := by
    have h := tB.hom.comm₂
    dsimp only [tB] at h
    set_option backward.isDefEq.respectTransparency false in
      simp only [Pretriangulated.isoTriangleOfIso₁₂_hom_hom₂, Iso.refl_hom,
        Category.id_comp] at h
    change eta n D P.S.X₁ ≫ _ = P.kummer.singleδ at h
    change eta n D P.S.X₁ ≫ (Triangle.π₃.mapIso tB).hom ≫ _ ≫ _ = _
    change eta n D P.S.X₁ ≫ (Triangle.π₃.mapIso tB).hom = P.kummer.singleδ at h
    erw [← Category.assoc, ← Category.assoc, h]
    exact Category.assoc _ _ _
  have : (G.obj P.H)⟦(1 : ℤ)⟧ |>.IsGE (-1) :=
    DerivedCategory.TStructure.t.isGE_shift (G.obj P.H) 0 1 (-1) (by decide)
  have : (G.obj P.H)⟦(1 : ℤ)⟧ |>.IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_shift (G.obj P.H) 0 1 (-1) (by decide)
  obtain ⟨αB, hαB, huniqB⟩ := normalized_pure_iso R D.T a (-1) (F.obj P.S.X₁)
    ((G.obj P.H)⟦(1 : ℤ)⟧) (kappa n P) eB heB
  have hαF' : eta n D P.S.X₃ ≫ R.mapDerivedCategory.map αF.hom ≫
      c.hom.app P.Q = F.map P.p := by
    erw [← Category.assoc, hαF]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  let I : Identifications n D P := ⟨αF, αB, hαF', hαB⟩
  refine ⟨{ default := I, uniq := ?_ }⟩
  rintro ⟨βF, βB, hβF, hβB⟩
  have hF : βF = αF := huniqF βF (by
    apply (cancel_mono (c.hom.app P.Q)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hβF)
  have hB : βB = αB := huniqB βB hβB
  cases hF
  cases hB
  rfl


/-- The unique normalized identifications; their data is determined by the unit equations.
Source: Cartier proof, paragraph 4
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def identifications [HasTerminal C] (hn : 1 ≤ n)
    (P : Presentation (J := J) n) : Identifications n D P :=
  (Classical.choice (divisible_extension_derived_reduction n D hn P)).default

attribute [local irreducible] identifications

/-- The reduced extension boundary, with the canonical comparison [1][1] = [2].
Source: Cartier proof, paragraph 4
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def boundary [HasTerminal C] (hn : 1 ≤ n) (P : Presentation (J := J) n) :
    (DerivedCategory.singleFunctor (Residue J n) 0).obj P.Q ⟶
      ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)⟦(2 : ℤ)⟧ :=
  (identifications n D hn P).alphaF.inv ≫ D.T.map P.exact.singleδ ≫
    (D.T.commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₁) ≫
    (identifications n D hn P).alphaB.hom⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd (DerivedCategory (Residue J n)) (1 : ℤ) 1).inv.app
      ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)

set_option backward.isDefEq.respectTransparency true in
/-- The unit object reduces canonically to the residue unit.
Source: Cartier proof, paragraph 5; Stacks 06YU, 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: Z[0] is K-flat since tensoring with it is the identity. Apply the K-flat
counit to identify its scalar extension with R[0]. The normalized derived unit
is the ordinary coefficient map. Conversely this unit equation determines the
isomorphism, by the scalar adjunction and the fact that a map of residue unit
sheaves is fixed on 1. -/
theorem coefficientIso_existsUnique [HasTerminal C] (hn : 1 ≤ n) :
    ∃! e : D.T.obj ((DerivedCategory.singleFunctor (Integral J) 0).obj (integerUnit J)) ≅
        (DerivedCategory.singleFunctor (Residue J n) 0).obj (residueUnit J n),
      eta n D (integerUnit J) ≫ (derivedRestriction n).map e.hom ≫
        ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app (residueUnit J n) =
      (DerivedCategory.singleFunctor (Integral J) 0).map (coefficientUnit J n) := by
  have _ := hn
  classical
  let a := sheafScalarOrdinaryAdjunction (projection J n) D
  let K := (HomologicalComplex.single (Integral J) (.up ℤ) 0).obj (integerUnit J)
  have hK : CochainComplex.IsKFlatIndependentCoefficients (R := integers J) K :=
    SheafOfModules.unit_kflat (integers J)
  let b := (a.homEquiv _ _).symm (coefficientUnit J n)
  have hb : IsIso b := extension_unit_isIso n D.E a
  have hε : IsIso (D.ε.app K) := D.computes K hK
  have hbunit : a.unit.app (integerUnit J) ≫ (restriction J n).map b =
      coefficientUnit J n := by
    exact (Adjunction.homEquiv_unit a _ _ b).symm.trans (Equiv.apply_symm_apply _ _)
  have hnormal := scalar_derived_unit (projection J n) D K hK
  obtain ⟨e, he⟩ := derived_single_iso D.E (restriction J n) a D.T
    (sheafScalarDerivedAdjunction (projection J n) D) D.ε
    (integerUnit J) (residueUnit J n) b (coefficientUnit J n) hbunit hε hnormal
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (sheafScalarDerivedAdjunction (projection J n) D).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply (cancel_mono
    (((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app
      (residueUnit J n))).1
  simp only [Category.assoc]
  exact he'.trans he.symm

/-- The unit reduction fixed by the actual coefficient map.
Source: Cartier proof, paragraph 5
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def coefficientIso [HasTerminal C] (hn : 1 ≤ n) :=
  Classical.choose (coefficientIso_existsUnique n D hn)

set_option backward.isDefEq.respectTransparency true in
/-- Reduction of a section and the precise derived adjunct formula.
Source: Cartier proof, paragraph 5; Stacks 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: reduce the map s using the quotient universal property; the local formula
sends the residue of k to p(s(k)). Single-object full faithfulness identifies
its derived map with alphaF Lq(s) coefficientIso^-1. Apply the scalar adjunction:
the adjunct is Res(d sbar) eta_Z. Naturality of eta for s and for the extension
boundary, followed by shift compatibility and the Kummer unit equation, gives
s followed by partial_S followed by kappa[1]. The final two comparison maps
identify restriction of H[1][1] with restriction of H[2]. This is exactly the
Kummer connecting image of the extension boundary; it fixes the sign. -/
theorem boundary_adjunct [HasTerminal C] (hn : 1 ≤ n) (P : Presentation (J := J) n)
    (s : integerUnit J ⟶ P.S.X₃) :
    ∃! sbar : residueUnit J n ⟶ P.Q,
      (coefficientUnit J n ≫ (restriction J n).map sbar = s ≫ P.p) ∧
      (DerivedCategory.singleFunctor (Residue J n) 0).map sbar =
        (coefficientIso n D hn).inv ≫
          D.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map s) ≫
          (identifications n D hn P).alphaF.hom ∧
      (sheafScalarDerivedAdjunction (projection J n) D).homEquiv _ _
        ((coefficientIso n D hn).hom ≫
          (DerivedCategory.singleFunctor (Residue J n) 0).map sbar ≫ boundary n D hn P) =
        (DerivedCategory.singleFunctor (Integral J) 0).map s ≫ P.exact.singleδ ≫
          (kappa n P)⟦(1 : ℤ)⟧' ≫
          ((derivedRestriction n).commShiftIso (1 : ℤ)).inv.app
            (((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)⟦(1 : ℤ)⟧) ≫
          (derivedRestriction n).map
            ((shiftFunctorAdd (DerivedCategory (Residue J n)) (1 : ℤ) 1).inv.app
              ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)) := by
  classical
  let F := DerivedCategory.singleFunctor (Integral J) 0
  let G := DerivedCategory.singleFunctor (Residue J n) 0
  let R := derivedRestriction (J := J) n
  let c := (restriction J n).mapDerivedCategorySingleFunctor 0
  let I := identifications n D hn P
  let e := coefficientIso n D hn
  have he : eta n D (integerUnit J) ≫ R.map e.hom ≫ c.hom.app (residueUnit J n) =
      F.map (coefficientUnit J n) :=
    (Classical.choose_spec (coefficientIso_existsUnique n D hn)).1
  let b := e.inv ≫ D.T.map (F.map s) ≫ I.alphaF.hom
  let sbar := G.preimage b
  have hb : G.map sbar = b := G.map_preimage b
  refine ⟨sbar, ⟨?_, hb, ?_⟩, ?_⟩
  · apply F.map_injective
    simp only [Functor.map_comp]
    rw [← he]
    simp only [Category.assoc]
    have hc : R.map (G.map sbar) ≫ c.hom.app P.Q =
        c.hom.app (residueUnit J n) ≫ F.map ((restriction J n).map sbar) :=
      c.hom.naturality sbar
    rw [← hc, ← R.map_comp_assoc, hb]
    change eta n D (integerUnit J) ≫
      R.map (e.hom ≫ (e.inv ≫ D.T.map (F.map s) ≫ I.alphaF.hom)) ≫ c.hom.app P.Q = _
    simp only [Iso.hom_inv_id_assoc, Functor.map_comp, Category.assoc]
    rw [← Category.assoc (eta n D (integerUnit J)),
      show eta n D (integerUnit J) ≫ R.map (D.T.map (F.map s)) =
        F.map s ≫ eta n D P.S.X₃ from
          ((sheafScalarDerivedAdjunction (projection J n) D).unit.naturality
            (F.map s)).symm]
    simp only [Category.assoc]
    exact congrArg (fun z ↦ F.map s ≫ z) I.quotient_unit
  · let ad := sheafScalarDerivedAdjunction (projection J n) D
    have : ad.CommShift ℤ := ad.commShift_of_rightAdjoint ℤ
    have hinput : e.hom ≫ G.map sbar ≫ boundary n D hn P =
        D.T.map (F.map s ≫ P.exact.singleδ) ≫
          (D.T.commShiftIso (1 : ℤ)).hom.app (F.obj P.S.X₁) ≫
          I.alphaB.hom⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory (Residue J n)) (1 : ℤ) 1).inv.app
            (G.obj P.H) := by
      rw [hb]
      change e.hom ≫ (e.inv ≫ D.T.map (F.map s) ≫ I.alphaF.hom) ≫
        (I.alphaF.inv ≫ D.T.map P.exact.singleδ ≫ _ ≫ _ ≫ _) = _
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
      rfl
    rw [hinput]
    simpa only [Category.assoc] using!
      shifted_boundary_adjunct D.T R ad (F.map s ≫ P.exact.singleδ)
        I.alphaB.hom (kappa n P) I.kummer_unit
  · intro t ht
    apply G.map_injective
    exact ht.2.1.trans hb.symm

set_option backward.isDefEq.respectTransparency true in
/-- Naturality for every morphism of the short exact extensions, with the maps
on torsion and quotient specified by their kernel and cokernel squares.
Source: Cartier proof, paragraphs 4 and 5
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: apply the scalar adjunction's injective hom equivalence to each
identification square. Naturality of its unit, the quotient normalization and
the given quotient square prove the first. The Kummer normalization reduces
the second to naturality of singleTriangle.map for the Kummer sequences.
Naturality of singleTriangle.map for the extensions then gives the boundary
square after functoriality of Lq, its shift comparison, and [1][1] = [2]. -/
theorem boundary_natural [HasTerminal C] (hn : 1 ≤ n)
    (P P' : Presentation (J := J) n) (f : P.S ⟶ P'.S)
    (h : P.H ⟶ P'.H) (q : P.Q ⟶ P'.Q)
    (hi : (restriction J n).map h ≫ P'.i = P.i ≫ f.τ₁)
    (hp : f.τ₃ ≫ P'.p = P.p ≫ (restriction J n).map q) :
    D.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map f.τ₃) ≫
        (identifications n D hn P').alphaF.hom =
      (identifications n D hn P).alphaF.hom ≫
        (DerivedCategory.singleFunctor (Residue J n) 0).map q ∧
    D.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map f.τ₁) ≫
        (identifications n D hn P').alphaB.hom =
      (identifications n D hn P).alphaB.hom ≫
        ((DerivedCategory.singleFunctor (Residue J n) 0).map h)⟦(1 : ℤ)⟧' ∧
    (DerivedCategory.singleFunctor (Residue J n) 0).map q ≫ boundary n D hn P' =
      boundary n D hn P ≫
        ((DerivedCategory.singleFunctor (Residue J n) 0).map h)⟦(2 : ℤ)⟧' := by
  simpa only [generic_boundary, boundary] using!
    normalized_boundary_natural (restriction J n) D.T
      (sheafScalarDerivedAdjunction (projection J n) D) n P P'
      (identifications n D hn P) (identifications n D hn P') f h q hi hp

section InverseImage

variable {C' : Type u'} [Category.{v'} C'] [EssentiallySmall.{r} C']
  {K : GrothendieckTopology C'}
  [HasSheafify K CommRingCat.{r}]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
  [HasDerivedCategory.{wZ'} (Integral K)] [HasDerivedCategory.{wR'} (Residue K n)]
  (D' : DerivedChangeOfRingsCochainModel (projection K n))
  (UZ : Integral J ⥤ Integral K) (UR : Residue J n ⥤ Residue K n)
  [UZ.Additive] [PreservesFiniteLimits UZ] [PreservesFiniteColimits UZ]
  [UR.Additive] [PreservesFiniteLimits UR] [PreservesFiniteColimits UR]

private theorem inverse_comparison [NeZero n]
    (rho : restriction J n ⋙ UZ ≅ UR ⋙ restriction K n) :
    ∃ e : D.E ⋙ UR ≅ UZ ⋙ D'.E,
      (∀ A, UZ.map ((sheafScalarOrdinaryAdjunction (projection J n) D).unit.app A) ≫
        rho.hom.app (D.E.obj A) ≫ (restriction K n).map (e.hom.app A) =
        (sheafScalarOrdinaryAdjunction (projection K n) D').unit.app (UZ.obj A)) ∧
      ∃ theta : D.T ⋙ UR.mapDerivedCategory ≅ UZ.mapDerivedCategory ⋙ D'.T,
        NatTrans.CommShift theta.hom ℤ ∧
        (∀ X, (sheafScalarDerivedAdjunction (projection K n) D').unit.app
            (UZ.mapDerivedCategory.obj X) ≫
          (restriction K n).mapDerivedCategory.map (theta.inv.app X) =
          UZ.mapDerivedCategory.map
            ((sheafScalarDerivedAdjunction (projection J n) D).unit.app X) ≫
          (CategoryTheory.Functor.mapDerivedCategorySquareIso rho).hom.app (D.T.obj X)) ∧
        ∀ P : CochainComplex (Integral J) ℤ,
          theta.hom.app (DerivedCategory.Q.obj P) ≫
            D'.T.map (UZ.mapDerivedCategoryFactors.hom.app P) ≫
            D'.ε.app ((UZ.mapHomologicalComplex (.up ℤ)).obj P) =
          UR.mapDerivedCategory.map (D.ε.app P) ≫
            UR.mapDerivedCategoryFactors.hom.app ((D.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  have : (sheafScalarDerivedAdjunction (projection J n) D).CommShift ℤ :=
    Adjunction.commShift_of_rightAdjoint _ ℤ
  have : (sheafScalarDerivedAdjunction (projection K n) D').CommShift ℤ :=
    Adjunction.commShift_of_rightAdjoint _ ℤ
  let H : CochainComplex (Integral J) ℤ → Prop := fun P ↦
    CochainComplex.IsKFlatIndependentCoefficients (R := integers J) P ∧
      ∀ i : ℤ, Mono (n • 𝟙 (P.X i))
  let H' : CochainComplex (Integral K) ℤ → Prop := fun P ↦
    CochainComplex.IsKFlatIndependentCoefficients (R := integers K) P ∧
      ∀ i : ℤ, Mono (n • 𝟙 (P.X i))
  apply CategoryTheory.derivedCokernelAdjointExchange n D.E D'.E
    (restriction J n) (restriction K n)
    (sheafScalarOrdinaryAdjunction (projection J n) D)
    (sheafScalarOrdinaryAdjunction (projection K n) D') D.T D'.T
    (sheafScalarDerivedAdjunction (projection J n) D)
    (sheafScalarDerivedAdjunction (projection K n) D') D.ε D'.ε UZ UR rho
    (ordinaryUnit_zero n D.E _) (ordinaryUnit_zero n D'.E _)
    (ordinaryUnit_cokernel n D.E _) (ordinaryUnit_cokernel n D'.E _) H H'
  · intro A
    obtain ⟨P, p, hP, hm, hp⟩ := multiplication_resolving n A
    exact ⟨P, p, ⟨hP, hm⟩, hp⟩
  · intro A
    obtain ⟨P, p, hP, hm, hp⟩ := multiplication_resolving n A
    exact ⟨P, p, ⟨hP, hm⟩, hp⟩
  · exact fun _ h ↦ h.2
  · exact fun _ h ↦ h.2
  · exact fun P h ↦ D.computes P h.1
  · exact fun P h ↦ D'.computes P h.1
  · exact fun P h ↦ scalar_derived_unit (projection J n) D P h.1
  · exact fun P h ↦ scalar_derived_unit (projection K n) D' P h.1

-- The original interface includes lift witnesses; exact lifts suffice for this proof.
set_option linter.unusedVariables false in
/-- Compatibility with every exact inverse image of a geometric morphism.
The natural isomorphisms eZ and eR say that UZ and UR are its lifts to the two
constant-coefficient module categories. The comparison rho identifies their
restrictions, hence includes the induced constant-ring identification. Neither
a tensor comparison nor a derived comparison is assumed: both are conclusions.
Source: Cartier proof, paragraphs 4 and 5; Stacks 06YY, 0G7E, 07A4 and 0152
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: inverse image preserves coproducts and the terminal object, hence constant
rings. Transporting addition and the constant scalar action gives UZ and UR.
Their ordinary scalar comparison e is fixed by the ordinary unit equation below.
Both ordinary units are cokernels of multiplication by n; exactness therefore
makes their mate invertible. For the derived mate, it suffices to compute on
flat-term K-flat resolutions. Their image has termwise monic n; comparing the
two multiplication short exact sequences shows that the target universal
counit computes there too. Thus the derived mate is invertible and gives theta
and its representative formula. The mate of the shift-compatible right square
commutes with shifts.
Exactness preserves kernels, cokernels and the multiplication sequences.
It preserves the canonical boundary -p q^-1: it sends the cone differential,
projection p and quasi-isomorphism q to those of the pulled-back sequence.
The mate-unit equation and the quotient-unit normalization give the alphaF
square by adjunction. The alphaB square follows in the same way from the
Kummer-unit normalization and naturality of the canonical single triangle.
Composition in shifted Hom then gives the degree-two boundary square.
The unit formula and naturality
of the scalar adjunction then transport boundary_adjunct as well, including the
identity inverse image and arbitrary coefficient presentations. -/
theorem inverse_image_natural [HasTerminal C] [HasTerminal C'] (hn : 1 ≤ n)
    (U : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (V : Sheaf K (Type r) ⥤ Sheaf J (Type r))
    (adj : U ⊣ V) [PreservesFiniteLimits U]
    (eZ : UZ ⋙ (toSheaf (derivedChangeRingIndependentCoefficients K (integers K)) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{r})) ≅
      (toSheaf (derivedChangeRingIndependentCoefficients J (integers J)) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})) ⋙ U)
    (eR : UR ⋙ (toSheaf (derivedChangeRingIndependentCoefficients K (residues K n)) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{r})) ≅
      (toSheaf (derivedChangeRingIndependentCoefficients J (residues J n)) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})) ⋙ U)
    (rho : restriction J n ⋙ UZ ≅ UR ⋙ restriction K n) :
    ∃ e : D.E ⋙ UR ≅ UZ ⋙ D'.E,
      (∀ A : Integral J,
        UZ.map ((sheafScalarOrdinaryAdjunction (projection J n) D).unit.app A) ≫
          rho.hom.app (D.E.obj A) ≫ (restriction K n).map (e.hom.app A) =
        (sheafScalarOrdinaryAdjunction (projection K n) D').unit.app (UZ.obj A)) ∧
      ∃ theta : D.T ⋙ UR.mapDerivedCategory ≅ UZ.mapDerivedCategory ⋙ D'.T,
        NatTrans.CommShift theta.hom ℤ ∧
        (∀ P : CochainComplex (Integral J) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := integers J) P →
          theta.hom.app (DerivedCategory.Q.obj P) ≫
            D'.T.map (UZ.mapDerivedCategoryFactors.hom.app P) ≫
            D'.ε.app ((UZ.mapHomologicalComplex (.up ℤ)).obj P) =
          UR.mapDerivedCategory.map (D.ε.app P) ≫
            UR.mapDerivedCategoryFactors.hom.app ((D.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) ∧
        ∀ (P : Presentation (J := J) n) (P' : Presentation (J := K) n)
          (f : P'.S ≅ UZ.mapShortComplex.obj P.S)
          (h : P'.H ≅ UR.obj P.H) (q : P'.Q ≅ UR.obj P.Q),
          P'.i ≫ f.hom.τ₁ = (restriction K n).map h.hom ≫
            rho.inv.app P.H ≫ UZ.map P.i →
          f.hom.τ₃ ≫ UZ.map P.p = P'.p ≫ (restriction K n).map q.hom ≫
            rho.inv.app P.Q →
          (UR.mapDerivedCategory.map (identifications n D hn P).alphaF.hom ≫
            (UR.mapDerivedCategorySingleFunctor 0).hom.app P.Q =
          theta.hom.app ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₃) ≫
            D'.T.map ((UZ.mapDerivedCategorySingleFunctor 0).hom.app P.S.X₃) ≫
            D'.T.map ((DerivedCategory.singleFunctor (Integral K) 0).map f.inv.τ₃) ≫
            (identifications n D' hn P').alphaF.hom ≫
            (DerivedCategory.singleFunctor (Residue K n) 0).map q.hom) ∧
          (UR.mapDerivedCategory.map (identifications n D hn P).alphaB.hom ≫
            (UR.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
              ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H) ≫
            ((UR.mapDerivedCategorySingleFunctor 0).hom.app P.H)⟦(1 : ℤ)⟧' =
          theta.hom.app ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₁) ≫
            D'.T.map ((UZ.mapDerivedCategorySingleFunctor 0).hom.app P.S.X₁) ≫
            D'.T.map ((DerivedCategory.singleFunctor (Integral K) 0).map f.inv.τ₁) ≫
            (identifications n D' hn P').alphaB.hom ≫
            ((DerivedCategory.singleFunctor (Residue K n) 0).map h.hom)⟦(1 : ℤ)⟧') ∧
          (UR.mapDerivedCategory.map (boundary n D hn P) ≫
            (UR.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
              ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H) ≫
            ((UR.mapDerivedCategorySingleFunctor 0).hom.app P.H)⟦(2 : ℤ)⟧' =
          (UR.mapDerivedCategorySingleFunctor 0).hom.app P.Q ≫
            (DerivedCategory.singleFunctor (Residue K n) 0).map q.inv ≫
            boundary n D' hn P' ≫
            ((DerivedCategory.singleFunctor (Residue K n) 0).map h.hom)⟦(2 : ℤ)⟧') := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨e, he, theta, hshift, htheta, hrep⟩ := inverse_comparison n D D' UZ UR rho
  have : NatTrans.CommShift theta.hom ℤ := hshift
  refine ⟨e, he, theta, hshift, (fun P _ ↦ hrep P), ?_⟩
  intro P P' f h q hi hp
  have hc := CategoryTheory.normalizedScalarBoundaryNaturality
    (restriction J n) UZ UR (restriction K n) rho D.T D'.T
    (sheafScalarDerivedAdjunction (projection J n) D)
    (sheafScalarDerivedAdjunction (projection K n) D') theta htheta n
    P.S P'.S P.exact P'.exact P.H P.Q P'.H P'.Q P.i P'.i P.wi P'.wi
    P.kummer P'.kummer P.p P'.p
    (identifications n D hn P).alphaF (identifications n D' hn P').alphaF
    (identifications n D hn P).alphaB (identifications n D' hn P').alphaB
    (identifications n D hn P).quotient_unit
    (identifications n D' hn P').quotient_unit
    (identifications n D hn P).kummer_unit
    (identifications n D' hn P').kummer_unit f h q hi hp
  refine ⟨hc.1, hc.2.1, ?_⟩
  simpa only [boundary, shifted_comp_one_one, ShiftedHom.map, Category.assoc] using hc.2.2


end InverseImage

end DivisibleReduction
end SheafOfModules
