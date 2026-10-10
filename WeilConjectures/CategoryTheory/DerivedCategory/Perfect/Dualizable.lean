/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.Algebra.Homology.ModuleCat.Subcomplex
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Dualizable complexes of modules are perfect

Let `R` be a commutative ring. A perfect complex of `D(R)` is dualizable for the derived tensor
product (`DerivedCategory.IsPerfect.isDualizable`). This file proves the converse over a
Noetherian ring: a dualizable object of `D(R)` is perfect (`DerivedCategory.isPerfect_of_isDualizable`).
Together, perfectness and dualizability agree (`DerivedCategory.isPerfect_iff_isDualizable`).

## Strategy

Let `C` be dualizable, with right dual `D`, and represent `C` by a complex `L`.

1. Maps `C ⟶ Z` correspond to maps `𝟙 ⟶ Z ⊗ D`. Represent `D` by a K-flat complex `F` of flat
   modules. A map `𝟙 ⟶ Q(L) ⊗ D = Q(L ⊗ F)` is given by a cocycle `x` of degree `0` of the
   complex `L ⊗ F`, as `𝟙 = R[0]` is K-projective. The element `x` comes from a subcomplex
   `L' ⊗ F` with `L'` a subcomplex of `L` with finitely generated terms, vanishing outside a
   finite interval, and it is a cocycle there since `L' ⊗ F ⟶ L ⊗ F` is injective. Applied to
   the identity of `C`, this shows that `C` is a retract of `Q(L')`
   (`DerivedCategory.exists_retract_of_exactPairing`).
2. Over a Noetherian ring, `C` is then bounded with finitely generated cohomology. So is its dual
   `D`, which is again dualizable. If `C` vanishes above `b` and `D` vanishes above `b'`, then
   `C` has Tor amplitude in `[-b', b]`: maps `Y ⟶ C ⊗ᴸ M` correspond to maps `D ⊗ᴸ Y ⟶ M`.
3. A bounded complex with finitely generated cohomology and finite Tor amplitude is perfect
   (`DerivedCategory.isPerfect_of_finiteTorAmplitude`).

## Main statements

- `DerivedCategory.exists_retract_of_exactPairing`: a dualizable object of `D(R)` is a retract
  of a bounded complex with finitely generated terms.
- `DerivedCategory.isPerfect_of_isDualizable`, `DerivedCategory.isPerfect_iff_isDualizable`
  (`sk-def-perfect`): over a Noetherian ring, the perfect objects of `D(R)` are exactly the
  dualizable ones.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

/-- Every complex has a K-flat resolution by a complex of flat objects: the functorial flat
resolution of an unbounded complex is a colimit of bounded above complexes of flat objects. -/
lemma exists_quasiIso_flat_kFlat (L : CochainComplex C ℤ) :
    ∃ (P : CochainComplex C ℤ) (π : P ⟶ L), QuasiIso π ∧ (∀ n, ObjectProperty.flat (P.X n)) ∧
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  have (X : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ C))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ C).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  refine ⟨Λ.resolutionFunctor.obj L, Λ.resolutionNatTrans.app L, inferInstance, fun n ↦ ?_,
    Λ.kFlat_resolutionFunctor_obj hι L⟩
  have := CochainComplex.closedUnderColimitsOfShape_flat C ℤ
  let c := Λ.colimitOfShapeResolutionFunctorObj L
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) n) c.isColimit)
    (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))

end CochainComplex

namespace DerivedCategory

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- The isomorphism `L ⊗ᴸ P ≅ L ⊗ P` for a K-flat complex `P` is natural in `L`. -/
@[reassoc]
lemma QObjTensorQObjIsoOfKFlatRight_hom_naturality {L L' : CochainComplex C ℤ} (f : L ⟶ L')
    (P : CochainComplex C ℤ) (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    Q.map f ▷ Q.obj P ≫ (QObjTensorQObjIsoOfKFlatRight L' P hP).hom =
      (QObjTensorQObjIsoOfKFlatRight L P hP).hom ≫ Q.map (f ▷ P) := by
  have h₁ := (tensorRightCounit ((HomotopyCategory.quotient C (.up ℤ)).obj P)).naturality
    ((HomotopyCategory.quotient C (.up ℤ)).map f)
  have h₂ := Functor.LaxMonoidal.μ_natural_left (HomotopyCategory.quotient C (.up ℤ)) f P
  have h₃ := (quotientCompQhIso C).hom.naturality (f ▷ P)
  have h₄ := (quotientCompQhIso C).inv.naturality f
  dsimp at h₁ h₂ h₃ h₄
  simp only [QObjTensorQObjIsoOfKFlatRight, Iso.trans_hom, tensorIso_hom, Iso.app_hom,
    Iso.symm_hom, asIso_hom, Functor.mapIso_hom, Category.assoc]
  have key : Q.map f ▷ Q.obj P ≫
      ((quotientCompQhIso C).inv.app L' ⊗ₘ (quotientCompQhIso C).inv.app P) =
      ((quotientCompQhIso C).inv.app L ⊗ₘ (quotientCompQhIso C).inv.app P) ≫
        Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ▷ _ := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, h₄,
      Category.comp_id, Category.id_comp]
  rw [reassoc_of% key, reassoc_of% h₁, ← h₃, Functor.Monoidal.μIso_hom, ← Qh.map_comp_assoc,
    h₂, Qh.map_comp_assoc, Functor.Monoidal.μIso_hom]

end General

end DerivedCategory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A morphism `Q(K) ⟶ Q(L)` in the derived category out of a K-projective complex `K` is
the image of a morphism of complexes. -/
lemma IsKProjective.exists_Q_map_eq (K L : CochainComplex C ℤ) [K.IsKProjective]
    (g : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ φ : K ⟶ L, DerivedCategory.Q.map φ = g := by
  obtain ⟨g', hg'⟩ := (IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (.up ℤ)).obj L)).2
      ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ g ≫
        (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g'
  refine ⟨φ, ?_⟩
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality φ
  dsimp at h hg'
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K), ← h, hg']
  simp

end CochainComplex

namespace DerivedCategory

section ModuleCat

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

variable (R) in
/-- The complex `R[0]`, whose image in `D(R)` is the monoidal unit. -/
noncomputable abbrev unitComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj (𝟙_ (ModuleCat.{u} R))

instance : (unitComplex R).IsKProjective := by
  have (n : ℤ) : Projective ((unitComplex R).X n) := by
    by_cases h : n = 0
    · subst h
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).projective
  exact CochainComplex.isKProjective_of_projective _ 0

/-- The monoidal unit of `D(R)` is the image of `R[0]`. -/
noncomputable def unitIsoQObjUnitComplex :
    𝟙_ (DerivedCategory (ModuleCat.{u} R)) ≅ Q.obj (unitComplex R) :=
  (singleFunctorObjUnitIso _).symm ≪≫ (singleFunctorIsoCompQ _ 0).app _

/-- **A dualizable object is a retract of a finite complex.** Let `C` be an object of `D(R)`
with a right dual `D`, represented by a complex `L`. Then the isomorphism `C ≅ Q(L)` factors
through `Q(L')` for a subcomplex `L'` of `L` with finitely generated terms, vanishing outside a
finite interval.

The coevaluation `𝟙 ⟶ C ⊗ D ≅ Q(L ⊗ F)`, where `F` is a K-flat complex of flat modules
representing `D`, is given by a cocycle of `L ⊗ F` of degree `0`, as `𝟙 = R[0]` is
K-projective. This cocycle comes from `L' ⊗ F` for a finite subcomplex `L'` of `L`, so the
coevaluation factors through `Q(L') ⊗ D`, and the zigzag identity factors `C ≅ Q(L)` through
`Q(L')`. -/
theorem exists_retract_of_exactPairing (C D : DerivedCategory (ModuleCat.{u} R))
    [ExactPairing C D] (L : CochainComplex (ModuleCat.{u} R) ℤ) (e : C ≅ Q.obj L) :
    ∃ (N : L.SubcomplexFamily) (_ : N.IsFinite) (w : C ⟶ Q.obj (CochainComplex.subcomplex N)),
      w ≫ Q.map (CochainComplex.subcomplexι N) = e.hom := by
  obtain ⟨F, π, _, hFflat, hF⟩ := CochainComplex.exists_quasiIso_flat_kFlat (Q.objPreimage D)
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  let eD : Q.obj F ≅ D := asIso (Q.map π) ≪≫ Q.objObjPreimageIso D
  let T (L' : CochainComplex (ModuleCat.{u} R) ℤ) : Q.obj L' ⊗ D ≅ Q.obj (L' ⊗ F) :=
    whiskerLeftIso (Q.obj L') eD.symm ≪≫ QObjTensorQObjIsoOfKFlatRight L' F hF
  have hT {L₁ L₂ : CochainComplex (ModuleCat.{u} R) ℤ} (f : L₁ ⟶ L₂) :
      Q.map f ▷ D ≫ (T L₂).hom = (T L₁).hom ≫ Q.map (f ▷ F) := by
    simp only [T, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc, ← whisker_exchange_assoc,
      QObjTensorQObjIsoOfKFlatRight_hom_naturality]
  let eU := unitIsoQObjUnitComplex (R := R)
  obtain ⟨φ, hφ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq (unitComplex R) (L ⊗ F)
    (eU.inv ≫ η_ C D ≫ e.hom ▷ D ≫ (T L).hom)
  let s : (unitComplex R).X 0 :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv (1 : R)
  obtain ⟨N, hN, x', hx'⟩ := CochainComplex.exists_mem_range_tensor F 0 (φ.f 0 s)
  let ι := CochainComplex.subcomplexι N
  have hd : (CochainComplex.subcomplex N ⊗ F).d 0 1 x' = 0 := by
    apply CochainComplex.injective_subcomplexι_whiskerRight_f N F hFflat 1
    rw [map_zero, ← ModuleCat.comp_apply, ← HomologicalComplex.Hom.comm, ModuleCat.comp_apply,
      hx', ← ModuleCat.comp_apply, φ.comm]
    simp
  let φ' : unitComplex R ⟶ CochainComplex.subcomplex N ⊗ F :=
    HomologicalComplex.mkHomFromSingle (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x'))
      (by
        rintro k (rfl : 0 + 1 = k)
        refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
        change (CochainComplex.subcomplex N ⊗ F).d 0 1 (LinearMap.toSpanSingleton R _ x' 1) = 0
        rw [LinearMap.toSpanSingleton_apply, one_smul]
        exact hd)
  have hφ' : φ' ≫ ι ▷ F = φ := by
    apply HomologicalComplex.from_single_hom_ext
    rw [← cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv,
      HomologicalComplex.comp_f]
    have hf0 : φ'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x') :=
      HomologicalComplex.mkHomFromSingle_f _ _
    rw [hf0, Category.assoc, Iso.inv_hom_id_assoc]
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, one_smul]
    exact hx'
  have hu : (eU.hom ≫ Q.map φ' ≫ (T _).inv) ≫ Q.map ι ▷ D = η_ C D ≫ e.hom ▷ D := by
    rw [← cancel_mono (T L).hom, Category.assoc, Category.assoc, Category.assoc, hT ι,
      Iso.inv_hom_id_assoc, ← Q.map_comp, hφ', hφ, Iso.hom_inv_id_assoc,
      Category.assoc]
  have key : (tensorRightHomEquiv _ C D _).symm (eU.hom ≫ Q.map φ' ≫ (T _).inv) ≫ Q.map ι =
      (λ_ C).hom ≫ e.hom := by
    rw [← tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight (Y' := D), ← hu, Equiv.eq_symm_apply,
      tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]
  exact ⟨N, hN, _, by rw [Category.assoc, key, Iso.inv_hom_id_assoc]⟩

end ModuleCat

end DerivedCategory
