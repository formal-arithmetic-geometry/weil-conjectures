/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives

/-!
# Products in the derived category

Let `C` be an abelian category with products of shape `J` in which every cochain complex
admits a quasi-isomorphism to a K-injective complex (for instance a Grothendieck abelian
category). Then the derived category `D(C)` has products of shape `J`: the product of a
family `X` is the degreewise product of K-injective complexes representing the `X j`.

## Main results

- `HomologicalComplex.homotopyOfPi`: two maps to a product of complexes are homotopic
  if their components are.
- `CochainComplex.isKInjective_pi`: a product of K-injective complexes is K-injective.
- `DerivedCategory.hasProductsOfShape`: `D(C)` has products of shape `J`.

-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {J : Type*} (I : J → HomologicalComplex C c) [HasProduct I]
  [∀ i, PreservesLimit (Discrete.functor I) (eval C c i)]

/-- In each degree, a product of complexes is the product of the terms. -/
noncomputable def isLimitPiEval (i : ι) :
    IsLimit (Fan.mk ((∏ᶜ I).X i) fun j ↦ (Pi.π I j).f i : Fan fun j ↦ (I j).X i) :=
  isLimitFanMkObjOfIsLimit (eval C c i) I (Pi.π I) (productIsProduct I)

variable {I}

/-- A family of maps `X ⟶ (I j).X i`, as a map to the degree `i` term of the product. -/
noncomputable def liftPiX {X : C} {i : ι} (φ : ∀ j, X ⟶ (I j).X i) : X ⟶ (∏ᶜ I).X i :=
  Fan.IsLimit.lift (isLimitPiEval I i) φ

@[reassoc (attr := simp)]
lemma liftPiX_π {X : C} {i : ι} (φ : ∀ j, X ⟶ (I j).X i) (j : J) :
    liftPiX φ ≫ (Pi.π I j).f i = φ j :=
  Fan.IsLimit.fac (isLimitPiEval I i) φ j

lemma liftPiX_ext {X : C} {i : ι} {a b : X ⟶ (∏ᶜ I).X i}
    (h : ∀ j, a ≫ (Pi.π I j).f i = b ≫ (Pi.π I j).f i) : a = b :=
  Fan.IsLimit.hom_ext (isLimitPiEval I i) _ _ h

/-- Two maps to a product of complexes are homotopic if their components are. -/
noncomputable def homotopyOfPi {K : HomologicalComplex C c} {f g : K ⟶ ∏ᶜ I}
    (h : ∀ j, Homotopy (f ≫ Pi.π I j) (g ≫ Pi.π I j)) : Homotopy f g where
  hom i i' := liftPiX fun j ↦ (h j).hom i i'
  zero i i' hii' := liftPiX_ext fun j ↦ by simp [(h j).zero i i' hii']
  comm i := liftPiX_ext fun j ↦ by
    have := (h j).comm i
    simp only [comp_f, dNext, prevD, AddMonoidHom.mk'_apply] at this
    simp only [dNext, prevD, AddMonoidHom.mk'_apply, Preadditive.add_comp, assoc, liftPiX_π,
      ← Hom.comm, liftPiX_π_assoc]
    exact this

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A product of K-injective cochain complexes is K-injective. -/
lemma isKInjective_pi {J : Type*} (I : J → CochainComplex C ℤ) [HasProduct I]
    [∀ i, PreservesLimit (Discrete.functor I) (HomologicalComplex.eval C (.up ℤ) i)]
    [∀ j, (I j).IsKInjective] : (∏ᶜ I).IsKInjective where
  nonempty_homotopy_zero {K} f hK := ⟨HomologicalComplex.homotopyOfPi fun j ↦
    (IsKInjective.homotopyZero (f ≫ Pi.π I j) hK).trans (.ofEq (by simp))⟩

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

lemma Q_map_surjective_of_isKInjective (K L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Surjective (Q.map : (K ⟶ L) → (Q.obj K ⟶ Q.obj L)) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) L).surjective
      ((quotientCompQhIso C).hom.app K ≫ φ ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective ψ
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((quotientCompQhIso C).hom.app K), ← quotientCompQhIso_hom_naturality, hψ]
  simp

lemma nonempty_homotopy_of_Q_map_eq {K L : CochainComplex C ℤ} [L.IsKInjective] {g g' : K ⟶ L}
    (h : Q.map g = Q.map g') : Nonempty (Homotopy g g') := by
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ((CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) L).injective ?_)⟩
  rw [← cancel_mono ((quotientCompQhIso C).hom.app L), quotientCompQhIso_hom_naturality,
    quotientCompQhIso_hom_naturality, h]

variable [Abelian.HasKInjectiveResolutions C]

/-- In an abelian category with products of shape `J` and K-injective resolutions, products of
shape `J` exist in the derived category: they are the degreewise products of K-injective
representatives. -/
lemma hasProduct {J : Type*} [HasProductsOfShape J C] (X : J → DerivedCategory C) :
    HasProduct X := by
  have := Localization.essSurj (Q (C := C)) (HomologicalComplex.quasiIso C (.up ℤ))
  choose L hL i hi using fun j ↦
    Abelian.HasKInjectiveResolutions.exists_isKInjective (Q.objPreimage (X j))
  have hQi (j : J) : IsIso (Q.map (i j)) :=
    Localization.inverts Q (HomologicalComplex.quasiIso C (.up ℤ)) _
      (by rw [HomologicalComplex.mem_quasiIso_iff]; exact (hi j).2)
  let e (j : J) : Q.obj (L j) ≅ X j :=
    (asIso (Q.map (i j))).symm ≪≫ Q.objObjPreimageIso (X j)
  have := hL
  have : (∏ᶜ L).IsKInjective := CochainComplex.isKInjective_pi L
  let lift (s : Fan X) : s.pt ⟶ Q.obj (∏ᶜ L) :=
    (Q.objObjPreimageIso s.pt).inv ≫ Q.map (Pi.lift fun j ↦
      (Q_map_surjective_of_isKInjective _ _
        ((Q.objObjPreimageIso s.pt).hom ≫ s.proj j ≫ (e j).inv)).choose)
  have hlift (s : Fan X) (j : J) : lift s ≫ Q.map (Pi.π L j) ≫ (e j).hom = s.proj j := by
    simp only [lift, assoc, ← Functor.map_comp_assoc, limit.lift_π, Fan.mk_π_app]
    rw [(Q_map_surjective_of_isKInjective _ _ _).choose_spec]
    simp
  refine ⟨⟨⟨Fan.mk (Q.obj (∏ᶜ L)) fun j ↦ Q.map (Pi.π L j) ≫ (e j).hom,
    Fan.IsLimit.mk _ lift (fun s j ↦ hlift s j) fun s m hm ↦ ?_⟩⟩⟩
  obtain ⟨g', hg'⟩ := Q_map_surjective_of_isKInjective _ _ ((Q.objObjPreimageIso s.pt).hom ≫ m)
  rw [← cancel_epi (Q.objObjPreimageIso s.pt).hom, ← hg']
  simp only [lift, Iso.hom_inv_id_assoc]
  refine Q_map_eq_of_homotopy (C := C) (HomologicalComplex.homotopyOfPi fun j ↦
    (nonempty_homotopy_of_Q_map_eq ?_).some)
  rw [Functor.map_comp, Functor.map_comp, hg', ← Functor.map_comp Q (Pi.lift _) (Pi.π _ j),
    Pi.lift_π, (Q_map_surjective_of_isKInjective _ _ _).choose_spec, ← cancel_mono (e j).hom]
  simp only [assoc, Iso.inv_hom_id, comp_id]
  exact congrArg _ (hm j)

instance hasProductsOfShape (J : Type*) [HasProductsOfShape J C] :
    HasProductsOfShape J (DerivedCategory C) :=
  ⟨fun F ↦ by
    have : HasProduct (F.obj ∘ Discrete.mk) := hasProduct _
    exact hasLimit_of_iso (Discrete.natIsoFunctor (F := F)).symm⟩

end DerivedCategory
