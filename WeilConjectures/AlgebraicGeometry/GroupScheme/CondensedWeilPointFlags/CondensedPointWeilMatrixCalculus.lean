/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.CategoryTheory.Preadditive.FinitePowerPivot

/-! # Native finite-free point matrix calculus

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-matrix-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags

private theorem scalar_apply {R : Type*} [CommRing R] {C : Type*} [Category* C]
    (F : C ⥤ ModuleCat R) {X : C} (e : F.obj X ≃ₗ[R] R) (f : X ⟶ X)
    (x : F.obj X) :
    e (F.map f x) = e x * e (F.map f (e.symm 1)) := by
  have hx : x = e x • e.symm 1 := by apply e.injective; simp
  conv_lhs => rw [hx]
  rw [map_smul, e.map_smul]
  rfl

private def scalarHom {R : Type*} [CommRing R] {C : Type*} [Category* C]
    [Preadditive C] (F : C ⥤ ModuleCat R) [F.Additive] {X : C}
    (e : F.obj X ≃ₗ[R] R) : End X →+* R where
  toFun f := e (F.map f (e.symm 1))
  map_zero' := by simp
  map_one' := by simp
  map_add' f g := by simp only [F.map_add, ModuleCat.hom_add, LinearMap.add_apply, e.map_add]
  map_mul' f g := by
    change e (F.map (g ≫ f) (e.symm 1)) = _
    rw [F.map_comp, ModuleCat.comp_apply, scalar_apply]
    exact mul_comm _ _

private def nativeCoordinates (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [IsSepClosed k] : End (𝟙_ (NativeCondensedModule.Modules l (Spec (.of k)))) →+*
      PadicAlgCl l := by
  letI : (NativeCondensedModule.pointSections l k).Additive := by
    unfold NativeCondensedModule.pointSections
    infer_instance
  exact ULift.ringEquiv.toRingHom.comp
    (scalarHom (NativeCondensedModule.pointSections l k)
      (NativeCondensedModule.pointSectionsUnitIso l k).symm.toLinearEquiv)

private theorem nativeCoordinates_apply (l : ℕ) [Fact l.Prime] (k : Type u)
    [Field k] [IsSepClosed k]
    (t : End (𝟙_ (NativeCondensedModule.Modules l (Spec (.of k))))) :
    nativeCoordinates l k t =
      ((NativeCondensedModule.pointSectionsUnitIso l k).inv.hom
        ((NativeCondensedModule.pointSections l k).map t
          (NativeCondensedModule.pointSectionsUnit l k))).down := by
  have hunit : (NativeCondensedModule.pointSectionsUnitIso l k).hom.hom 1 =
      NativeCondensedModule.pointSectionsUnit l k := by
    change (1 : ULift.{u + 1} (PadicAlgCl l)) •
      NativeCondensedModule.pointSectionsUnit l k = _
    exact one_smul _ _
  change ((NativeCondensedModule.pointSectionsUnitIso l k).inv.hom
    ((NativeCondensedModule.pointSections l k).map t
      ((NativeCondensedModule.pointSectionsUnitIso l k).hom.hom 1))).down = _
  rw [hunit]

private theorem nativeCoordinates_bijective (l : ℕ) [Fact l.Prime] (k : Type u)
    [Field k] [IsSepClosed k] : Function.Bijective (nativeCoordinates l k) := by
  have heq : ⇑(nativeCoordinates l k) = fun t ↦
      ((NativeCondensedModule.pointSectionsUnitIso l k).inv.hom t).down := by
    funext t
    rw [nativeCoordinates_apply]
    change ((NativeCondensedModule.pointSectionsUnitIso l k).inv.hom
      (𝟙 _ ≫ t)).down = _
    rw [Category.id_comp]
  rw [heq]
  exact ULift.down_bijective.comp
    (NativeCondensedModule.pointSectionsUnitIso l k).symm.toLinearEquiv.bijective

private def pointCoordinates (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] :
    End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) (pointSpace D))) →+*
      PadicAlgCl l :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (nativeCoordinates l D.k).comp
    (CondensedRing.restrictEnd (Profinite.padicAlgClRingObj l) (pointLift D))

private theorem pointCoordinates_bijective (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] : Function.Bijective (pointCoordinates D l) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : IsIso (pointLift D) := by unfold pointLift; infer_instance
  apply (nativeCoordinates_bijective l D.k).comp
  unfold CondensedRing.restrictEnd
  exact (CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj l)
    (pointLift D)).conjRingEquiv.bijective.comp
      (show Function.Bijective (fun f ↦
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (pointLift D)).map f) from
        (Functor.FullyFaithful.ofFullyFaithful
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (pointLift D))).map_bijective
            _ _)

private theorem matrix_eq_coordinates (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {a b : ℕ} (f : free D l a ⟶ free D l b) :
    matrix D l f = fun i j ↦ pointCoordinates D l (Mod.finFreeEntry f i j) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  ext i j
  exact (nativeCoordinates_apply l D.k _).symm

/-- Native scalar-normalized point matrices are bijective and respect composition and
identity, including empty free powers.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-matrix-calculus).

Proof: sections of the regular module are endomorphisms of that module, and the
unit-section isomorphism identifies these with the scalar field. The evaluation
coordinate is multiplicative because every endomorphism of a rank-one module is
scalar multiplication. Pullback along pointLift is fully faithful, so these coordinates
also identify endomorphisms before pullback. Apply the finite biproduct matrix
equivalence entry by entry. The biproduct resolution of the identity gives the matrix
composition formula, and the inclusion-projection identities give the identity matrix.
Realize a unit matrix and its inverse separately. Injectivity of coordinates and the
composition formula show that their composites are identities, producing the isomorphism. -/
theorem point_matrix_calculus (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] :
    (∀ a b : ℕ, Function.Bijective (matrix D l (a := a) (b := b))) ∧
    (∀ (a b c : ℕ) (f : free D l a ⟶ free D l b) (g : free D l b ⟶ free D l c),
      matrix D l (f ≫ g) = matrix D l g * matrix D l f) ∧
    (∀ a : ℕ, matrix D l (𝟙 (free D l a)) = 1) ∧
    ∀ (a : ℕ) (C : Matrix (Fin a) (Fin a) (PadicAlgCl l)), IsUnit C →
      ∃ e : free D l a ≅ free D l a, matrix D l e.hom = C := by
  classical
  have hbij := pointCoordinates_bijective D l
  have hbijM : ∀ a b : ℕ, Function.Bijective (matrix D l (a := a) (b := b)) := by
    intro a b
    constructor
    · intro f g hfg
      apply Mod.finFree_hom_ext
      intro i j
      apply hbij.1
      have h := congrFun (congrFun hfg i) j
      simpa only [matrix_eq_coordinates] using h
    · intro C
      choose t ht using fun i j ↦ hbij.2 (C i j)
      refine ⟨biproduct.matrix (fun j i ↦ t i j), ?_⟩
      rw [matrix_eq_coordinates]
      ext i j
      change pointCoordinates D l
        (biproduct.components (biproduct.matrix (fun j i ↦ t i j)) j i) = C i j
      rw [biproduct.matrix_components]
      exact ht i j
  have hcompM : ∀ (a b c : ℕ) (f : free D l a ⟶ free D l b)
      (g : free D l b ⟶ free D l c), matrix D l (f ≫ g) = matrix D l g * matrix D l f := by
    intro a b c f g
    simp only [matrix_eq_coordinates]
    change Matrix.map (biproductFinMatrix (f ≫ g)) (pointCoordinates D l) =
      Matrix.map (biproductFinMatrix g) (pointCoordinates D l) *
        Matrix.map (biproductFinMatrix f) (pointCoordinates D l)
    rw [biproductFinMatrix_comp, Matrix.map_mul]
  have hidM : ∀ a : ℕ, matrix D l (𝟙 (free D l a)) = 1 := by
    intro a
    rw [matrix_eq_coordinates]
    change Matrix.map (biproductFinMatrix (𝟙 (free D l a))) (pointCoordinates D l) = 1
    rw [biproductFinMatrix_id]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨hbijM, hcompM, hidM, ?_⟩
  intro a C hC
  obtain ⟨U, rfl⟩ := hC
  obtain ⟨f, hf⟩ := (hbijM a a).2 (U : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  obtain ⟨g, hg⟩ := (hbijM a a).2 (↑U⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (hbijM a a).1
    rw [hcompM, hf, hg, hidM]
    exact U.inv_val
  · apply (hbijM a a).1
    rw [hcompM, hf, hg, hidM]
    exact U.val_inv

end WeilConjectures.CondensedWeilPointFlags
