/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
import all WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # The direct algebraic-closure coefficient fibre at a geometric point

Source: latest blueprint, def-weil-finite-coefficient-point, fourth displayed functor.
(blueprint: def-weil-direct-qbar-point-fibre).

The functor is the restriction of the specified derived evaluation functor. Its
ordinary coefficient ring is identified by singleton evaluation. Boundedness and
finite-dimensionality are proved before restricting; no equivalence data is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedGeometricPoint

namespace WeilConjectures

/-- The actual coefficient-ring identification, normalized by singleton evaluation.
Source: latest blueprint, def-weil-finite-coefficient-point, Lambda(*) = Qbar_ell
(blueprint: def-weil-direct-qbar-point-fibre). -/
def pointQbarScalarCoordinates_condensed (ℓ : ℕ) [Fact ℓ.Prime] :
    ULift.{u + 1} (PadicAlgCl ℓ) ≃+*
      condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ) := by
  have : Subsingleton (⊤_ Profinite.{u}) := by
    constructor
    intro x y
    let c : (⊤_ Profinite.{u}) ⟶ (⊤_ Profinite.{u}) :=
      ConcreteCategory.ofHom ⟨fun _ ↦ x, continuous_const⟩
    exact ConcreteCategory.congr_hom (terminalIsTerminal.hom_ext c (𝟙 _)) y
  let R := Profinite.padicAlgClCondensedRing.{u} ℓ
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  have hm : (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).monObjObj Λ =
      R.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj Λ.obj := R.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul Λ
  let e : condensedScalarRing Λ ≃+* R.obj.obj (op (⊤_ Profinite.{u})) :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_mul' := by
        intro a b
        change (((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).monObjObj
          Λ).mul.app (op (⊤_ Profinite.{u}))).hom (a ⊗ₜ[ℤ] b) = _
        have h := congrArg (fun m : MonObj Λ.obj ↦ m.mul) hm
        rw [h]
        rfl }
  let v : R.obj.obj (op (⊤_ Profinite.{u})) ≃+* PadicAlgCl ℓ :=
    { toFun := fun f ↦ f.down.val coefficientPoint
      invFun := Profinite.PadicAlgCl.constSectionRingHom ℓ (op (⊤_ Profinite.{u}))
      left_inv := fun f ↦ by
        apply ULift.ext
        apply Subtype.ext
        apply ContinuousMap.ext
        intro x
        exact congrArg f.down.val (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  exact ((e.trans v).trans ULift.ringEquiv.symm).symm

private theorem pointHeartFinite
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {R : Type (u + 1)} [CommRing R]
    (e : R ≃+* condensedScalarRing Λ) (k : Type u) [Field k] [IsAlgClosed k]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ (Spec (.of k))) M) :
    Module.Finite R ((heartFiber Λ k ⋙ ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let t := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let S := CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
    (⊤_ Profinite.{u}) ⋙ ModuleCat.restrictScalars e.toRingHom
  have hfp := CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject
    Λ (Field.toIsField k) IsField.isSepClosed_toField hM (𝟙 _)
  have hfp' := hfp.of_iso ((CondensedRing.upperStarId Λ _).app M)
  let r : t.functor.obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ (Spec (.of k))) :=
    Mod.isoMk (Iso.refl _) (by simp)
  let r' : t.inverse.obj (Mod.regular (condensedRingObj Λ (Spec (.of k)))) ≅
      Mod.regular Λ :=
    t.inverse.mapIso r.symm ≪≫ (t.unitIso.app (Mod.regular Λ)).symm
  let := Functor.additive_of_preserves_binary_products t.inverse
  have hp := hfp'.map t.inverse r'
  obtain ⟨n, m, f, ⟨ef⟩⟩ := hp
  let p : R →ₗ[R] S.obj (Mod.regular Λ) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a b ↦ e.map_mul a b }
  have : Module.Finite R (S.obj (Mod.regular Λ)) :=
    Module.Finite.of_surjective p e.surjective
  let b := S.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    ModuleCat.biproductIsoPi (fun _ : Fin n ↦ S.obj (Mod.regular Λ))
  have : Module.Finite R (S.obj (Mod.finiteFree Λ n)) :=
    Module.Finite.equiv b.toLinearEquiv.symm
  have : Module.Finite R (cokernel (S.map f) : ModuleCat R) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient (S.map f)).toLinearEquiv.symm
  exact Module.Finite.equiv (S.mapIso ef ≪≫ PreservesCokernel.iso S f).toLinearEquiv.symm

/-- The specified direct point fibre has bounded finite-dimensional cohomology.
Source: latest blueprint, def-weil-finite-coefficient-point, fourth displayed functor
(blueprint: def-weil-direct-qbar-point-fibre).

Proof: the exact heart evaluation takes a constructible module to a finite module:
pull its finite presentation back to the condensed point and evaluate the resulting
cokernel of finite free modules. Singleton evaluation makes the regular module cyclic
over the identified ordinary field. The exact derived homology comparison then gives
finite-dimensional homology in every degree and preserves bounded support.
-/
theorem pointQbarFibre_mem_condensed (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (K : BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (Spec (.of D.k)))) :
    DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
      ((ordinaryPointFiber (Profinite.padicAlgClRingObj.{u} ℓ) D.k
        (pointQbarScalarCoordinates_condensed ℓ)).obj K.obj) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let e := pointQbarScalarCoordinates_condensed.{u} ℓ
  let H := heartFiber Λ D.k ⋙ ModuleCat.restrictScalars e.toRingHom
  let d : H.mapDerivedCategory ≅ ordinaryPointFiber Λ D.k e :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.isoWhiskerRight (heartFiberDerivedIso Λ D.k) _
  have hb := H.bounded_mapDerivedCategory_obj K.property.1
  refine ⟨(finite_support_iff_bounded _).mpr
    (DerivedCategory.TStructure.t.bounded.prop_of_iso (d.app K.obj) hb), fun i ↦ ?_⟩
  have hfin : Module.Finite (ULift.{u + 1} (PadicAlgCl ℓ))
      (H.obj ((DerivedCategory.homologyFunctor _ i).obj K.obj)) :=
    pointHeartFinite Λ e D.k _ (K.property.2 i)
  let c := (H.mapDerivedCategoryHomologyFunctorIso i).app K.obj ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso (d.app K.obj)
  exact @Module.Finite.equiv _ _ _ _ _ _ _ _ hfin c.toLinearEquiv

/-- The direct fourth point fibre, restricted to intrinsic bounded constructible objects.
All data is ordinary derived evaluation and singleton scalar restriction; the preceding
membership theorem supplies only the proof needed to restrict the target.
Source: latest blueprint, def-weil-finite-coefficient-point, fourth displayed functor
(blueprint: def-weil-direct-qbar-point-fibre). -/
def pointQbarFibre_condensed (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p) :
    BoundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (Spec (.of D.k))) ⥤
      (DerivedCategory.pointFiniteDimensional
        (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory :=
  (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).lift
    ((boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (Spec (.of D.k)))).ι ⋙
      ordinaryPointFiber (Profinite.padicAlgClRingObj.{u} ℓ) D.k
        (pointQbarScalarCoordinates_condensed ℓ)) (pointQbarFibre_mem_condensed D ℓ)

/-- This is the unique restriction of the specified direct ordinary point fibre.
Source: latest blueprint, def-weil-finite-coefficient-point, evaluation functor
(blueprint: def-weil-direct-qbar-point-fibre).

Proof: the constructed full-subcategory lift has exactly the specified underlying
functor. Equality after the inclusion determines its objects and all its morphisms,
since full-subcategory objects have only proof-valued extra data and the inclusion
is faithful. Thus the restricted functor is unique.
-/
theorem pointQbarFibre_existsUnique_condensed
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p) :
    ∃! F : BoundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (Spec (.of D.k))) ⥤
      (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory,
      F ⋙ (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).ι =
        (boundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) (Spec (.of D.k)))).ι ⋙
          ordinaryPointFiber (Profinite.padicAlgClRingObj.{u} ℓ) D.k
            (pointQbarScalarCoordinates_condensed ℓ) := by
  refine ⟨pointQbarFibre_condensed D ℓ hℓ, rfl, ?_⟩
  intro F hF
  refine CategoryTheory.Functor.ext
    (fun K ↦ ObjectProperty.FullSubcategory.ext (CategoryTheory.Functor.congr_obj hF K)) ?_
  intro A B f
  apply (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).ι.map_injective
  simpa only [CategoryTheory.Functor.map_comp, eqToHom_map, CategoryTheory.Functor.comp_map,
    pointQbarFibre_condensed, ObjectProperty.ι_obj_lift_map]
    using CategoryTheory.Functor.congr_hom hF f

#print axioms pointQbarFibre_mem_condensed
#print axioms pointQbarFibre_existsUnique_condensed

end WeilConjectures
