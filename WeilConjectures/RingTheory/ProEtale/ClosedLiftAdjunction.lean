/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import WeilConjectures.RingTheory.ProEtale.ClosedLift

/-!
# The universal property of the ind-étale closed lift

For an `A`-algebra `C̄`, the lift `H_A(C̄)` of `Algebra.ClosedLift` is the coreflection of `C̄`
into ind-étale `A`-algebras: for every ind-étale `A`-algebra `D`, composition with
`H_A(C̄) ⟶ C̄` is a bijection `Hom_A(D, H_A(C̄)) ≃ Hom_A(D, C̄)`
(`Algebra.ClosedLift.homEquiv`). When `C̄` is an `A ⧸ I`-algebra the target is
`Hom_{A ⧸ I}(D ⧸ I D, C̄)` (`Algebra.ClosedLift.homEquivReduction`, blueprint
`lem-exc-closed-lift-adjunction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Algebra.ClosedLift

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]

/-- Two maps from an étale `A`-algebra to `H_A(C̄)` with the same image in `C̄` agree: both
factor through stages of the filtered colimit, which a further stage equalizes. -/
theorem algHom_ext_of_etale {D : Type u} [CommRing D] [Algebra A D] [Algebra.Etale A D]
    {ψ₁ ψ₂ : D →ₐ[A] ClosedLift A C}
    (h : (toAlgHom A C).comp ψ₁ = (toAlgHom A C).comp ψ₂) : ψ₁ = ψ₂ := by
  have hfp : IsFinitelyPresentable.{u} (CommAlgCat.of A D) :=
    CommAlgCat.finitePresentation_le_isFinitelyPresentable A _
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  obtain ⟨X₁, φ₁, hφ₁⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (colimit.isColimit (diagram A C)) (CommAlgCat.ofHom ψ₁)
  obtain ⟨X₂, φ₂, hφ₂⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (colimit.isColimit (diagram A C)) (CommAlgCat.ofHom ψ₂)
  have h₁ : ∀ d, ι X₁ (φ₁.hom d) = ψ₁ d := fun d ↦ congrArg (fun g ↦ CommAlgCat.Hom.hom g d) hφ₁
  have h₂ : ∀ d, ι X₂ (φ₂.hom d) = ψ₂ d := fun d ↦ congrArg (fun g ↦ CommAlgCat.Hom.hom g d) hφ₂
  let f := (toAlgHom A C).comp ψ₁
  let e := Index.ofEtaleEquiv D f
  let g₁ : Index.ofEtale D f ⟶ X₁ := ⟨φ₁.hom.comp e.toAlgHom, by
    ext y
    simp only [AlgHom.comp_apply, Index.ofEtale_toC_apply]
    rw [← toAlgHom_ι]
    exact congrArg _ (h₁ (e y))⟩
  let g₂ : Index.ofEtale D f ⟶ X₂ := ⟨φ₂.hom.comp e.toAlgHom, by
    ext y
    simp only [AlgHom.comp_apply, Index.ofEtale_toC_apply]
    rw [← toAlgHom_ι]
    exact (congrArg _ (h₂ (e y))).trans (DFunLike.congr_fun h (e y)).symm⟩
  obtain ⟨Z, t₁, t₂, -⟩ := IsFilteredOrEmpty.cocone_objs X₁ X₂
  obtain ⟨Z', q, hq⟩ := IsFilteredOrEmpty.cocone_maps (g₁ ≫ t₁) (g₂ ≫ t₂)
  ext d
  obtain ⟨y, rfl⟩ := e.surjective d
  rw [← h₁, ← h₂, ← ι_hom (t₁ ≫ q), ← ι_hom (t₂ ≫ q)]
  have := congrArg (fun g : Index.ofEtale D f ⟶ Z' ↦ g.hom y) hq
  exact congrArg (ι Z') this

/-- Every `A`-algebra map from an étale `A`-algebra `D` to `C̄` lifts to `H_A(C̄)`: `D` is itself
an object of `N_A(C̄)`. -/
theorem exists_algHom_of_etale (D : Type u) [CommRing D] [Algebra A D] [Algebra.Etale A D]
    (f : D →ₐ[A] C) : ∃ ψ : D →ₐ[A] ClosedLift A C, (toAlgHom A C).comp ψ = f :=
  ⟨(ι (Index.ofEtale D f)).comp (Index.ofEtaleEquiv D f).symm.toAlgHom, by
    ext d
    simp [Index.ofEtale_toC_apply]⟩

/-- For an ind-étale `A`-algebra `D`, composition with `H_A(C̄) ⟶ C̄` is a bijection
`Hom_A(D, H_A(C̄)) → Hom_A(D, C̄)`: apply the étale case on the stages of a filtered colimit
presentation of `D`. -/
theorem bijective_comp_toAlgHom (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D] :
    Function.Bijective (fun ψ : D →ₐ[A] ClosedLift A C ↦ (toAlgHom A C).comp ψ) := by
  obtain ⟨κ, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A) (S := D)
  have hinj : ∀ ψ₁ ψ₂ : D →ₐ[A] ClosedLift A C,
      (toAlgHom A C).comp ψ₁ = (toAlgHom A C).comp ψ₂ → ψ₁ = ψ₂ := by
    intro ψ₁ ψ₂ h
    have : CommAlgCat.ofHom ψ₁ = CommAlgCat.ofHom ψ₂ := by
      refine P.isColimit.hom_ext fun a ↦ ?_
      have : Algebra.Etale A (P.diag.obj a) := hP a
      ext1
      refine algHom_ext_of_etale ?_
      ext x
      exact DFunLike.congr_fun h ((P.ι.app a).hom x)
    exact congrArg CommAlgCat.Hom.hom this
  refine ⟨fun ψ₁ ψ₂ h ↦ hinj ψ₁ ψ₂ h, fun f ↦ ?_⟩
  have hex : ∀ a, ∃ ψ : P.diag.obj a →ₐ[A] ClosedLift A C,
      (toAlgHom A C).comp ψ = f.comp (P.ι.app a).hom := fun a ↦
    have : Algebra.Etale A (P.diag.obj a) := hP a
    exists_algHom_of_etale _ _
  choose ψ hψ using hex
  let c : Cocone P.diag :=
    { pt := CommAlgCat.of A (ClosedLift A C)
      ι :=
        { app a := CommAlgCat.ofHom (ψ a)
          naturality a b g := by
            have : Algebra.Etale A (P.diag.obj a) := hP a
            ext1
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
              CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
            refine algHom_ext_of_etale ?_
            rw [← AlgHom.comp_assoc, hψ, hψ, AlgHom.comp_assoc, ← CommAlgCat.hom_comp, P.w] } }
  refine ⟨(P.isColimit.desc c).hom, ?_⟩
  have : CommAlgCat.ofHom ((toAlgHom A C).comp (P.isColimit.desc c).hom) = CommAlgCat.ofHom f := by
    refine P.isColimit.hom_ext fun a ↦ ?_
    ext1
    have h := P.isColimit.fac c a
    simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
    rw [AlgHom.comp_assoc, ← CommAlgCat.hom_comp, h]
    exact hψ a
  exact congrArg CommAlgCat.Hom.hom this

/-- For an ind-étale `A`-algebra `D`, composition with `H_A(C̄) ⟶ C̄` identifies
`Hom_A(D, H_A(C̄))` with `Hom_A(D, C̄)`. -/
noncomputable def homEquiv (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D] :
    (D →ₐ[A] ClosedLift A C) ≃ (D →ₐ[A] C) :=
  Equiv.ofBijective _ (bijective_comp_toAlgHom D)

@[simp]
lemma homEquiv_apply (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D]
    (ψ : D →ₐ[A] ClosedLift A C) : homEquiv D ψ = (toAlgHom A C).comp ψ :=
  rfl

variable (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]

/-- For an `A ⧸ I`-algebra `C̄`, `A`-algebra maps `D → C̄` are the `A ⧸ I`-algebra maps
`D ⧸ I D → C̄`. -/
noncomputable def quotientHomEquiv (D : Type u) [CommRing D] [Algebra A D] :
    (D →ₐ[A] C) ≃ (D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] C) where
  toFun f := (Ideal.Quotient.liftₐ _ f (fun d hd ↦ by
    have : I.map (algebraMap A D) ≤ RingHom.ker (f : D →+* C) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_coe, AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply A (A ⧸ I) C, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact this hd)).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  invFun g := (g.restrictScalars A).comp (Ideal.Quotient.mkₐ A _)
  left_inv f := by ext; rfl
  right_inv g := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- Blueprint `lem-exc-closed-lift-adjunction` (subsection `sk-prop-sf-open-closed-triangle`): for
every ind-étale `A`-algebra `D`, reduction induces a natural bijection
`Hom_A(D, H_A(C̄)) ≃ Hom_{A ⧸ I}(D ⧸ I D, C̄)`; so `H_A` is right adjoint to reduction on
ind-étale algebras (see also `Algebra.ClosedLift.homEquiv`).

For `D` étale, a map `D ⧸ I D → C̄` makes `D` an object of `N_A(C̄)` and gives its canonical map
to the colimit; any two lifts factor through stages which a further stage equalizes. The general
case follows by passing to the colimit of the étale stages of `D`. -/
noncomputable def homEquivReduction (D : Type u) [CommRing D] [Algebra A D]
    [Algebra.IndEtale A D] :
    (D →ₐ[A] ClosedLift A C) ≃ (D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] C) :=
  (homEquiv D).trans (quotientHomEquiv I D)

lemma homEquivReduction_apply_mk (D : Type u) [CommRing D] [Algebra A D]
    [Algebra.IndEtale A D] (ψ : D →ₐ[A] ClosedLift A C) (d : D) :
    homEquivReduction I D ψ (Ideal.Quotient.mk _ d) = toAlgHom A C (ψ d) :=
  rfl

/-! ### The lift as an adjoint on categories of ind-étale algebras -/

section BaseChange

variable {R : Type u} [CommRing R] [Algebra A R]

/-- For an `R`-algebra `C̄` over `A`, the `R`-algebra maps `R ⊗_A D → C̄` are the `A`-algebra maps
`D → C̄`. -/
noncomputable def baseChangeHomEquiv (D : Type u) [CommRing D] [Algebra A D] (C : Type u)
    [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower A R C] :
    (TensorProduct A R D →ₐ[R] C) ≃ (D →ₐ[A] C) where
  toFun g := (g.restrictScalars A).comp Algebra.TensorProduct.includeRight
  invFun f := Algebra.TensorProduct.lift (Algebra.ofId R C) f (fun _ _ ↦ .all _ _)
  left_inv g := by
    ext x
    simp
  right_inv f := by
    ext x
    simp

lemma baseChangeHomEquiv_apply (D : Type u) [CommRing D] [Algebra A D] (C : Type u)
    [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
    (g : TensorProduct A R D →ₐ[R] C) (d : D) :
    baseChangeHomEquiv D C g d = g (1 ⊗ₜ d) :=
  rfl

end BaseChange

end Algebra.ClosedLift

namespace Algebra

open ClosedLift

variable (A : Type u) [CommRing A]

/-- The category of ind-étale `A`-algebras. Its opposite is the affine ind-étale basis
`B_{Spec A}` of the pro-étale site of `Spec A`. -/
abbrev IndEtaleAlgCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (fun B : CommAlgCat.{u} A ↦ Algebra.IndEtale A B)

namespace IndEtaleAlgCat

instance (D : IndEtaleAlgCat A) : Algebra.IndEtale A D.obj := D.property

variable {A} in
/-- Morphisms of ind-étale algebras are algebra maps. -/
@[simps]
def algHomEquiv {X Y : IndEtaleAlgCat A} : (X ⟶ Y) ≃ (X.obj →ₐ[A] Y.obj) where
  toFun f := f.hom.hom
  invFun φ := ObjectProperty.homMk (CommAlgCat.ofHom φ)
  left_inv _ := rfl
  right_inv _ := rfl

variable (I : Ideal A)

/-- An `A ⧸ I`-algebra, viewed as an `A`-algebra. -/
abbrev algebraOfQuotient (C : CommAlgCat.{u} (A ⧸ I)) : Algebra A C :=
  Algebra.compHom C (algebraMap A (A ⧸ I))

attribute [local instance] algebraOfQuotient

instance (C : CommAlgCat.{u} (A ⧸ I)) : IsScalarTower A (A ⧸ I) C :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D] :
    Algebra.IndEtale (A ⧸ I) (TensorProduct A (A ⧸ I) D) :=
  (RingHom.IndEtale.algebraMap_iff _ _).mp (RingHom.IndEtale.isStableUnderBaseChange A D (A ⧸ I)
    (TensorProduct A (A ⧸ I) D) ((RingHom.IndEtale.algebraMap_iff _ _).mpr inferInstance))

/-- Reduction modulo `I` of ind-étale algebras, `D ↦ (A ⧸ I) ⊗_A D = D ⧸ I D`. Its opposite is the
base change functor `u : B_{Spec A} ⥤ B_{Spec (A ⧸ I)}`. -/
noncomputable def reduction : IndEtaleAlgCat A ⥤ IndEtaleAlgCat (A ⧸ I) where
  obj D := ⟨CommAlgCat.of (A ⧸ I) (TensorProduct A (A ⧸ I) D.obj), inferInstanceAs
    (Algebra.IndEtale (A ⧸ I) (TensorProduct A (A ⧸ I) D.obj))⟩
  map f := algHomEquiv.symm
    (Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) (algHomEquiv f))
  map_id _ := by
    apply algHomEquiv.injective
    ext <;> rfl
  map_comp _ _ := by
    apply algHomEquiv.injective
    ext <;> rfl

/-- The lift `H_A(C̄)` of an ind-étale `A ⧸ I`-algebra, as an ind-étale `A`-algebra. -/
noncomputable def closedLiftObj (C : IndEtaleAlgCat (A ⧸ I)) : IndEtaleAlgCat A :=
  ⟨CommAlgCat.of A (ClosedLift A C.obj), inferInstance⟩

/-- The bijection `Hom((A ⧸ I) ⊗_A D, C̄) ≃ Hom(D, H_A(C̄))` underlying the adjunction
`Algebra.IndEtaleAlgCat.closedLiftAdjunction`. -/
noncomputable def closedLiftHomEquiv (D : IndEtaleAlgCat A) (C : IndEtaleAlgCat (A ⧸ I)) :
    ((reduction A I).obj D ⟶ C) ≃ (D ⟶ closedLiftObj A I C) :=
  (algHomEquiv (X := (reduction A I).obj D) (Y := C)).trans
    ((baseChangeHomEquiv D.obj C.obj).trans ((ClosedLift.homEquiv D.obj).symm.trans
      (algHomEquiv (X := D) (Y := closedLiftObj A I C)).symm))

lemma toAlgHom_comp_closedLiftHomEquiv (D : IndEtaleAlgCat A) (C : IndEtaleAlgCat (A ⧸ I))
    (g : (reduction A I).obj D ⟶ C) :
    (toAlgHom A C.obj).comp (algHomEquiv (closedLiftHomEquiv A I D C g)) =
      baseChangeHomEquiv D.obj C.obj (algHomEquiv g) := by
  exact (ClosedLift.homEquiv D.obj).apply_symm_apply
    (baseChangeHomEquiv D.obj C.obj (algHomEquiv g))

lemma toAlgHom_closedLiftHomEquiv_apply (D : IndEtaleAlgCat A) (C : IndEtaleAlgCat (A ⧸ I))
    (g : (reduction A I).obj D ⟶ C) (x : D.obj) :
    toAlgHom A C.obj (algHomEquiv (closedLiftHomEquiv A I D C g) x) = algHomEquiv g (1 ⊗ₜ x) :=
  DFunLike.congr_fun (toAlgHom_comp_closedLiftHomEquiv A I D C g) x

/-- Blueprint `def-exc-closed-site-lift` (algebra side), see also `lem-exc-closed-lift-adjunction`:
the lift `C̄ ↦ H_A(C̄)` of ind-étale `A ⧸ I`-algebras to ind-étale `A`-algebras
(`Algebra.ClosedLift`), right adjoint to reduction modulo `I`. -/
noncomputable def closedLift : IndEtaleAlgCat (A ⧸ I) ⥤ IndEtaleAlgCat A :=
  Adjunction.rightAdjointOfEquiv (G_obj := closedLiftObj A I) (closedLiftHomEquiv A I)
    fun X' X Y f g ↦ by
      apply algHomEquiv.injective
      apply (ClosedLift.homEquiv X'.obj).injective
      ext x
      change toAlgHom A Y.obj (algHomEquiv (closedLiftHomEquiv A I X' Y _) x) =
        toAlgHom A Y.obj (algHomEquiv (closedLiftHomEquiv A I X Y g) (algHomEquiv f x))
      rw [toAlgHom_closedLiftHomEquiv_apply, toAlgHom_closedLiftHomEquiv_apply]
      rfl

/-- Blueprint `lem-exc-closed-lift-adjunction` (subsection `sk-prop-sf-open-closed-triangle`), as
an adjunction: reduction modulo `I` is left adjoint to the lift `H_A` on ind-étale algebras
(`Algebra.ClosedLift.homEquivReduction`). -/
noncomputable def closedLiftAdjunction : reduction A I ⊣ closedLift A I :=
  Adjunction.adjunctionOfEquivRight _ _

/-- The counit `(A ⧸ I) ⊗_A H_A(C̄) ⟶ C̄` of `Algebra.IndEtaleAlgCat.closedLiftAdjunction` is an
isomorphism: it is the reduction isomorphism of `Algebra.ClosedLift.bijective_reduction`. -/
theorem isIso_closedLiftAdjunction_counit_app (C : IndEtaleAlgCat (A ⧸ I)) :
    IsIso ((closedLiftAdjunction A I).counit.app C) := by
  let φ : TensorProduct A (A ⧸ I) (ClosedLift A C.obj) →ₐ[A ⧸ I] C.obj :=
    algHomEquiv ((closedLiftAdjunction A I).counit.app C)
  have hφ : ∀ x : ClosedLift A C.obj, φ (1 ⊗ₜ x) = toAlgHom A C.obj x := by
    intro x
    have := toAlgHom_closedLiftHomEquiv_apply A I _ C ((closedLiftAdjunction A I).counit.app C) x
    refine this.symm.trans ?_
    congr 1
    change algHomEquiv (closedLiftHomEquiv A I _ C ((closedLiftHomEquiv A I _ C).symm (𝟙 _))) x
      = x
    rw [Equiv.apply_symm_apply]
    rfl
  have hbij : Function.Bijective φ := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor (ClosedLift A C.obj) I
    have : (φ : _ → C.obj) ∘ e = ClosedLift.reduction A C.obj I := by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hφ x
    have hred := bijective_reduction A C.obj I
    rw [← this] at hred
    exact (Function.Bijective.of_comp_iff φ e.bijective).1 hred
  have : IsIso ((ObjectProperty.ι _).map ((closedLiftAdjunction A I).counit.app C)) :=
    (CommAlgCat.isoMk (AlgEquiv.ofBijective φ hbij)).isIso_hom
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

end IndEtaleAlgCat

variable (I : Ideal A)

/-- The base change functor `u : B_{Spec A} ⥤ B_{Spec (A ⧸ I)}` of affine ind-étale bases. -/
noncomputable abbrev closedSiteBaseChange : (IndEtaleAlgCat A)ᵒᵖ ⥤ (IndEtaleAlgCat (A ⧸ I))ᵒᵖ :=
  (IndEtaleAlgCat.reduction A I).op

/-- Blueprint `def-exc-closed-site-lift`: for `X = Spec A` and `Z = Spec (A ⧸ I)`, the lift
`v : B_Z ⥤ B_X` of affine ind-étale objects, `v(Spec C̄) = Spec H_A(C̄)`
(`Algebra.ClosedLift`), on the bases `B_X = (IndEtaleAlgCat A)ᵒᵖ`. -/
noncomputable abbrev closedSiteLift : (IndEtaleAlgCat (A ⧸ I))ᵒᵖ ⥤ (IndEtaleAlgCat A)ᵒᵖ :=
  (IndEtaleAlgCat.closedLift A I).op

/-- Blueprint `lem-exc-closed-site-adjunction` (subsection `sk-prop-sf-open-closed-triangle`): the
lift `v` is left adjoint to base change `u`; it is the opposite of the algebra adjunction
`Algebra.IndEtaleAlgCat.closedLiftAdjunction`. The unit `V ⟶ u v V` is an isomorphism
(`Algebra.isIso_closedSiteLiftAdjunction_unit_app`). -/
noncomputable def closedSiteLiftAdjunction : closedSiteLift A I ⊣ closedSiteBaseChange A I :=
  (IndEtaleAlgCat.closedLiftAdjunction A I).op

/-- The unit `V ⟶ u v V` of `Algebra.closedSiteLiftAdjunction` is an isomorphism, so `u v` is
canonically the identity (blueprint `lem-exc-closed-site-adjunction`). -/
theorem isIso_closedSiteLiftAdjunction_unit_app (V : (IndEtaleAlgCat (A ⧸ I))ᵒᵖ) :
    IsIso ((closedSiteLiftAdjunction A I).unit.app V) := by
  have := IndEtaleAlgCat.isIso_closedLiftAdjunction_counit_app A I V.unop
  change IsIso ((IndEtaleAlgCat.closedLiftAdjunction A I).counit.app V.unop).op
  infer_instance

end Algebra
