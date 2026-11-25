/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
public import WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchange

/-! # The derived affine tensor mate before taking homology

## References

* Stacks Project, Tag 06Z0
* Stacks Project, Tag 06Y6
* Stacks Project, Tag 01I9
* Stacks Project, Tag 08HY
* Stacks Project, Tag 0DJ8
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The induced exact associated-sheaf functor, using the proved exactness of tilde. -/
def affineExactTildeDerived (B : Type u) [CommRing B]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)] :
    DerivedCategory.{wM} (ModuleCat.{u} B) ⥤
      schemeDerivedCategory.{u, w} (Spec (.of B)) := by
  let T := affinePushforwardTilde B
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : T.PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  let : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  exact T.mapDerivedCategory

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
  (M : CochainComplex (ModuleCat.{u} A) ℤ)
  (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)

/-- The actual cohomology coordinates of derived associated sheaf of the tensor model. -/
def affineTildeDerivedTensorSourceIso (i : ℤ) :
    (affinePushforwardTilde B).obj
        ((ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom).obj
          (m.cohomology i)) ≅
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).obj
        ((affineExactTildeDerived.{u, w, wM} B).obj
          (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
            (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
              (.up ℤ)).obj M))))) := by
  let T := affinePushforwardTilde B
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : T.PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  let : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  exact T.mapIso (m.cohomologyIso i) ≪≫
    (T.mapDerivedCategoryHomologyFunctorIso i).app _

/-- Scalar-extension augmentation and coefficient map, as a map of B-complexes. -/
def affineTildeTensorCoefficientComplexMap
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ) :
    (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (.up ℤ)).obj M)) ⟶
    ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) := by
  let α := algebraMap (A ⊗[R] B) D
  let j : B →+* A ⊗[R] B := Algebra.TensorProduct.includeRight.toRingHom
  let C := (((ModuleCat.extendScalars (α.comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
    (.up ℤ)).obj M)
  let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let ρ := ModuleCat.restrictScalarsComp' j α ψ hψ.symm
  let z : C ⟶ Cg := eqToHom (by dsimp only [C, α]; rw [hφ])
  exact m.ordinaryIso.hom ≫
    ((ModuleCat.restrictScalars j).mapHomologicalComplex (.up ℤ)).map m.ordinaryToLocalized ≫
    (ρ.inv.mapHomologicalComplex (.up ℤ)).app C ≫
    ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).map z


omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem affineTildeTensorCoefficientComplexMap_tmul
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ)
    (i : ℤ) (b : B) (q : M.X i) :
    (affineTildeTensorCoefficientComplexMap R A B D M m φ ψ hφ hψ).f i
        (b ⊗ₜ[R,algebraMap R B] q) = ψ b ⊗ₜ[A,φ] q := by
  subst φ
  subst ψ
  dsimp only [affineTildeTensorCoefficientComplexMap]
  simp only [eqToHom_refl]
  change m.ordinaryToLocalized.f i
      (m.ordinaryIso.hom.f i (b ⊗ₜ[R,algebraMap R B] q)) = _
  rw [m.ordinaryIso_tmul, m.ordinaryToLocalized_tmul]
  rfl

/-- The raw derived tensor counit followed by the coefficient map, ordinary affine
pushforward comparison and right-derived pushforward unit. This construction uses
no base-change mate, pullback counit or cohomological degree. -/
def affineTildeDerivedTensorToPushforward
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ) :
    (affineExactTildeDerived.{u, w, wM} B).obj
      (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)))) ⟶
    (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom ψ))).obj
      (DerivedCategory.Q.obj (((affinePushforwardTilde D).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))) := by
  let T := affinePushforwardTilde B
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : T.PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  let : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  have hF₀ : affineExactTildeDerived.{u, w, wM} B =
      Functor.mapDerivedCategory.{wM, w} (affinePushforwardTilde B) := rfl
  exact affineTildeTensorDerivedCounit R A B D M m
      (affineExactTildeDerived.{u, w, wM} B) hF₀ ≫
    affineTildeTensorOrdinaryTargetMap R A B D M φ ψ
      (affineTildeTensorCoefficientComplexMap R A B D M m φ ψ hφ hψ)

private theorem affineTildeDerivedTensorToPushforward_factor
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ) :
    let T := affinePushforwardTilde B
    let : T.Additive := by
      constructor
      intro M N f g
      exact tilde.map_add (R := .of B) f g
    let : T.PreservesHomology := tilde_preservesHomology B
    let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
    let : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
    let hF₀ : affineExactTildeDerived.{u, w, wM} B = T.mapDerivedCategory := rfl
    affineTildeDerivedTensorToPushforward R A B D M m φ ψ hφ hψ =
      affineTildeTensorDerivedCounit R A B D M m
        (affineExactTildeDerived.{u, w, wM} B) hF₀ ≫
      affineTildeTensorOrdinaryTargetMap R A B D M φ ψ
        (affineTildeTensorCoefficientComplexMap R A B D M m φ ψ hφ hψ) := by
  rfl

attribute [local irreducible] tilde Functor.mapDerivedCategory affineTildePushforwardComparison
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit Scheme.Modules.tensorPullback
  affineBaseChangeTildeRepresentativeIso affineTildeTensorOrdinarySourceIso
  schemeDerivedBaseChangeMap affineTildeTensorDerivedCounit affineTildeTensorOrdinaryTargetMap
  affineTildeDerivedTensorToPushforward

/-- The affine base-change mate on the derived scalar-extension object, before
applying any homology functor. Its source comparison is independent of D. -/
theorem exists_affineTildeDerivedTensorMate
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (_hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (_hK : schemeDerivedQCohProperty (Spec (.of A))
      (DerivedCategory.Q.obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)))
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    let K := DerivedCategory.Q.obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)
    let t := affineBaseChangeTildeRepresentativeIso A D φ K M (Iso.refl K) hc
    ∃ σ : (affineExactTildeDerived.{u, w, wM} B).obj
          (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
            (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
              (.up ℤ)).obj M)))) ≅
        (derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj K),
      σ.hom ≫ schemeDerivedBaseChangeMap
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom ψ))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom φ)) hw K =
      affineTildeDerivedTensorToPushforward R A B D M m φ ψ hφ hψ ≫
        (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom ψ))).map t.hom := by
  clear _hM _hK
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let p := Spec.map (CommRingCat.ofHom φ)
  let f' := Spec.map (CommRingCat.ofHom ψ)
  let H : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) (.up ℤ) :=
    (HomotopyCategory.quotient _ (.up ℤ)).obj
    (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)
  let T := affinePushforwardTilde B
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : T.PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  let : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  have hF₀ : affineExactTildeDerived.{u, w, wM} B =
      T.mapDerivedCategory := rfl
  obtain ⟨χ, hχ⟩ := exists_affineTildeTensorSourceComparison.{u, w, wM} R A B D M m
    (affineExactTildeDerived.{u, w, wM} B) hF₀
  let σ := χ
  let t := affineBaseChangeTildeRepresentativeIso A D φ
    (DerivedCategory.Q.obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)) M (Iso.refl _) hc
  suffices hsigma : σ.hom ≫
      schemeDerivedBaseChangeMap f f' g p hw (DerivedCategory.Qh.obj H) =
      affineTildeDerivedTensorToPushforward R A B D M m φ ψ hφ hψ ≫
        (schemeDerivedDirectImage f').map t.hom by
    exact ⟨σ, hsigma⟩
  let : (Scheme.Modules.tensorPullback g).Additive :=
    SingleComplexBaseChange.tensorPullbackAdditive.{u, w} g
  let : (Scheme.Modules.tensorPullback p).Additive :=
    SingleComplexBaseChange.tensorPullbackAdditive.{u, w} p
  let c := (SingleComplexBaseChange.counit p).app H
  have : IsIso c := hc
  have hsource := hχ φ ψ hw
  have he := affineTildeTensorOrdinaryExchange.{u, w} R A B D M φ ψ hw
    (affineTildeTensorCoefficientComplexMap R A B D M m φ ψ hφ hψ)
    (affineTildeTensorCoefficientComplexMap_tmul R A B D M m φ ψ hφ hψ) hc
  have hr := affineTildeDerivedTensorToPushforward_factor R A B D M m φ ψ hφ hψ
  have hexchange := congrArg (fun k ↦
    affineTildeTensorDerivedCounit R A B D M m
      (affineExactTildeDerived.{u, w, wM} B) hF₀ ≫ k) he
  have hresult := hsource.trans (by simpa only [Category.assoc] using hexchange)
  have : IsIso ((schemeDerivedDirectImage f').map c) := inferInstance
  apply (cancel_mono ((schemeDerivedDirectImage f').map c)).mp
  simpa only [σ, cast_eq, Category.assoc, hr] using hresult

end AlgebraicGeometry
