module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A semilinear chain map and coefficient map induce the expected tensor chain map. -/
theorem tensorResolutionSemilinearTensorLift
    (A C : Type u) [CommRing A] [CommRing C] (φ : A →+* C)
    (P : ChainComplex (ModuleCat.{u} A) ℕ)
    (R : ChainComplex (ModuleCat.{u} C) ℕ)
    (N : ModuleCat.{u} A) (N' : ModuleCat.{u} C)
    (a : P ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj R)
    (b : N →ₛₗ[φ] N') :
    let TA := (tensorRight N).mapHomologicalComplex (.down ℕ)
    let TC := (tensorRight N').mapHomologicalComplex (.down ℕ)
    ∃ k : TA.obj P ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj (TC.obj R),
      ∀ (j : ℕ) (x : P.X j) (y : N),
        k.f j (x ⊗ₜ[A] y) = (show R.X j from a.f j x) ⊗ₜ[C] (b y) := by
  classical
  dsimp only
  let au (j : ℕ) : P.X j →ₛₗ[φ] R.X j :=
    { toFun := a.f j
      map_add' := (a.f j).hom.map_add
      map_smul' := (a.f j).hom.map_smul }
  let TA := (tensorRight N).mapHomologicalComplex (.down ℕ)
  let TC := (tensorRight N').mapHomologicalComplex (.down ℕ)
  let kf (j : ℕ) : (TA.obj P).X j ⟶
      (ModuleCat.restrictScalars φ).obj ((TC.obj R).X j) :=
    ModuleCat.ofHom (X := (TA.obj P).X j)
      (Y := (ModuleCat.restrictScalars φ).obj ((TC.obj R).X j))
      { toFun := TensorProduct.map (au j) b
        map_add' := (TensorProduct.map (au j) b).map_add
        map_smul' := (TensorProduct.map (au j) b).map_smul' }
  let k : TA.obj P ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (.down ℕ)).obj (TC.obj R) :=
    { f := kf
      comm' := by
        intro j l hjl
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        change R.d j l (a.f j x) ⊗ₜ[C] b y =
          (show R.X l from a.f l (P.d j l x)) ⊗ₜ[C] b y
        have h := congrArg (fun g ↦ g x) (a.comm j l)
        exact congrArg (fun z : R.X l ↦ z ⊗ₜ[C] b y) h }
  exact ⟨k, by intro j x y; rfl⟩

end AlgebraicGeometry
