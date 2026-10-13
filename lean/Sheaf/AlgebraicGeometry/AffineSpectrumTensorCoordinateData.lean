/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
import Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
private def tensorDegreeIso
    {A A₀ D D₀ : Type u}
    [CommRing A] [CommRing A₀] [CommRing D] [CommRing D₀]
    (φ : A →+* D) (φ₀ : A₀ →+* D₀) (eA : A ≃+* A₀) (eD : D ≃+* D₀)
    (h : ∀ a, eD (φ a) = φ₀ (eA a))
    (M : ModuleCat.{u} A) (M₀ : ModuleCat.{u} A₀)
    (q : M ≅ (ModuleCat.restrictScalars eA.toRingHom).obj M₀) :
    (ModuleCat.extendScalars φ).obj M ≅
      (ModuleCat.restrictScalars eD.toRingHom).obj
        ((ModuleCat.extendScalars φ₀).obj M₀) := by
  let := RingHomInvPair.of_ringEquiv eA
  let := RingHomInvPair.of_ringEquiv_symm eA
  let : Module A D := Module.compHom D φ
  let : Module A₀ D₀ := Module.compHom D₀ φ₀
  let d : LinearEquiv (eA : A →+* A₀) (σ' := (eA.symm : A₀ →+* A)) D D₀ :=
    { __ := eD.toAddEquiv
      map_smul' := by
        intro a x
        change eD (φ a * x) = φ₀ (eA a) * eD x
        rw [map_mul, h] }
  let c : LinearEquiv (eA : A →+* A₀) (σ' := (eA.symm : A₀ →+* A)) M M₀ :=
    { __ := q.toLinearEquiv.toAddEquiv
      map_smul' := q.hom.hom.map_smul }
  let T := TensorProduct.congr (σ₂₁ := (eA.symm : A₀ →+* A)) d c
  let T' : (ModuleCat.extendScalars φ).obj M ≃ₗ[D]
      (ModuleCat.restrictScalars eD.toRingHom).obj
        ((ModuleCat.extendScalars φ₀).obj M₀) :=
    { __ := T.toAddEquiv
      map_smul' := by
        intro b z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul b' m =>
          change D at b'
          change T ((b * b') ⊗ₜ[A] m) = eD b • T (b' ⊗ₜ[A] m)
          change eD (b * b') ⊗ₜ[A₀] c m = (eD b * eD b') ⊗ₜ[A₀] c m
          rw [map_mul]
        | add z w hz hw =>
          change T (b • (z + w)) = eD b • T (z + w)
          change T (b • z) = eD b • T z at hz
          change T (b • w) = eD b • T w at hw
          rw [smul_add, map_add, hz, hw, map_add, smul_add] }
  exact T'.toModuleIso

private theorem tensorDegreeIso_tmul
    {A A₀ D D₀ : Type u}
    [CommRing A] [CommRing A₀] [CommRing D] [CommRing D₀]
    (φ : A →+* D) (φ₀ : A₀ →+* D₀) (eA : A ≃+* A₀) (eD : D ≃+* D₀)
    (h : ∀ a, eD (φ a) = φ₀ (eA a))
    (M : ModuleCat.{u} A) (M₀ : ModuleCat.{u} A₀)
    (q : M ≅ (ModuleCat.restrictScalars eA.toRingHom).obj M₀)
    (d : D) (m : M) :
    (tensorDegreeIso φ φ₀ eA eD h M M₀ q).hom (d ⊗ₜ[A, φ] m) =
      eD d ⊗ₜ[A₀, φ₀] (show M₀ from q.hom m) := by
  rfl

private theorem exists_tensorComplexIso
    {A A₀ D D₀ : Type u}
    [CommRing A] [CommRing A₀] [CommRing D] [CommRing D₀]
    (φ : A →+* D) (φ₀ : A₀ →+* D₀) (eA : A ≃+* A₀) (eD : D ≃+* D₀)
    (h : ∀ a, eD (φ a) = φ₀ (eA a))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (Q₀ : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (q : Q ≅ ((ModuleCat.restrictScalars eA.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj Q₀) :
    ∃ t : ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj Q ≅
        ((ModuleCat.restrictScalars eD.toRingHom).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars φ₀).mapHomologicalComplex (.up ℤ)).obj Q₀),
      ∀ (k : ℤ) (d : D) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A, φ] x) =
          eD d ⊗ₜ[A₀, φ₀] (show Q₀.X k from q.hom.f k x) := by
  let e (k : ℤ) := tensorDegreeIso φ φ₀ eA eD h (Q.X k) (Q₀.X k)
    (HomologicalComplex.eval _ _ k |>.mapIso q)
  have he (k : ℤ) (d : D) (x : Q.X k) :
      (e k).hom (d ⊗ₜ[A, φ] x) =
        eD d ⊗ₜ[A₀, φ₀] (show Q₀.X k from q.hom.f k x) :=
    tensorDegreeIso_tmul φ φ₀ eA eD h _ _ _ d x
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_, ?_⟩
  · intro k l _
    ext x
    symm
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul d x =>
      change (e l).hom ((ModuleCat.extendScalars φ).map (Q.d k l) (d ⊗ₜ[A, φ] x)) =
        (ModuleCat.restrictScalars eD.toRingHom).map
          ((ModuleCat.extendScalars φ₀).map (Q₀.d k l)) ((e k).hom (d ⊗ₜ[A, φ] x))
      rw [ModuleCat.ExtendScalars.map_tmul, he, he]
      change eD d ⊗ₜ[A₀, φ₀] (show Q₀.X l from q.hom.f l (Q.d k l x)) =
        eD d ⊗ₜ[A₀, φ₀] (Q₀.d k l (show Q₀.X k from q.hom.f k x))
      congr 1
      exact (ConcreteCategory.congr_hom (q.hom.comm k l) x).symm
  · exact he

namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option backward.isDefEq.respectTransparency true in
-- The retained public signature includes homology coordinates absent from this conclusion.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency.types true in
/-- The affine coordinate and tensor compatibility data, split from the parent transport theorem.
Source: Stacks Project, Tag 0098.
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-data). -/
theorem exists_affineSpectrum_tensor_coordinate_data
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let j := X'.isoSpec.inv
    let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    let alpha := (NatIso.mapHomologicalComplex
      ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso j g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
      (.up ℤ)).app P
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    let V0 := tensorComplex (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
    ∃ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0)
      (t : tensorComplex f f' g g' sq z P ≅
        ((ModuleCat.restrictScalars.{u} eD.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj V0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) ∧
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) := by
  classical
  intro z P0 Pg j S0 F F0 alpha R0 A0 B0 D0 Q Q0 V0
  clear i Pg S0 F F0 alpha
  obtain ⟨eR, eA, eB, eD, q, hRA, hRB, hD⟩ :=
    exists_affineSpectrum_stalk_coordinate_data f f' g g' sq sq0 z0 P
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
  let := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
  let := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
  let φ := (tensorMap f f' g g' sq z).comp
    (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))
  let φ0 := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
      (algebraMap A0 (A0 ⊗[R0] B0))
  have hφ (a : A g' z) : eD (φ a) = φ0 (eA a) := by
    change eD ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z))
      (a ⊗ₜ[R f g' z] 1)) =
        (algebraMap (A0 ⊗[R0] B0) D0) (eA a ⊗ₜ[R0] 1)
    simpa only [map_one] using hD a 1
  obtain ⟨t, ht⟩ := exists_tensorComplexIso φ φ0 eA eD hφ
    Q Q0 q
  refine ⟨eR, eA, eB, eD, q, t, ?_, ?_, ?_, ?_⟩
  · exact hRA
  · exact hRB
  · exact hD
  · intro k d x
    exact ht k d x

end AlgebraicGeometry.SingleComplexBaseChange
