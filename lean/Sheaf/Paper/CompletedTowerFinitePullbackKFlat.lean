/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import all Sheaf.Paper.ProEtaleCanonicalTensorPullback
import all Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Algebra.Homology.AlgebraicInverseImageKFlat
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients

/-! # Arbitrary K-flatness for the actual finite tower pullback

Source: Stacks Project, Cohomology on Sites, Tags 0DEN and 0DEP.
(blueprint: lem-pur-completed-tower-finite-pullback-kflat)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- The actual finite pullback in the strict tower preserves every K-flat complex.
Source: Stacks 0DEN and 0DEP
(blueprint: lem-pur-completed-tower-finite-pullback-kflat).
Proof: use the specified algebraic inverse image on the pro-etale topoi. The
conservative family of target points and the stalk criterion preserve K-flatness.
Scalar extension along the constant-ring comparison also preserves K-flatness.
The right adjoint of this composite has exactly the constant-section coefficient
map used by coefficientProEtaleModuleDirectImage. The adjunction Hom equivalence
identifies these maps. Uniqueness of left adjoints therefore compares the
composite with integralOperationsLevelPullback. Apply that natural isomorphism
degreewise and transport acyclicity of every total tensor test. No flat-term,
boundedness, constructibility or invertibility hypothesis is used. -/
theorem completedTowerFinitePullbackKFlat {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y n) P) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
      u + 1, u + 1, u + 2, u + 1} _
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
      u + 1, u + 1, u + 2, u + 1} _
  let A : Type u := Padic.coefficientExtensionRing l E (n + 1)
  let R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1} :=
    integralCoefficientCommRingSheaf l E Y n
  let S : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
    integralCoefficientCommRingSheaf l E X n
  let RI : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  let c : RI ≅ S := proEtaleConstantRingComparison.{u} f A
  let geom : GeometricMorphism
      (Sheaf (ProEt.topology X) (Type (u + 1)))
      (Sheaf (ProEt.topology Y) (Type (u + 1))) :=
    { inverse := proEtaleSheafInverseImage f (Type (u + 1))
      direct := proEtaleSheafDirectImage f (Type (u + 1))
      adj := proEtaleSheafAdjunction f (Type (u + 1))
      leftExact := (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1 }
  let I := SheafOfModules.inverseImageOfUniverses (normalizedAlgebraicLift f R)
  let : Limits.PreservesFiniteLimits (proEtaleModuleInverseImage f R) :=
    proEtaleModuleInverseImage_preservesFiniteLimits f R
  have : (proEtaleModuleInverseImage f R).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : I.modules.Additive := inferInstanceAs (proEtaleModuleInverseImage f R).Additive
  obtain ⟨ι, p, hp⟩ := proEtale_enoughPoints.{u, u} X
  let s : ∀ i, RingedSitePoint RI (p i) :=
    fun i ↦ Classical.choice (RingedSitePoint.nonempty _ (p i))
  have hcons : JointlyReflectIsomorphisms (fun i ↦ (p i).inverse) := by
    constructor
    intro M N a _
    exact hp a (fun i ↦ (isIso_iff_bijective ((p i).inverse.map a)).1 inferInstance)
  have hI := SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points
    (ProEt.topology Y) (ProEt.topology X) geom I ι p s hcons P hP
  let F := proEtaleRingExtension f R S c
  let : Limits.PreservesFiniteLimits F := proEtaleRingExtension_preservesFiniteLimits f R S c
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have hF := SheafOfModules.changeOfRings_isKFlat_independentCoefficients c.hom
    ((I.modules.mapHomologicalComplex (.up ℤ)).obj P) F
    (fun _ ↦ rfl) (fun g ↦ by
      change F.map g = 𝟙 _ ≫ SheafOfModules.changeOfRingsHom c.hom _ g ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      rfl) hI
  have hc : proEtaleRingDirectImageMap f R S c =
      proEtaleCoefficientDirectImageMap f A :=
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
      (proEtaleCoefficientDirectImageMap f A)
  let d : proEtaleRingModuleDirectImage f R S c ≅
      coefficientProEtaleModuleDirectImage.{u, u} f
        (CommRingCat.of (ULift.{u + 1} A)) :=
    SheafOfModules.pushforwardCongr (by rw [hc]; rfl)
  let adj := (proEtaleRingModuleAdjunction f R S c).ofNatIsoRight d
  let e₀ : proEtaleRingModulePullback f R S c ≅ integralOperationsLevelPullback l E f n :=
    adj.leftAdjointUniq (coefficientProEtaleModuleAdjunction.{u, u} f
      (CommRingCat.of (ULift.{u + 1} A)))
  have : (integralOperationsLevelPullback l E f n).Additive :=
    integralOperationsLevelPullback_additive l E f n
  let : (integralOperationsLevelPullback l E f n).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let e : ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P ≅
      ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj P :=
    HomologicalComplex.Hom.isoOfComponents (fun k ↦ e₀.app (P.X k))
      (fun i j _ ↦ (e₀.hom.naturality (P.d i j)).symm)
  let B := S
  let := SheafOfModules.isMonoidal_W_independentCoefficients B
  let := SheafOfModules.monoidalCategory B
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients B
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients B
  intro Q hQ i
  exact (hF Q hQ i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj Q).mapIso e)

end WeilConjectures
