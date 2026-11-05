/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction

/-! # Coordinates for the finite tensor representative square

Source: Stacks 07A4 and 00YV.
(blueprint: def-pur-finite-pullback-tensor-representative-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures.FinitePullbackTensorRep
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf finiteIntrinsicDerivedTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local implicit_reducible] modules_abelian modules_derived

/-- The same pullback on complexes.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def pull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    CochainComplex (normalizedDVRModules l E Y n) ℤ ⥤
      CochainComplex (normalizedDVRModules l E X n) ℤ :=
  (ordinary l E f n).mapHomologicalComplex (.up ℤ)

/-- The fixed tensor-model representative comparison followed by its recorded identification.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def representative (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) P)
    (hQ : proEtaleFlatRepresentatives W (integralCoefficientCommRingSheaf l E W n) Q) :
    (quotient l E W n).obj (tensor l E W n P Q) ≅
      (finiteIntrinsicDerivedTensor l E W n).obj
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  (pullbackTensorFiniteModel l E W n).representative.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≪≫
    (pullbackTensorFiniteModelIso l E W n).app
      ((quotient l E W n).obj P, (quotient l E W n).obj Q)

/-- Exact pullback computed in the ordinary model, using the prescribed realization.
Source: Stacks 00YV (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def factors {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    DerivedCategory.Q ⋙ finiteDerivedPullback l E n f ≅
      pull l E f n ⋙ DerivedCategory.Q := by
  unfold pull
  exact isoWhiskerLeft DerivedCategory.Q
      (realization l E f n).symm ≪≫
    (ordinaryFactors l E f n)

/-- The forward total-tensor comparison in the ordinary presentation.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    (pull l E f n).obj (tensor l E Y n P Q) ⟶
      tensor l E X n ((pull l E f n).obj P) ((pull l E f n).obj Q) := by
  unfold pull
  exact (proEtaleTensorPullbackTotalIso f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n) P Q).inv

/-- Its degreewise action on complexes.
Source: Stacks 00YV (blueprint: def-pur-finite-pullback-tensor-representative-data). -/
@[irreducible] def complexComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ) :
    pull l E (h ≫ f) n ≅ pull l E f n ⋙ pull l E h n :=
  by
    unfold pull
    exact (mapHomologicalComplexCompIso (moduleComp l E f h n).symm (.up ℤ)).symm

end WeilConjectures.FinitePullbackTensorRep
