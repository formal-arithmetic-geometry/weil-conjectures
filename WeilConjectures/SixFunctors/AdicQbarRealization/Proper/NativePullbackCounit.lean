/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackIdentityCancellation

/-! # The normalized derived counit for native module inverse image

Source: Bhatt--Scholze Remark 6.8.15; Stacks Tag 06YY.
(blueprint: lem-sf-native-pullback-counit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

/-- The canonical scalar-extension computation counit becomes a normalized module
inverse-image counit after removing the identity coefficient factor.
Source: Bhatt--Scholze Remark 6.8.15; Stacks Tag 06YY.
(blueprint: lem-sf-native-pullback-counit).

Proof: use the tensor-generator-normalized identity cancellation, and apply it in
every cochain degree. The resulting cochain isomorphism has exactly its ordinary
components. Compose the exact inverse-image computation isomorphism, the scalar
extension universal counit, and localization of this cochain isomorphism. Each factor
is a natural transformation, so their composite is natural on all complexes. Its
component is precisely the formula defining IsNormalizedPullCounit. The ordinary
cancellation theorem supplies the required generator equation. No flatness or
boundedness restriction is needed for this natural transformation. -/
theorem nativePullbackCounit {X Y : Scheme.{u}} (p : X ⟶ Y)
    {A : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage p).obj A ⟶ B)
    [(ContinuousRational.modulePull p c).Additive] :
    ∃ δ : DerivedCategory.Q ⋙ ContinuousRational.derivedPull p c ⟶
        (ContinuousRational.modulePull p c).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q,
      ContinuousRational.IsNormalizedPullCounit p c δ := by
  obtain ⟨e, he⟩ := nativePullbackIdentityCancellation p c
  let G := proEtaleRingModulePullback p A ((adicTowerInverseImage p).obj A) (Iso.refl _)
  let eC := Functor.mapHomologicalComplexCompIso e (.up ℤ)
  let β : DerivedCategory.Q ⋙ pbcDerivedExtend c ⟶
      (pbcExtend c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (pbcDerivedExtend c) ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ _) (pbcExtensionCounit c) ≫
      Functor.whiskerRight ((pbcExtend c).mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft ((pbcExtend c).mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso _).hom
  let δ : DerivedCategory.Q ⋙ ContinuousRational.derivedPull p c ⟶
      (ContinuousRational.modulePull p c).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    Functor.whiskerRight
        (proEtaleRingDerivedPullbackFactors p A ((adicTowerInverseImage p).obj A)
          (Iso.refl _)).hom (pbcDerivedExtend c) ≫
      Functor.whiskerLeft (G.mapHomologicalComplex (.up ℤ)) β ≫
      Functor.whiskerRight eC.hom DerivedCategory.Q
  refine ⟨δ, e, eC, ?_, he, ?_⟩
  · intro P n
    rfl
  · intro P
    rfl

end WeilConjectures.AdicQbarRealization.Proper
