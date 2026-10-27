/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage
import Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated
import Sheaf.CategoryTheory.DerivedCategory.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
/-! # Finite truncation induction for derived internal Hom -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] {k : Type u} [Field k]
variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
/-- Finite truncation induction in both variables reduces Hom closure to single sheaves.
Source: Bhatt--Scholze, Remark 6.8.15, and Stacks Tag 08JC.
(blueprint: lem-sfb-dc-hom-devissage) -/
theorem boundedConstructible_hom_closure
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)]
    (hsingle : ∀ (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)),
      IsConstructibleModuleObject (condensedRingObj Λ X.left) F →
      IsConstructibleModuleObject (condensedRingObj Λ X.left) G →
      boundedConstructible (condensedRingObj Λ X.left)
        (((derivedHom Λ X.left).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
          ((DerivedCategory.singleFunctor _ 0).obj G))) :
    (boundedConstructible (condensedRingObj Λ X.left)).IsMonoidalClosed := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj Λ X.left)
  let P := boundedConstructible (condensedRingObj Λ X.left)
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : P.IsTriangulated := isTriangulated_boundedConstructible_ellAdic Λ X.left
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology Ab.{u + 1} X.left
  have : Abelian.HasFunctorialFlatResolution
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) :=
    AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf Ab.{u + 1} X.left
  have : IsGrothendieckAbelian.{u + 1} C :=
    Mod.isGrothendieckAbelian.{u + 1, u + 1, u + 2} _
  let : MonoidalClosed (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) :=
    AlgebraicGeometry.ProEtale.sheafMonoidalClosed Ab.{u + 1} X.left
  have : Abelian.HasFunctorialFlatResolution C :=
    Mod.hasFunctorialFlatResolution.{u + 1, u + 2}
      (C := Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (R := condensedRingObj Λ X.left)
  refine ⟨fun K L hK hL ↦ ?_⟩
  let H := (derivedHom Λ X.left).obj (op K)
  let : ((derivedTensor Λ X.left).obj K).CommShift ℤ :=
    DerivedCategory.commShiftTensorLeft C K
  have : ((derivedTensor Λ X.left).obj K).IsTriangulated :=
    DerivedCategory.isTriangulated_tensorLeft C K
  let adj := derivedTensorHomAdjunction Λ K
  let : H.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : H.IsTriangulated := adj.isTriangulated_rightAdjoint
  apply prop_of_boundedConstructibleModule (P.inverseImage H) ?_ hL
  intro G hG
  let W := (DerivedCategory.singleFunctor C 0).obj G
  let F := (derivedHom Λ X.left).flip.obj W
  obtain ⟨s, hs⟩ := DerivedCategory.nativeInternalHom_contravariant_exact.{u + 2, u + 1} C W
  let : F.CommShift ℤ := s
  have : F.IsTriangulated := hs
  exact prop_of_boundedConstructibleModule (P.inverseImage F).unop
    (fun F hF ↦ hsingle F G hF hG) hK


end AlgebraicGeometry.ProEtale.CondensedRing
