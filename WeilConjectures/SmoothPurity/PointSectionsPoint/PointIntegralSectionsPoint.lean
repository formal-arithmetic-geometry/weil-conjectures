/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.SixFunctors.RingedSitePoint
public import WeilConjectures.AlgebraicGeometry.GeometricStalkToposPoint
import all WeilConjectures.Algebra.Homology.RingedSitePointTensor
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.Limits

/-! # Final-object sections as a ringed topos point

Source: the geometric-stalk point construction and the identity pointed neighbourhood.
(blueprint: lem-sf-point-integral-sections-point).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointSectionsPoint
variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The actual set-valued final-object evaluation.
Source: geometric-stalk point specialization (blueprint: lem-sf-point-integral-sections-point). -/
abbrev sets := (sheafSections (ProEt.topology (Spec (.of k))) (Type (u + 1))).obj
  (op (ProEt.mk (𝟙 (Spec (.of k)))))

/-- Final-object evaluation is the inverse image of a topos point.
Source: identity pointed neighbourhood and the geometric-stalk adjunction
(blueprint: lem-sf-point-integral-sections-point).

Proof: the identity pointed neighbourhood is initial, by full faithfulness of the
site's forgetful functor to schemes over the base. Its opposite is terminal, so its
colimit inclusion identifies final-object evaluation with the geometric stalk.
Transport the geometric-stalk adjunction along this natural isomorphism. -/
theorem sets_isLeftAdjoint : (sets k).IsLeftAdjoint := by
  let U := ProEt.mk (𝟙 (Spec (.of k)))
  let N : ProEtaleGeometricNeighbourhood (𝟙 (Spec (.of k))) :=
    StructuredArrow.mk (𝟙 ((ProEt.forget (Spec (.of k))).obj U))
  have hN : IsInitial N := StructuredArrow.mkIdInitial
  let H := (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
    (proEtaleGeometricNeighbourhoodForget (𝟙 (Spec (.of k)))).op
  let α : sets k ⟶ proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))) :=
    Functor.whiskerLeft (sheafToPresheaf _ _) (Functor.whiskerLeft H (colim.ι (op N)))
  have hi (F : Sheaf (ProEt.topology (Spec (.of k))) (Type (u + 1))) :
      IsIso (α.app F) :=
    (colimit.isColimit _).isIso_ι_app_of_isTerminal _ hN.op
  have : IsIso α := NatIso.isIso_of_isIso_app α
  obtain ⟨R, _, ⟨adj⟩, _⟩ := (geometricStalkToposPoint (𝟙 (Spec (.of k)))).2
  exact ⟨R, ⟨adj.ofNatIsoLeft (asIso α).symm⟩⟩

/-- The topos point with literal final-object evaluation as inverse image.
Source: the preceding adjunction theorem
(blueprint: lem-sf-point-integral-sections-point). -/
def point : GeometricMorphism (Type (u + 1))
    (Sheaf (ProEt.topology (Spec (.of k))) (Type (u + 1))) := by
  let := sets_isLeftAdjoint k
  exact { inverse := sets k
          direct := (sets k).rightAdjoint
          adj := Adjunction.ofIsLeftAdjoint (sets k)
          leftExact := by
            change PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
              (CategoryTheory.evaluation _ _).obj (op (ProEt.mk (𝟙 (Spec (.of k))))))
            infer_instance }

/-- Module evaluation, with its actual section-ring action, is a ringed point.
Source: geometric-stalk point specialization (blueprint: lem-sf-point-integral-sections-point). -/
def ringed (B : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :
    RingedSitePoint B (point k) where
  ring := CommRingCat.of (B.obj.obj (op (ProEt.mk (𝟙 (Spec (.of k))))))
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h x ↦ h _ x
  ringMul := fun _ _ _ _ h x ↦ h _ x
  ringZero := fun _ _ h x ↦ h _ x
  ringOne := fun _ _ h x ↦ h _ x
  modules := ProEtale.pointModuleSections k B
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h x ↦ h _ x
  moduleZero := fun _ _ _ h x ↦ h _ x
  moduleSMul := fun _ _ _ _ _ h x ↦ h _ x
  modules_additive := ⟨by intros; rfl⟩

end WeilConjectures.PointSectionsPoint
