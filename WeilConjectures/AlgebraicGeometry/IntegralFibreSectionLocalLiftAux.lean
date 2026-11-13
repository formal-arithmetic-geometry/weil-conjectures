/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure


public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiber
import WeilConjectures.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility
import WeilConjectures.AlgebraicGeometry.IntegralStrictHenselianGeometricFibreSections
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension

/-! # Integral strict-local fibre comparison

## References

* Stacks Project, Tag 0EYP.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- Sections on the integral strict-local pullback and on the geometric fibre agree,
compatibly with the restrictions from each affine pointed neighbourhood. This compares
only two schemes; it does not assert that strict-local sections have neighbourhood
representatives, which is the separate qcqs continuity theorem. (Stacks, Tag 0EYP) -/
theorem exists_integralStrictLocalFibreComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Sheaf.Γ (pullback f (strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (strictLocalizationToBase s))).obj F) ≅
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        qcqsStrictLocalSectionRestriction Λ f s F j ≫ e.hom =
          geometricFibreSectionRestriction Λ sq.toCommSq F
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2 := by
  classical
  obtain ⟨hl, hs⟩ := (show ∃ (_ : IsLocalRing (Scheme.strictHenselization s)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselization s) from
      ⟨inferInstance, ⟨inferInstance⟩⟩)
  let := hl
  let := hs
  let : Algebra (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨ψ, hsurj, hker, hpoint⟩ := strictHenselizationPointedMap s (by rfl)
  let t : Spec (.of Ω) ⟶ strictLocalization s := Spec.map (CommRingCat.ofHom
    ((IntermediateField.val
      (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp ψ))
  have ht : t ≫ strictLocalizationToBase s = s := by
    let := (strictHenselizationAffineProperties s).2.1
    let j := Classical.choice (IsCofiltered.nonempty (C :=
      SmallModel.{u} (strictHenselizationNeighbourhoods s)))
    have hp := hpoint j
    rw [isoSpec_Spec_inv] at hp
    have hstr := strictHenselizationStructuralMap_eq s j
    change _ = strictLocalizationToBase s at hstr
    rw [← hstr, ← Category.assoc, ← Category.assoc]
    exact (congrArg (fun a ↦ a ≫ ((AffineEtale.Spec Y).obj
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1).hom)
      hp).trans ((equivSmallModel.{u}
        (strictHenselizationNeighbourhoods s)).inverse.obj j).2.w
  set_option backward.isDefEq.respectTransparency false in
  have hclosed : t (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (strictHenselization s) := by
    apply (strictHenselizationStructuralMap_fiber_eq_closedPoint
      (A := strictHenselization s) s (Iso.refl _)
      (t (IsLocalRing.closedPoint Ω))).mp
    change (t ≫ strictLocalizationToBase s) (IsLocalRing.closedPoint Ω) = _
    rw [ht]
  let i : X' ⟶ pullback f (strictLocalizationToBase s) :=
    pullback.lift g' (f' ≫ t) (by rw [Category.assoc, ht]; exact sq.w)
  have hi : i ≫ pullback.fst f (strictLocalizationToBase s) = g' :=
    pullback.lift_fst _ _ _
  have hi' : i ≫ pullback.snd f (strictLocalizationToBase s) = f' ≫ t :=
    pullback.lift_snd _ _ _
  have hsq : IsPullback i f' (pullback.snd f (strictLocalizationToBase s)) t := by
    apply IsPullback.of_right _ hi'
      (IsPullback.of_hasPullback f (strictLocalizationToBase s))
    simpa only [hi, ht] using sq
  have hc : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (strictLocalizationToBase s))).obj F)) :=
    isIso_integralStrictHenselianGeometricFibreRestriction Λ (strictHenselization s)
      (pullback.snd f (strictLocalizationToBase s)) t hclosed hsq _
  let := hc
  have : IsIso (strictLocalFibreRestriction Λ i hi F) := by
    unfold strictLocalFibreRestriction
    infer_instance
  refine ⟨asIso (strictLocalFibreRestriction Λ i hi F), ?_⟩
  intro j
  exact strictLocalFibreRestriction_compatibility Λ sq.toCommSq t hpoint i hi hi' F j

end AlgebraicGeometry.Etale
