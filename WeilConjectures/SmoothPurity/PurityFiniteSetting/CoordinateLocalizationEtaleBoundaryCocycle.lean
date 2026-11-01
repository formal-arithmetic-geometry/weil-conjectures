/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback

/-! # Injective cocycle data for the coordinate support boundary

Source: Milne, Lectures on Etale Cohomology, Section 9, Example 9.5
(blueprint: lem-pur-coordinate-localization-etale-boundary-cocycle).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- A bounded-below injective cocycle model for the coordinate support boundary. -/
structure CoordinateLocalizationEtaleWitness
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    (M : CoordinateBoundaryModel P T) where
  I : CochainComplex.Plus
    (Sheaf (Line T).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
  injective : ∀ n : ℤ, Injective (I.obj.X n)
  e : DerivedCategory.Plus.Q.obj I ≅ P.coordinateEtaleInput h (Line T)
  x : ((etaleSupportHomPair P (zeroSection T)).complex I).cycles 2
  f : (etaleSupportHomPair P (zeroSection T)).supported ⟶ I.obj.X 2
  hf : f ≫ I.obj.d 2 3 = 0
  boundary :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 2).map
        ((etaleSupportHomPair P (zeroSection T)).sections.rightDerivedFunctorPlus.map e.hom)
        ((etaleSupportHomPair P (zeroSection T)).cycleClass I 2 x) =
      -M.alphaEtale P h aT
  cocycle : f = f

/-- The injective resolution and cocycle model exist for the coordinate boundary.

Source: Milne, Section 9, Example 9.5, pp. 66--67.
Proof: choose a bounded-below injective representative of the coordinate input;
represent the normalized support boundary by a cycle and lift its cocycle through
the support kernel inclusion.  The support-boundary normalization identifies its
class with `-M.alphaEtale`.
(blueprint: lem-pur-coordinate-localization-etale-boundary-cocycle).
-/
theorem coordinateLocalization_etale_boundary_cocycle
    (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (M : CoordinateBoundaryModel P T)
    (N : SupportedHomCocycleNormalization
      (etaleSupportHomPair P (zeroSection T)).topology P.Coefficient
      (etaleSupportHomPair P (zeroSection T)).isTerminal
      (etaleSupportHomPair P (zeroSection T)).restriction
      (etaleSupportHomPair P (zeroSection T)).supported
      (etaleSupportHomPair P (zeroSection T)).constantRestriction) :
    Nonempty (CoordinateLocalizationEtaleWitness P h T aT M) := by
  classical
  let S := etaleSupportHomPair P (zeroSection T)
  let K := P.coordinateEtaleInput h (Line T)
  obtain ⟨n, hn⟩ := K.2
  letI : K.IsGE n := (K.isGE_ι_obj_iff n).mp hn
  obtain ⟨I₀, hI₀, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let I := (InjectiveObject.ι (Sheaf S.topology (ModuleCat.{u + 1} P.Coefficient))).mapCochainComplexPlus.obj I₀
  letI hI (r : ℤ) : Injective (I.obj.X r) := (I₀.obj.X r).2
  let E := Sheaf.supportSequenceModelIso S.topology
    (ModuleCat.{u + 1} P.Coefficient) S.sections I
    (DerivedCategory.Plus.Q.obj I) (Iso.refl _) 2
  let H := (S.sections.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 2)
  let z := H.map e.inv (-M.alphaEtale P h aT)
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective
    (((S.complex I).homologyπ 2))).mp inferInstance (E.inv z)
  obtain ⟨f, ⟨hfx, ⟨hdf, _⟩⟩, _⟩ := N.cocycle I I (𝟙 I) 2 x
  refine ⟨⟨I, hI, e, x, f, hdf, ?_, rfl⟩⟩
  dsimp [S, H, z, E, SupportHomPair.cycleClass]
  rw [hx]
  change (ConcreteCategory.hom (H.map e.hom))
      ((ConcreteCategory.hom E.hom) ((ConcreteCategory.hom E.inv)
        ((ConcreteCategory.hom (H.map e.inv)) (-M.alphaEtale P h aT)))) = _
  rw [Iso.inv_hom_id_apply, ← ConcreteCategory.comp_apply, ← H.map_comp, e.inv_hom_id,
    H.map_id, ConcreteCategory.id_apply]

end WeilConjectures.PurityFiniteSetting
