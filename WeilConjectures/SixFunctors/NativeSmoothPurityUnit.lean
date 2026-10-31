/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTraceUnit
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # The normalized purity comparison at the unit in coefficient coordinates

Source: the purity and trace paragraph of sk-thm-sf-identification.proof.md.
(blueprint: lem-sf-native-smooth-purity-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor CategoryTheory.TwoSquare

namespace AlgebraicGeometry.ProEtale.CondensedRing
open PurityTransport

private theorem scalar_ctf {A B : ScalarSixRing.{u}} (e : A ≅ B)
    (X : Scheme.{u}) (K : ConstantModelConstructibleFiniteTor A.X X) :
    (constantModelBoundedConstructible B.X X ⊓ DerivedCategory.finiteTorAmplitude _)
      ((scalarSixChange e.hom X).obj K.obj) := by
  let eM := (CommMon.forget₂Mon _).mapIso e
  have : IsIso eM.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map eM.hom))
  have : IsIso (coefficientMap (Λ := A.X) (Λ' := B.X) e.hom.hom.hom X) := by
    change IsIso ((upperStarFromPoint X).map eM.hom.hom)
    infer_instance
  have : (Mod.comap (asIso (coefficientMap (Λ := A.X) (Λ' := B.X)
      e.hom.hom.hom X)).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have : (Mod.extendScalars
      (coefficientMap (Λ := A.X) (Λ' := B.X) e.hom.hom.hom X)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv
      (coefficientMap (Λ := A.X) (Λ' := B.X) e.hom.hom.hom X)).symm
  have hi : inv (coefficientMap (Λ := A.X) (Λ' := B.X) e.hom.hom.hom X) =
      coefficientMap (Λ := B.X) (Λ' := A.X) e.inv.hom.hom X := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← coefficientMap_comp]
    change coefficientMap ((Mon.forget _).map (eM.hom ≫ eM.inv)) X = _
    rw [Iso.hom_inv_id]
    exact coefficientMap_id X
  let q : scalarSixChange e.hom X ≅
      (Mod.comap (coefficientMap (Λ := B.X) (Λ' := A.X) e.inv.hom.hom X)).mapDerivedCategory :=
    (Mod.extendScalars (coefficientMap (Λ := A.X) (Λ' := B.X) e.hom.hom.hom X)
      ).leftDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso
        (Mod.extendScalarsIsoComapInv
          (coefficientMap (Λ := A.X) (Λ' := B.X) e.hom.hom.hom X) ≪≫ Mod.comapCongr hi)
  have := (constantModelConstructibleFiniteTor_wellDefined B.X X).2.1
  have := (constantModelConstructibleFiniteTor_wellDefined B.X X).2.2.2.1
  exact ObjectProperty.prop_of_iso _ (q.app K.obj).symm
    (constantModelCtf_coefficientIso eM X K)

private def scalar_domain {A B : ScalarSixRing.{u}} (e : A ≅ B) (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor A.X X ⥤ ConstantModelConstructibleFiniteTor B.X X :=
  (constantModelBoundedConstructible B.X X ⊓ DerivedCategory.finiteTorAmplitude _).lift
    ((constantModelBoundedConstructible A.X X ⊓ DerivedCategory.finiteTorAmplitude _).ι ⋙
      scalarSixChange e.hom X) (scalar_ctf e X)

private theorem scalar_domain_equivalence {A B : ScalarSixRing.{u}}
    (e : A ≅ B) (X : Scheme.{u}) : (scalar_domain e X).IsEquivalence := by
  have hφ : IsIso (coefficientMap (Λ := A.X) (Λ' := B.X) e.hom.hom.hom X) := by
    change IsIso ((upperStarFromPoint X).map e.hom.hom.hom)
    infer_instance
  have : (Mod.comap (coefficientMap (Λ := A.X) (Λ' := B.X)
      e.hom.hom.hom X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have : (scalarSixChange e.hom X).IsEquivalence :=
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := A.X) (Λ' := B.X) e.hom.hom.hom X)
      ).isEquivalence_left_of_isEquivalence_right
  have : (scalar_domain e X).Faithful := by unfold scalar_domain; infer_instance
  have : (scalar_domain e X).Full := by unfold scalar_domain; infer_instance
  have : (scalar_domain e X).EssSurj := by
    constructor
    intro K
    let q := (scalarSixTower e.inv e.hom X) ≪≫
      eqToIso (congrArg (fun a ↦ scalarSixChange a X) e.inv_hom_id) ≪≫ scalarChangeUnit B X
    exact ⟨(scalar_domain e.symm X).obj K,
      ⟨ObjectProperty.isoMk _ (q.app K.obj)⟩⟩
  exact { }

set_option maxHeartbeats 800000 in
-- The mate calculation elaborates both restricted adjunctions and their ambient derived functors.
set_option maxRecDepth 4000 in
/-- The integration-normalized source line identifies with every Brown exceptional
unit, with its specified counit composite equal to the normalized smooth trace.
Source: blueprint sk-thm-sf-identification, purity and counit normalization
(blueprint: lem-sf-native-smooth-purity-unit).

Proof: restrict scalar extension along the coefficient isomorphism to Dctf.
Restriction along its inverse proves preservation, and scalar association and
identity comparison show that the restricted functors are equivalences. The
inverse of the prescribed compact-support comparison has an invertible right
mate between the normalized purity adjunction and the given Brown adjunction.
Evaluate that mate at the coefficient unit and compose with the source unitor,
scalar-shift comparison and scalar-unit isomorphism. The mate counit equation,
naturality of compact-support comparison and of the Brown counit give exactly
the trace composite in smoothTraceUnitOfCoefficientIso. Every comparison uses
the displayed normalization; no new choice of trace is made. Zero coefficients,
the empty source, and relative dimension zero are included. -/
theorem native_smoothPurity_unit (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (Λ : ScalarSixRing.{u}) (c : Coefficient ell) (e : c.bundled.{u} ell ≅ Λ)
    (s : SmoothDatum D)
    (hs : (constantModelBoundedConstructible Λ.X s.Y.left ⊓
      DerivedCategory.finiteTorAmplitude _) (𝟙_ _))
    (R : ScalarExceptionalAdjoint Λ s.compactification) :
    ∃ γ : (smoothTraceCoefficientLine ell Λ c e s.X.left s.dim) ⟦2 * (s.dim : ℤ)⟧ ≅
        (R.upper.obj ⟨𝟙_ _, hs⟩).obj,
      (rightDerivedLowerShriekOfCompactification Λ.X s.compactification).map γ.hom ≫
          R.counit ⟨𝟙_ _, hs⟩ = smoothTraceUnitOfCoefficientIso ell Λ c e D hEll s := by
  let A := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c s
  let P := support ell c s.compactification A.support_closed
  let Q := source ell c s.map s.dim A.source_closed
  let U : c.ctf ell s.Y.left := ⟨𝟙_ _, smoothTraceUnit_mem ell c s.Y.left⟩
  let S := scalar_domain e s.X.left
  let T := scalar_domain e s.Y.left
  let _ := scalar_domain_equivalence e s.X.left
  let _ := scalar_domain_equivalence e s.Y.left
  let α : P ⋙ T ≅ S ⋙ R.lower := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      (@asIso _ _ _ _ ((scalarCompactSupportMap e.hom s.compactification.i
        s.compactification.g).app K.obj)
        (smoothTraceCoefficientSupport_isIso ell Λ c e s.compactification K.obj)))
    (fun f ↦ ObjectProperty.hom_ext _
      ((scalarCompactSupportMap e.hom s.compactification.i
        s.compactification.g).naturality f.hom))
  let β := mateEquiv A.adjunction R.restrictedAdjunction (TwoSquare.mk _ _ _ _ α.inv)
  have : IsIso β.natTrans := isIso_mateEquiv_of_isEquivalence
    A.adjunction R.restrictedAdjunction (TwoSquare.mk _ _ _ _ α.inv)
  let b := ((constantModelBoundedConstructible Λ.X s.X.left ⊓
    DerivedCategory.finiteTorAmplitude _).ι).mapIso ((asIso β.natTrans).app U)
  let _ := scalarSixChangeMonoidal e.hom s.Y.left
  let _ := smoothTraceCoefficientCommShift ell Λ c e s.X.left
  let v : T.obj U ≅ ⟨𝟙_ _, hs⟩ := ObjectProperty.isoMk _
    (Functor.Monoidal.εIso (scalarSixChange e.hom s.Y.left)).symm
  let γ := (((scalarSixChange e.hom s.X.left).commShiftIso (2 * (s.dim : ℤ))).app
      ((DerivedCategory.singleFunctor _ 0).obj (c.line ell s.X.left s.dim))).symm ≪≫
    (scalarSixChange e.hom s.X.left).mapIso (smoothTraceUnitSource ell c D s).symm ≪≫
    b ≪≫ ((constantModelBoundedConstructible Λ.X s.X.left ⊓
      DerivedCategory.finiteTorAmplitude _).ι).mapIso (R.upper.mapIso v)
  refine ⟨γ, ?_⟩
  have hb := mateEquiv_counit A.adjunction R.restrictedAdjunction
    (TwoSquare.mk _ _ _ _ α.inv) U
  have hv := R.restrictedAdjunction.counit.naturality v.hom
  have hα := (scalarCompactSupportMap e.hom s.compactification.i
    s.compactification.g).naturality (smoothTraceUnitSource ell c D s).inv
  let F := rightDerivedLowerShriekOfCompactification Λ.X s.compactification
  let F₀ := rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification
  let V := (scalarSixChange e.hom s.Y.left)
  let W := (scalarSixChange e.hom s.X.left)
  let (M : c.derived ell s.X.left) : IsIso
      ((scalarCompactSupportMap e.hom s.compactification.i
        s.compactification.g).app M) :=
    smoothTraceCoefficientSupport_isIso ell Λ c e s.compactification M
  have hb₀ := congrArg (fun f ↦ f.hom) hb
  change F.map b.hom ≫ R.counit (T.obj U) =
    inv ((scalarCompactSupportMap e.hom s.compactification.i
      s.compactification.g).app ((c.smoothSource ell s.map s.dim).obj U.obj)) ≫
        V.map (A.trace U) at hb₀
  have hv₀ := congrArg (fun f ↦ f.hom) hv
  change F.map (((constantModelBoundedConstructible Λ.X s.X.left ⊓
    DerivedCategory.finiteTorAmplitude _).ι).map (R.upper.map v.hom)) ≫
      R.counit ⟨𝟙_ _, hs⟩ = R.counit (T.obj U) ≫ v.hom.hom at hv₀
  have := smoothTraceCoefficientSupport_isIso ell Λ c e s.compactification
    (c.derivedLine ell s.X.left s.dim)
  have := smoothTraceCoefficientSupport_isIso ell Λ c e s.compactification
    ((c.smoothSource ell s.map s.dim).obj U.obj)
  have hα₀ : F.map (W.map (smoothTraceUnitSource ell c D s).inv) ≫
      inv ((scalarCompactSupportMap e.hom s.compactification.i
        s.compactification.g).app ((c.smoothSource ell s.map s.dim).obj U.obj)) =
    inv ((scalarCompactSupportMap e.hom s.compactification.i
      s.compactification.g).app (c.derivedLine ell s.X.left s.dim)) ≫
      V.map (F₀.map (smoothTraceUnitSource ell c D s).inv) := by
    apply (cancel_epi ((scalarCompactSupportMap e.hom s.compactification.i
      s.compactification.g).app (c.derivedLine ell s.X.left s.dim))).1
    apply (cancel_mono ((scalarCompactSupportMap e.hom s.compactification.i
      s.compactification.g).app ((c.smoothSource ell s.map s.dim).obj U.obj))).1
    change V.map (F₀.map (smoothTraceUnitSource ell c D s).inv) ≫
      (scalarCompactSupportMap e.hom s.compactification.i s.compactification.g).app
        ((c.smoothSource ell s.map s.dim).obj U.obj) =
      (scalarCompactSupportMap e.hom s.compactification.i s.compactification.g).app
        (c.derivedLine ell s.X.left s.dim) ≫
        F.map (W.map (smoothTraceUnitSource ell c D s).inv) at hα
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc,
      IsIso.inv_hom_id, IsIso.hom_inv_id, Category.comp_id, Category.id_comp] using hα.symm
  dsimp only [γ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv]
  simp only [Functor.map_comp, Category.assoc]
  rw [hv₀, reassoc_of% hb₀, reassoc_of% hα₀]
  simp only [smoothTraceUnitOfCoefficientIso, smoothTraceUnitCanonical,
    Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
