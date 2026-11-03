/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ComparisonBrownExplicit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenScalarSourceUnit
import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenScalarSupportComparison
import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenScalarOrdinaryCounit
import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenBoundedCounitCoordinates
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification

/-!
# Scalar transport of open unit counits

Source: smooth purity transport Steps 2--3, expanded as open normalization
Step 5 (blueprint: lem-pur-open-scalar-unit-counit).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormalizedUnitTrace
open Scheme CondensedRing PurityTransport ExplicitSmoothComparison

private local instance openScalarUnitCounitBundledComm
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) :
    IsCommMonObj (CommMon.toMon (c.bundled.{u} ell)).X := by
  change IsCommMonObj (c.obj ell)
  infer_instance

set_option maxHeartbeats 4000000 in
-- The bundled coefficient categories require substantial definitional equality checking.
private theorem integralClosureMap_listed (ell : ℕ) [Fact ell.Prime] :
    IsListedScalarCoefficientMap ell (integralClosureMap.{u} ell) := by
  classical
  let E : PadicAlgCl.FiniteIntermediateField ell := ⟨⊥, inferInstance⟩
  obtain ⟨eq, ez, heq, hez, hiq, hiqi, hiz, hizi, q, z, hq, hqi, hz, hzi, hsq⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} ell
  let e : (Coefficient.integers : Coefficient ell).bundled.{u} ell ≅
      latticeIntegralRing ell E := (CommMon.fullyFaithfulForget₂Mon _).preimageIso z
  let t : (Coefficient.integers : Coefficient ell).bundled.{u} ell ⟶
      scalarSixFieldRing ell E :=
    ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Profinite.padicIntToBotFiniteIntermediateField ell)
        (Profinite.continuous_padicIntToBotFiniteIntermediateField ell))⟩⟩
  have hi : e.hom ≫ scalarSixIntegralToField ell E = t := by
    ext S x
    change ULift.{u + 1} C(S.unop, ℤ_[ell]) at x
    rcases x with ⟨x⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    change (((z.hom.hom.hom.app S) (ULift.up x)).down s : E) =
      Profinite.padicIntToBotFiniteIntermediateField ell (x s)
    have hz' : ((z.hom.hom.hom.app S) (ULift.up x)).down s = ez (x s) :=
      hz S.unop x s
    exact (congrArg (fun y : PadicAlgCl.integers ell
        (⊥ : IntermediateField ℚ_[ell] (PadicAlgCl ell)) ↦ (y : E)) hz').trans (congrArg
      (fun f : ℤ_[ell] →+* PadicAlgCl.integers ell
          (⊥ : IntermediateField ℚ_[ell] (PadicAlgCl ell)) ↦ (f (x s) : E)) hez)
  have h : integralClosureMap ell =
      e.hom ≫ scalarSixIntegralToField ell E ≫
        (⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩ :
          scalarSixFieldRing ell E ⟶ latticeClosureRing ell) ≫ (Iso.refl _).hom := by
    simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    rw [hi]
    rfl
  rw [h]
  exact IsListedScalarCoefficientMap.iso e (Iso.refl _)
    (IsListedScalarCoefficientMap.comp
      (IsListedScalarCoefficientMap.localization (ell := ell) E)
      (IsListedScalarCoefficientMap.algebraicClosure (ell := ell) E))

private theorem scalar_unit_counit_of_source
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (H₁ : D₁ ⥤ C₁)
    (S : C₀ ⥤ C₁) (T : D₀ ⥤ D₁) (β : F₀ ⋙ T ⟶ S ⋙ F₁)
    {U₀ : D₀} {U₁ : D₁} (u : T.obj U₀ ≅ U₁)
    {L₀ M₀ : C₀} {M₁ : C₁} (v₀ : L₀ ≅ M₀) (v₁ : H₁.obj U₁ ≅ M₁)
    (σ : S.obj L₀ ⟶ H₁.obj (T.obj U₀)) (w : S.obj M₀ ⟶ M₁)
    (e₀ : F₀.obj L₀ ⟶ U₀)
    (e₁ : F₁.obj (H₁.obj (T.obj U₀)) ⟶ T.obj U₀)
    (e₁' : F₁.obj (H₁.obj U₁) ⟶ U₁)
    (hscalar : T.map e₀ = β.app L₀ ≫ F₁.map σ ≫ e₁)
    (hnat : F₁.map (H₁.map u.hom) ≫ e₁' = e₁ ≫ u.hom)
    (hsource : S.map v₀.inv ≫ σ ≫ H₁.map u.hom ≫ v₁.hom = w) :
    T.map (F₀.map v₀.inv ≫ e₀) ≫ u.hom =
      β.app M₀ ≫ F₁.map w ≫ F₁.map v₁.inv ≫ e₁' := by
  have hb : T.map (F₀.map v₀.inv) ≫ β.app L₀ =
      β.app M₀ ≫ F₁.map (S.map v₀.inv) := β.naturality v₀.inv
  calc
    _ = T.map (F₀.map v₀.inv) ≫ β.app L₀ ≫
        F₁.map σ ≫ e₁ ≫ u.hom := by
      rw [T.map_comp, hscalar]
      simp only [Category.assoc]
    _ = β.app M₀ ≫ F₁.map (S.map v₀.inv) ≫
        F₁.map σ ≫ F₁.map (H₁.map u.hom) ≫ e₁' := by
      rw [← Category.assoc (T.map (F₀.map v₀.inv)), hb]
      simp only [Category.assoc, hnat]
    _ = β.app M₀ ≫ F₁.map w ≫ F₁.map v₁.inv ≫ e₁' := by
      have hw : S.map v₀.inv ≫ σ ≫ H₁.map u.hom = w ≫ v₁.inv := by
        rw [← hsource]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      simp only [← F₁.map_comp_assoc]
      rw [hw, F₁.map_comp]

set_option maxHeartbeats 4000000 in
-- The concrete functor comparisons require substantial definitional equality checking.
/-- Scalar compatibility gives an equality with the explicit transport function,
and this same function preserves the ordinary open counit. Neither assertion
assumes the geometric normalization of the integral smooth counit.

Source: smooth purity transport coefficient compatibility and open normalization
Step 5 (blueprint: lem-pur-open-scalar-unit-counit).

Proof: factor the integral coefficient map through the integers of the bottom finite
subfield, then its fraction field, then the closure; the existing coefficient
identification proves that this is a listed map. Apply ScalarCompatible to this
map and the unit. Naturality of the closure adjunction counit moves the scalar
unit isomorphism through the source. The zero-line normalization then rewrites
the scalar equation as T(unitCounit_0) followed by the scalar unit equals the
support comparison followed by F_1 of the source scalar unit and unitCounit_1.
The support comparison in chosen-to-trivial coordinates has an explicit left
inverse W, obtained from the open scalar isomorphism and the two unit comparisons.
Cancel with W to obtain exactly transportIntegralOpenTrace, proving (1).
For (2), substitute the ordinary integral trace in the transport function and
cancel its inverse compactification comparison. The ordinary scalar open-counit
equation leaves the closure ordinary trace. The bounded counit coordinate
comparison identifies this last morphism with boundedOpenUnitTrace. -/
theorem openScalarUnitCounit
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (b : Family ell k) (hscalar : ScalarCompatible ell k b)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (unitCounit ell b .closure j =
      transportIntegralOpenTrace ell j (unitCounit ell b .integers j)) ∧
    (transportIntegralOpenTrace ell j
      (ordinaryUnitTrace ell .integers (integersAdmissible ell) j) =
        boundedOpenUnitTrace ell j) := by
  classical
  let a := integralClosureMap ell
  let F₀ := CondensedRing.rightDerivedLowerShriekOfCompactification
    ((Coefficient.integers : Coefficient ell).obj ell) (compactificationOverField j)
  let F₁ := CondensedRing.rightDerivedLowerShriekOfCompactification
    ((Coefficient.closure : Coefficient ell).obj ell) (compactificationOverField j)
  let H₁ := (Coefficient.closure : Coefficient ell).smoothSource ell j.left 0
  let S := scalarSixChange a X.left
  let T := scalarSixChange a Y.left
  let J := actualOpen ((Coefficient.closure : Coefficient ell).obj ell) j.left
  let C₀ := openUnitComparison ell .integers (integersAdmissible ell) j
  let C₁ := openUnitComparison ell .closure (closureAdmissible ell) j
  let e := CondensedRing.derivedOpenImmersionShriekIso
        (Λ := (Coefficient.integers : Coefficient ell).obj ell)
        (Λ' := (Coefficient.closure : Coefficient ell).obj ell) a.hom.hom j.left
  let uX := scalarUnitIso ell X.left
  let uY := scalarUnitIso ell Y.left
  let β := scalarSupportMap a (compactificationOverField j)
  let W := C₁.hom ≫ J.map uX.inv ≫ e.inv.app (𝟙_ _) ≫ T.map C₀.inv
  have hlisted : IsListedScalarCoefficientMap ell a := integralClosureMap_listed ell
  obtain ⟨ha, hb⟩ := hscalar .integers .closure a hlisted
  obtain ⟨p, hp⟩ := hb (datum j 0)
  let K₀ : (Coefficient.integers : Coefficient ell).ctf ell Y.left :=
    ⟨𝟙_ _, smoothTraceUnit_mem ell .integers Y.left⟩
  obtain ⟨hK, hs⟩ := hp K₀
  let K₁ : (Coefficient.closure : Coefficient ell).ctf ell Y.left := ⟨_, hK⟩
  let U₁ : (Coefficient.closure : Coefficient ell).ctf ell Y.left :=
    ⟨𝟙_ _, smoothTraceUnit_mem ell .closure Y.left⟩
  have hn : F₁.map (H₁.map uY.hom) ≫ (b .closure (datum j 0)).trace U₁ =
      (b .closure (datum j 0)).trace K₁ ≫ uY.hom := by
    exact congrArg (fun f ↦ f.hom)
      ((b .closure (datum j 0)).adjunction.counit.naturality
        (ObjectProperty.homMk uY.hom : K₁ ⟶ U₁))
  have ht := scalar_unit_counit_of_source F₀ F₁ H₁ S T β uY
    (unitSource ell .integers j.left 0 ≪≫ zeroLine ell .integers X.left)
    (unitSource ell .closure j.left 0 ≪≫ zeroLine ell .closure X.left)
    (sourceScalar ell a j.left 0 ha p (𝟙_ _)) uX.hom
    ((b .integers (datum j 0)).trace K₀)
    ((b .closure (datum j 0)).trace K₁)
    ((b .closure (datum j 0)).trace U₁) hs hn
    (openScalarSourceUnit ell j ha p)
  have htrace : T.map (unitCounit ell b .integers j) ≫ uY.hom =
      β.app (𝟙_ _) ≫ F₁.map uX.hom ≫ unitCounit ell b .closure j := by
    simpa only [unitCounit, unitTrace, datum, F₀, F₁, K₀, U₁, Iso.trans_inv,
      Functor.map_comp, Category.assoc] using ht
  have hsupp : T.map C₀.hom ≫ e.hom.app (𝟙_ _) ≫ J.map uX.hom =
      β.app (𝟙_ _) ≫ F₁.map uX.hom ≫ C₁.hom :=
    openScalarSupportComparison ell j
  have hW : W ≫ β.app (𝟙_ _) ≫ F₁.map uX.hom = 𝟙 _ := by
    apply (cancel_mono C₁.hom).1
    simp only [Category.assoc, Category.id_comp]
    rw [← hsupp]
    simp only [W, Category.assoc, ← T.map_comp_assoc, Iso.inv_hom_id,
      T.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    rw [← J.map_comp, Iso.inv_hom_id, J.map_id, Category.comp_id]
  constructor
  · change unitCounit ell b .closure j =
      C₁.hom ≫ J.map uX.inv ≫ e.inv.app (𝟙_ _) ≫
        T.map (C₀.inv ≫ unitCounit ell b .integers j) ≫ uY.hom
    calc
      _ = W ≫ T.map (unitCounit ell b .integers j) ≫ uY.hom := by
        rw [htrace]
        simp only [← Category.assoc, hW, Category.id_comp]
      _ = _ := by simp only [W, T.map_comp, Category.assoc]
  · calc
      _ = ordinaryUnitTrace ell .closure (closureAdmissible ell) j := by
        unfold transportIntegralOpenTrace ordinaryUnitTrace
        simp only [Iso.inv_hom_id_assoc]
        exact congrArg (C₁.hom ≫ ·) (openScalarOrdinaryCounit ell j)
      _ = boundedOpenUnitTrace ell j := openBoundedCounitCoordinates ell j

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
