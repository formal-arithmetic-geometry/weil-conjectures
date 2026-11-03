/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap

/-! # Tensor cohomology vanishing on one scalar-perfect chart

Source: the internal-Hom stability proof, paragraphs 2--3, and Stacks Project,
Tags 08JH, 08JJ, 08G1 and 07A4.
(blueprint: lem-sfb-scalar-perfect-chart-tor-vanishing).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 1600000 in
-- Derived monoidal comparisons require substantial instance synthesis.
set_option synthInstance.maxHeartbeats 400000 in
/-- A fixed bounded scalar-perfect model kills tensor cohomology off its window,
and its relative dual kills tensor cohomology off the reflected window, after
restriction to that one chart. No cover, compactness or admissibility is assumed.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/
  sec-the-remaining-operations/sk-thm-sf-ctf-stability/
  sk-thm-sf-ctf-stability-internal-hom.proof.md,
paragraph 2 final sentence and paragraph 3 parenthetical; Stacks 08JH, 08JJ,
08G1 and 07A4. (blueprint: lem-sfb-scalar-perfect-chart-tor-vanishing).

Proof: apply point pullback to F. It preserves the displayed finite-free
retractions and zero terms, so the resulting chart complex E is supported in
[a,b] and has dualizable, hence flat, terms. Its signed termwise right dual is
supported in [-b,-a] and also has flat terms. The native bounded-dual pairing
identifies Q(E.rightDual) with the internal Hom from Q(E) to the derived unit.
The bounded-flat tensor computation gives both universal Tor windows.
Weakly etale derived pullback preserves tensor and the unit and commutes with
internal Hom, by its exact extension-by-zero left adjoint and projection formula.
Use the supplied chart representation to identify the two pulled-back complexes
with Q(E) and Q(E.rightDual). Exact pullback commutes with homology and degree-zero
objects. Its underlying-sheaf comparison gives precisely the asserted abelian
inverse-image vanishings, for every test module, including rank zero, zero
complexes, empty charts and arbitrary integral endpoints. -/
theorem scalarPerfect_chart_tor_vanishing
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] {S U : Scheme.{u}} (g : U ⟶ S) [WeaklyEtale g]
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S)))
    (F : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) ℤ)
    (a b : ℤ) (hab : a ≤ b)
    (hF : ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n))
    (hproj : ∀ n : ℤ, ∃ r : ℕ, ∃ i : F.X n ⟶ Mod.finiteFree Λ.X r,
      ∃ p : Mod.finiteFree Λ.X r ⟶ F.X n, i ≫ p = 𝟙 (F.X n))
    (hG : ((upperStarFromPoint U).mapMod Λ.X).PreservesZeroMorphisms)
    (hrep : letI := hG
      Nonempty (((CondensedRing.upperStar Λ.X g).mapDerivedCategory).obj P ≅
        DerivedCategory.Q.obj
          ((((upperStarFromPoint U).mapMod Λ.X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F))) :
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S))
      (q : ℤ),
      (q < a ∨ b < q → IsZero ((upperStar Ab.{u + 1} g).obj
        (((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.derivedTensor Λ.X S).obj P).obj
            ((DerivedCategory.singleFunctor _ 0).obj N))).X))) ∧
      (q < -b ∨ -a < q → IsZero ((upperStar Ab.{u + 1} g).obj
        (((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.derivedTensor Λ.X S).obj
            (((CondensedRing.derivedHom Λ.X S).obj (Opposite.op P)).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (Mod.regular (condensedRingObj Λ.X S))))).obj
            ((DerivedCategory.singleFunctor _ 0).obj N))).X))) := by
  classical
  have _ := hab
  let H := (upperStarFromPoint U).mapMod Λ.X
  have := hG
  let E : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U)) ℤ :=
    (H.mapHomologicalComplex (.up ℤ)).obj F
  have hEa : E.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact H.map_isZero (hF n (Or.inl hn))
  have hEb : E.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact H.map_isZero (hF n (Or.inr hn))
  have : PreservesFiniteLimits (upperStarFromPoint U) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have hHadd : H.Additive := Functor.additive_of_preserves_binary_products H
  let eunit : H.obj (Mod.regular Λ.X) ≅ Mod.regular (condensedRingObj Λ.X U) :=
    Mod.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id,
        MonoidalCategory.whiskerLeft_id, Category.id_comp])
  have hd (n : ℤ) : IsDualizable (E.X n) := by
    obtain ⟨r, i, p, hip⟩ := hproj n
    let e := Mod.finiteFreeIsoMap H eunit r
    let ret : Retract (E.X n) (Mod.finiteFree (condensedRingObj Λ.X U) r) :=
      { i := H.map i ≫ e.hom
        r := e.inv ≫ H.map p
        retract := by
          change (H.map i ≫ e.hom) ≫ (e.inv ≫ H.map p) = 𝟙 (H.obj (F.X n))
          simp only [Category.assoc, Iso.hom_inv_id_assoc, ← H.map_comp, hip, H.map_id] }
    exact IsDualizable.of_retract ret (isDualizable_biproduct_unit r)
  let : ∀ n, HasRightDual (E.X n) := fun n ↦ (hd n).some
  have hd' (n : ℤ) : IsDualizable (E.rightDual.X n) :=
    ⟨{ rightDual := E.X (-n)
       exact := (BraidedCategory.exactPairing_swap (E.X (-n)) (E.X (-n))ᘁ :) }⟩
  have ht := DerivedCategory.torAmplitudeIn_Q_obj_of_flat E a b (fun n ↦ (hd n).flat)
  have htd := DerivedCategory.torAmplitudeIn_Q_obj_of_flat E.rightDual (-b) (-a)
    (fun n ↦ (hd' n).flat)
  obtain ⟨ep⟩ := DerivedCategory.nonempty_exactPairing_Q_obj_rightDual E a b
  let := ep
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
    (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U))
  let : ExactPairing (DerivedCategory.Q.obj E.rightDual) (DerivedCategory.Q.obj E) :=
    BraidedCategory.exactPairing_swap _ _
  let ed : (ihom (DerivedCategory.Q.obj E)).obj (𝟙_ _) ≅
      DerivedCategory.Q.obj E.rightDual := ihomObjUnitIso _ _
  let M := CondensedRing.upperStar Λ.X g
  let L := M.leftDerivedFunctor
  obtain ⟨eP⟩ := hrep
  let e : L.obj P ≅ DerivedCategory.Q.obj E :=
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X g).app P ≪≫ eP
  have hc := CondensedRing.isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale
    Λ.X g P
  let O := (DerivedCategory.singleFunctor _ 0).obj
    (Mod.regular (condensedRingObj Λ.X S))
  let eO : L.obj O ≅ 𝟙_ _ :=
    L.mapIso (DerivedCategory.singleFunctorObjUnitIso _) ≪≫
      CondensedRing.leftDerivedUpperStarUnitIso Λ.X g
  let eD : L.obj ((ihom P).obj O) ≅ DerivedCategory.Q.obj E.rightDual :=
    (asIso ((Functor.LaxMonoidal.ihomComparison L P).natTrans.app O)) ≪≫
      (ihom (L.obj P)).mapIso eO ≪≫
      (MonoidalClosed.internalHom.mapIso e.symm.op).app (𝟙_ _) ≪≫ ed
  have vanish (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S)))
      (q : ℤ) (hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj (L.obj K))) :
      IsZero ((upperStar Ab.{u + 1} g).obj
        (((DerivedCategory.homologyFunctor _ q).obj K).X)) := by
    let eH := (DerivedCategory.homologyFunctor _ q).mapIso
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X g).app K) ≪≫
        ((M.mapDerivedCategoryHomologyFunctorIso q).app K).symm
    exact ((Mod.forget _).map_isZero (hz.of_iso eH.symm)).of_iso
      (CondensedRing.upperStarObjXIso Λ.X g _).symm
  intro N q
  let eN : L.obj ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      (DerivedCategory.singleFunctor _ 0).obj (M.obj N) :=
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X g).app _ ≪≫
      (M.mapDerivedCategorySingleFunctor 0).app N
  have tensorVanish (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S)))
      (T : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ.X U)))
      (c d : ℤ) (eK : L.obj K ≅ T)
      (hT : DerivedCategory.torAmplitudeIn _ c d T) (hq : q < c ∨ d < q) :
      IsZero ((upperStar Ab.{u + 1} g).obj
        (((DerivedCategory.homologyFunctor _ q).obj
          (K ⊗ (DerivedCategory.singleFunctor _ 0).obj N)).X)) := by
    apply vanish
    let et : L.obj (K ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
        T ⊗ (DerivedCategory.singleFunctor _ 0).obj (M.obj N) :=
      ((CondensedRing.leftDerivedUpperStarTensorIso Λ.X g).app K).app _ ≪≫
        tensorIso eK eN
    have hbound := hT (M.obj N)
    have := hbound.1
    have := hbound.2
    have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (T ⊗ (DerivedCategory.singleFunctor _ 0).obj (M.obj N))) := by
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ c q hq
      · exact DerivedCategory.isZero_of_isLE _ d q hq
    exact hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso et)
  exact ⟨fun hq ↦ tensorVanish P _ a b e ht hq,
    fun hq ↦ tensorVanish ((ihom P).obj O) _ (-b) (-a) eD htd hq⟩

end AlgebraicGeometry.ProEtale
