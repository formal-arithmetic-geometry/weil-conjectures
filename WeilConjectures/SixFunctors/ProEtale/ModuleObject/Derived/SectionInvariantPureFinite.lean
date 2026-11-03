/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralExceptionalRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalRestrictionGlue
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import all WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingSmoothLocalFormula
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Finite pure-dimensional native dualizing invertibility

Source: current blueprint def-pur-section-invariant, constant-dimension step of the
Picard assertion (blueprint: lem-pur-section-pure-finite-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem invertible_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hC : ∀ i : C.I₀, IsInvertible ((L((C.f i)^*⟦Λ⟧)).obj M)) :
    IsInvertible M := by
  let _ : BraidedCategory (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
    (DerivedCategory.nonempty_braidedCategory (Mod
      (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))).some
  have hv : IsIso ((ihom.ev M).app (𝟙_ _)) := by
    apply isIso_of_forall_isIso_leftDerivedUpperStar_map C
    intro i
    have : WeaklyEtale (C.f i) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ ⟨i⟩
    let F := L((C.f i)^*⟦Λ⟧)
    let _ := monoidal_leftDerivedUpperStar Λ (C.f i)
    let _ : BraidedCategory (DerivedCategory
        (Mod (Sheaf (ProEt.topology (C.X i)) Ab.{u + 1})
          (condensedRingObj Λ (C.X i)))) :=
      (DerivedCategory.nonempty_braidedCategory (Mod
        (Sheaf (ProEt.topology (C.X i)) Ab.{u + 1})
        (condensedRingObj Λ (C.X i)))).some
    have := (hC i).isIso_ev (F.obj (𝟙_ _))
    have := isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale Λ (C.f i) M
    have : IsIso (Functor.LaxMonoidal.μ F M _ ≫ F.map ((ihom.ev M).app (𝟙_ _))) := by
      rw [← Functor.LaxMonoidal.ihomComparison_ev]
      infer_instance
    exact IsIso.of_isIso_comp_left (Functor.LaxMonoidal.μ F M _) _
  let _ := hv
  exact (isInvertible_iff_of_braided M).2
    ⟨(ihom M).obj (𝟙_ _), ⟨asIso ((ihom.ev M).app (𝟙_ _))⟩⟩

private theorem invertible_of_iso
    {C : Type*} [Category C] [MonoidalCategory C] {M N : C}
    (e : M ≅ N) (hN : IsInvertible N) : IsInvertible M := by
  obtain ⟨P, ⟨a⟩, ⟨b⟩⟩ := hN
  exact ⟨P, ⟨tensorIso e (Iso.refl _) ≪≫ a⟩,
    ⟨tensorIso (Iso.refl _) e ≪≫ b⟩⟩

private theorem unit_shift_invertible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (n : ℤ) :
    IsInvertible ((shiftFunctor (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) n).obj (𝟙_ _)) := by
  let U := 𝟙_ (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)))
  refine ⟨U⟦-n⟧, ⟨?_⟩, ⟨?_⟩⟩
  · exact _root_.DerivedCategory.shiftTensorShiftIso _ U U n (-n) ≪≫
      (shiftFunctor _ (n + -n)).mapIso (λ_ U) ≪≫
      (shiftFunctorZero' _ (n + -n) (by simp)).app U
  · exact _root_.DerivedCategory.shiftTensorShiftIso _ U U (-n) n ≪≫
      (shiftFunctor _ (-n + n)).mapIso (λ_ U) ≪≫
      (shiftFunctorZero' _ (-n + n) (by simp)).app U

private theorem finite_continuous_invertible
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (hf : ∀ K, localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X K →
      localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y
        ((rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj A) c).obj K))
    (G : (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y).FullSubcategory ⥤
      (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X).FullSubcategory)
    (adj : localizingLowerShriek (Profinite.continuousCoefficientRingObj A) c hf ⊣ G)
    (N : (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y).FullSubcategory)
    (hN : N.obj = 𝟙_ _) (r : ℕ) (hr : ((ell ^ r : ℕ) : ULift.{u + 1} A) = 0) :
    IsInvertible (G.obj N).obj := by
  classical
  let Λ := Profinite.continuousCoefficientRingObj A
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  let cb : Compactification.BoundaryCompactification f :=
    ⟨⟨c, c.quasiCompact_openImmersion inferInstance⟩⟩
  obtain ⟨C, hC⟩ :=
    localizingExceptionalAdjoint_smoothLocalFormula ell k A f cb hf G adj d r hr
  let S : ObjectProperty (localizingClosureProEtale Λ Y).FullSubcategory :=
    fun K ↦ (constantModelBoundedConstructible Λ Y ⊓
      fun L ↦ _root_.DerivedCategory.finiteTorAmplitude _ L) K.obj
  let Ns : S.FullSubcategory := ⟨N, by
    change (constantModelBoundedConstructible Λ Y ⊓
      fun L ↦ _root_.DerivedCategory.finiteTorAmplitude _ L) N.obj
    rw [hN]
    exact condensedCoefficientUnit_mem Λ Y⟩
  apply invertible_of_cover Λ X (C.weaken Scheme.etalePrecoverage_le_proetalePrecoverage)
  intro i
  obtain ⟨e⟩ := (hC i).2
  let j := C.f i
  let P := (upperStar Λ f).mapDerivedCategory
  let J := (upperStar Λ j).mapDerivedCategory
  let ep : P.obj N.obj ≅ 𝟙_ _ :=
    P.mapIso (eqToIso hN) ≪≫
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ f).app (𝟙_ _)).symm ≪≫
      leftDerivedUpperStarUnitIso Λ f
  let ej : J.obj (𝟙_ _) ≅ 𝟙_ _ :=
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app (𝟙_ _)).symm ≪≫
      leftDerivedUpperStarUnitIso Λ j
  apply invertible_of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app _)
  apply invertible_of_iso (e.app Ns)
  apply invertible_of_iso ((shiftFunctor _ (2 * (d : ℤ))).mapIso (J.mapIso ep ≪≫ ej))
  exact unit_shift_invertible Λ (C.X i) _

private theorem invertible_reflected
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence] (M : C)
    (hM : IsInvertible (F.obj M)) : IsInvertible M := by
  obtain ⟨P, ⟨e⟩, ⟨e'⟩⟩ := hM
  let Q := F.objPreimage P
  let j : F.obj Q ≅ P := F.objObjPreimageIso P
  refine ⟨Q, ⟨F.preimageIso ?_⟩, ⟨F.preimageIso ?_⟩⟩
  · exact (Functor.Monoidal.μIso F M Q).symm ≪≫
      tensorIso (Iso.refl _) j ≪≫ e ≪≫ Functor.Monoidal.εIso F
  · exact (Functor.Monoidal.μIso F Q M).symm ≪≫
      tensorIso j (Iso.refl _) ≪≫ e' ≪≫ Functor.Monoidal.εIso F

@[instance_reducible]
private noncomputable def coefficientTransportMonoidal
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    (shriekCoefficientTransport e T).Monoidal := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : IsIso (coefficientMap e.inv.hom T) :=
    inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
  let H := Mod.comap (D := Sheaf (ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.inv.hom T)
  let : H.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso (coefficientMap e.inv.hom T)).functor.IsEquivalence
  let : H.Monoidal := Mod.monoidal_comap _
  exact CategoryTheory.ExactMonoidalEquivalenceDerived.derivedEquivalenceMonoidal H

set_option maxHeartbeats 2000000 in
-- The closure equivalences and adjunction conjugation require dependent reductions.
private theorem coefficient_transport_invertible
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G)
    (hp : ∀ (h' : ∀ K, localizingClosureProEtale Λ' X K →
          localizingClosureProEtale Λ' Y
            ((rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).obj K))
        (G' : (localizingClosureProEtale Λ' Y).FullSubcategory ⥤
          (localizingClosureProEtale Λ' X).FullSubcategory)
        (_adj' : localizingLowerShriek Λ' c.obj.obj h' ⊣ G')
        (N' : (localizingClosureProEtale Λ' Y).FullSubcategory),
      Nonempty (N'.obj ≅ 𝟙_ _) → IsInvertible (G'.obj N').obj)
    (N : (localizingClosureProEtale Λ Y).FullSubcategory) (hN : N.obj = 𝟙_ _) :
    IsInvertible (G.obj N).obj := by
  classical
  let _ (T : Scheme.{u}) := (shriekCoefficientIso_transport e T).1
  let _ (T : Scheme.{u}) := (shriekCoefficientIso_transport e.symm T).1
  let d (T : Scheme.{u}) := (shriekCoefficientTransport e T).asEquivalence
  have hlocal (T : Scheme.{u}) : (localizingClosureProEtale Λ' T).inverseImage
      (shriekCoefficientTransport e T) = localizingClosureProEtale Λ T := by
    let S := shriekCoefficientCtf (Λ := Λ) T
    let S' := shriekCoefficientCtf (Λ := Λ') T
    obtain ⟨_, htri, hiso, _, _, _⟩ := brownHypotheses_structural Λ T
    obtain ⟨_, htri', hiso', _, _, _⟩ := brownHypotheses_structural Λ' T
    let _ := htri
    let _ := hiso
    let _ := htri'
    let _ := hiso'
    have hf : localizingClosureProEtale Λ T ≤
        (localizingClosureProEtale Λ' T).inverseImage (shriekCoefficientTransport e T) :=
      map_closure (shriekCoefficientTransport e T) S S'
        (fun K hK ↦ constantModelCtf_coefficientIso e T ⟨K, hK⟩)
    have hb : localizingClosureProEtale Λ' T ≤
        (localizingClosureProEtale Λ T).inverseImage (shriekCoefficientTransport e.symm T) :=
      map_closure (shriekCoefficientTransport e.symm T) S' S
        (fun K hK ↦ constantModelCtf_coefficientIso e.symm T ⟨K, hK⟩)
    funext K
    apply propext
    refine ⟨fun hK ↦ ?_, hf K⟩
    exact (localizingClosureProEtale Λ T).prop_of_iso
      ((transportCompIso e T).app K) (hb _ hK)
  obtain ⟨_, htriX, hisoX, _, _, _⟩ := brownHypotheses_structural Λ' X
  obtain ⟨_, htriY, hisoY, _, _, _⟩ := brownHypotheses_structural Λ' Y
  let _ := htriX
  let _ := htriY
  let _ := hisoX
  let _ := hisoY
  let EX := (d X).congrFullSubcategory (hlocal X)
  let EY := (d Y).congrFullSubcategory (hlocal Y)
  let F := localizingLowerShriek Λ c.obj.obj h
  have h' : ∀ K, localizingClosureProEtale Λ' X K → localizingClosureProEtale Λ' Y
      ((rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).obj K) := by
    intro K hK
    let L := (d X).inverse.obj K
    have hL : localizingClosureProEtale Λ X L := by
      rw [← hlocal X]
      exact (localizingClosureProEtale Λ' X).prop_of_iso
        ((d X).counitIso.app K).symm hK
    exact (localizingClosureProEtale Λ' Y).prop_of_iso
      ((shriekCoefficientCompactificationIso e c).app L ≪≫
        (rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).mapIso
          ((d X).counitIso.app K))
      (by
        change ((localizingClosureProEtale Λ' Y).inverseImage
          (shriekCoefficientTransport e Y))
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj L)
        rw [hlocal Y]
        exact h L hL)
  let F' := localizingLowerShriek Λ' c.obj.obj h'
  let comp : F ⋙ EY.functor ≅ EX.functor ⋙ F' :=
    ((localizingClosureProEtale Λ' Y).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (localizingClosureProEtale Λ X).ι
        (shriekCoefficientCompactificationIso e c))
  let left : (EX.inverse ⋙ F) ⋙ EY.functor ≅ F' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EX.inverse comp ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EX.counitIso F' ≪≫ F'.leftUnitor
  let G' := EY.inverse ⋙ G ⋙ EX.functor
  let adj' : F' ⊣ G' :=
    ((EX.symm.toAdjunction.comp adj).comp EY.toAdjunction).ofNatIsoLeft left
  let _ := coefficientTransportMonoidal e Y
  have hN' : Nonempty ((EY.functor.obj N).obj ≅ 𝟙_ _) :=
    ⟨(shriekCoefficientTransport e Y).mapIso (eqToIso hN) ≪≫
      (Functor.Monoidal.εIso (shriekCoefficientTransport e Y)).symm⟩
  have hv := hp h' G' adj' (EY.functor.obj N) hN'
  let i : G'.obj (EY.functor.obj N) ≅ EX.functor.obj (G.obj N) :=
    EX.functor.mapIso (G.mapIso (EY.unitIso.app N).symm)
  let _ := coefficientTransportMonoidal e X
  apply invertible_reflected (shriekCoefficientTransport e X) (G.obj N).obj
  exact invertible_of_iso
    ((localizingClosureProEtale Λ' X).ι.mapIso i).symm hv

/-- For any finite commutative ell-primary coefficient ring, the pure-dimensional
native exceptional unit is tensor invertible.

Source: def-pur-section-invariant, constant-dimension invertibility step
(blueprint: lem-pur-section-pure-finite-invertible).
Proof: lift the finite carrier to the scheme universe and transport the given coefficient
presentation. The finite localizing smooth formula gives an etale cover on which the
exceptional unit is the coefficient unit shifted by twice the dimension. The opposite
shift is its inverse. Pullback commutes with internal Hom and detects isomorphisms, so
invertibility of the evaluation descends. Conjugating the adjunction along the strong
monoidal coefficient equivalence returns the original coefficient presentation. The
argument allows the zero ring and an empty source. -/
theorem section_pure_finite_invertible
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (A : Type) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] [Finite A]
    (hA : ∃ r : ℕ, ∀ x : A, (ell ^ r) • x = 0)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (a : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (hf : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adj : localizingLowerShriek Λ c hf ⊣ G)
    (N : (localizingClosureProEtale Λ Y).FullSubcategory) (hN : N.obj = 𝟙_ _) :
    IsInvertible (G.obj N).obj := by
  classical
  obtain ⟨r, hr⟩ := hA
  obtain ⟨b⟩ := AdmissibleTriangulated.finiteCoefficientLiftIso A
  let e := a ≪≫ b
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  let cb : Compactification.BoundaryCompactification f :=
    ⟨⟨c, c.quasiCompact_openImmersion inferInstance⟩⟩
  apply coefficient_transport_invertible e cb hf G adj ?_ N hN
  intro h' G' adj' N' hN'
  obtain ⟨_, _, hiso, _, _, _⟩ :=
    brownHypotheses_structural (Profinite.continuousCoefficientRingObj (ULift.{u} A)) Y
  let _ := hiso
  obtain ⟨eN⟩ := hN'
  let N0 : (localizingClosureProEtale (Profinite.continuousCoefficientRingObj
      (ULift.{u} A)) Y).FullSubcategory :=
    ⟨𝟙_ _, ObjectProperty.prop_of_iso _ eN N'.property⟩
  apply invertible_of_iso ((localizingClosureProEtale _ X).ι.mapIso
    (G'.mapIso ((localizingClosureProEtale _ Y).isoMk (X := N') (Y := N0) eN)))
  exact finite_continuous_invertible ell k (ULift.{u} A) f d c
    h' G' adj' N0 rfl r (by
      apply ULift.ext
      apply ULift.ext
      change ((ell ^ r : ℕ) : A) = 0
      simpa only [nsmul_eq_mul, mul_one] using hr 1)

end AlgebraicGeometry.ProEtale.CondensedRing
