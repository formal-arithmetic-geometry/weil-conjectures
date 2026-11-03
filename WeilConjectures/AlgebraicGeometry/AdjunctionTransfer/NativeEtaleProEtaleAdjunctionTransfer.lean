/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityFiniteComparison.NativeFiniteAdjunctionRestrictions
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteBrownRestrictionForCompactification

/-! # Native etale to pro-etale adjunction transfer

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-et-proet/
det-sp-et-proet-adjunction-transfer.md and its adjacent proof
(blueprint: det-sp-et-proet-adjunction-transfer).

The equivalences and their quasi-inverses are arbitrary supplied data, normalized to
termwise comparison using the recorded coefficient encoding. No parent Compatibility
record, generation assertion, or adjunction-transfer conclusion is a hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.AdjunctionTransfer

open SmoothPurityFiniteComparison

/-- Full faithfulness of the normalized comparison, obtained from the specified D+ unit. -/
private def nativeComparisonFullyFaithful
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (T : Scheme.{u}) (enc : FiniteDiscreteOrdinary.Encoding A T)
    (e : (etaleProperty (ULift.{u + 1} A) T).FullSubcategory ≌
      ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) T)
    (ν : e.functor ⋙ (constantModelBoundedConstructible
        (FiniteDiscreteOrdinary.coefficient A) T ⊓
          fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).ι ⋙
        enc.fixedDerived.functor ≅
      (etaleProperty (ULift.{u + 1} A) T).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory) :
    e.functor.FullyFaithful := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let L := comparisonUpperStar B T
  have : IsIso (derivedComparisonAdjunctionPlus B T).unit :=
    isIso_compactSupportComparisonUnit T (ULift.{u + 1} A)
  let ff := (derivedComparisonAdjunctionPlus B T).fullyFaithfulLOfIsIsoUnit
  let ffEt : (etaleToPlus (ULift.{u + 1} A) T).FullyFaithful := by
    dsimp only [etaleToPlus]
    exact ObjectProperty.fullyFaithfulιOfLE _
  let ffp := ffEt.comp ff
  let ffa := ffp.comp (Functor.FullyFaithful.ofFullyFaithful _root_.DerivedCategory.Plus.ι)
  let iso := Functor.isoWhiskerLeft (etaleToPlus (ULift.{u + 1} A) T)
    L.mapDerivedCategoryPlusCompatibility
  exact ((ffa.ofIso iso).ofIso ν.symm).ofCompFaithful

section HomBijections
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The comparison Hom bijection with arbitrary target, using the chosen inverse. -/
private def comparisonTargetCore (e : C ≌ D) (ff : e.functor.FullyFaithful) :
    Adjunction.CoreHomEquiv e.functor e.inverse where
  homEquiv M N := (e.counitIso.app N).symm.homToEquiv.trans ff.homEquiv.symm
  homEquiv_naturality_left_symm f g := by
    simp [Functor.FullyFaithful.homEquiv, Functor.map_comp, Category.assoc]
  homEquiv_naturality_right f g := by
    change ff.preimage ((f ≫ g) ≫ e.counitIso.inv.app _) =
      ff.preimage (f ≫ e.counitIso.inv.app _) ≫ e.inverse.map g
    apply ff.map_injective
    simp only [Functor.map_comp, ff.map_preimage]
    simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
      congrArg (fun t ↦ f ≫ t) (e.counitIso.inv.naturality g)

/-- The source comparison Hom bijection, transported from a chosen representative. -/
private def comparisonSourceCore (e : C ≌ D) (ff : e.functor.FullyFaithful) :
    Adjunction.CoreHomEquiv e.inverse e.functor where
  homEquiv M N := ff.homEquiv.trans (e.counitIso.app M).homFromEquiv
  homEquiv_naturality_left_symm f g := by
    change ff.preimage (e.counitIso.hom.app _ ≫ (f ≫ g)) =
      e.inverse.map f ≫ ff.preimage (e.counitIso.hom.app _ ≫ g)
    apply ff.map_injective
    simp only [Functor.map_comp, ff.map_preimage]
    simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
      congrArg (fun t ↦ t ≫ g) (e.counitIso.hom.naturality f).symm
  homEquiv_naturality_right f g := by
    simp [Functor.FullyFaithful.homEquiv, Functor.map_comp, Category.assoc]

end HomBijections

/-- Native bounded constant-model constructibility is shift stable by cohomology
reindexing; finite Tor amplitude is shift stable by its proved well-definedness theorem.
This supplies step 3 of det-sp-et-proet-adjunction-transfer. -/
private theorem nativeProperty_stableUnderShift
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] (T : Scheme.{u}) :
    (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) T ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).IsStableUnderShift ℤ := by
  let Λ := FiniteDiscreteOrdinary.coefficient A
  let C := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)
  have hcons := (constantModelConstructibleFiniteTor_wellDefined Λ T).1
  have htor : (_root_.DerivedCategory.finiteTorAmplitude C).IsTriangulated :=
    (constantModelConstructibleFiniteTor_wellDefined Λ T).2.2.2.2.2.2.2.1
  refine ⟨fun n ↦ ⟨fun K hK ↦ ?_⟩⟩
  refine ⟨⟨_root_.DerivedCategory.TStructure.t.bounded.le_shift n K hK.1.1, ?_⟩,
    (_root_.DerivedCategory.finiteTorAmplitude C).le_shift n K hK.2⟩
  intro q
  exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ T)
    (((_root_.DerivedCategory.homologyFunctor C 0).shiftIso n q (q + n)
      (by omega)).app K).symm (hK.1.2 (q + n))

set_option maxHeartbeats 2000000 in
-- The counit calculation elaborates maps in the native derived module category.
/-- Transfer an etale Dctf adjunction to the native constant-model pro-etale Dctf and
identify it with the restriction of any supplied native Brown adjunction.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-et-proet/
det-sp-et-proet-adjunction-transfer.md, both paragraphs,
and det-sp-et-proet-adjunction-transfer.proof.md
(blueprint: det-sp-et-proet-adjunction-transfer).

Proof plan:
1. Compose adjEt with eY.toAdjunction and eX.symm.toAdjunction. Transport its left
functor along cf and the counit of eX. This uses Adjunction.comp and ofNatIsoLeft.
2. Expand the composite counit. Naturality of cf.inv and the equivalence triangle
identities cancel the source-equivalence terms. At eY(N), the inverse unit of eY
implements Q_Y nu_Y(N) = N and gives exactly the displayed three-factor formula.
3. The native Dctf predicate is bounded constant-model constructibility intersected
with finiteTorAmplitude. Its shifts again satisfy that predicate. Use the existing
constructibility comparison to identify the etale predicate in the supplied normalized
equivalences. No etale-origin predicate replaces the native pro-etale predicate.
4. For a supplied Brown adjunction on the native localizing closures, transpose the
transported counit to a map from the transported right adjoint into the Brown value.
On Hom from each shifted native Dctf generator this induces a bijection, by the two
adjunction Hom bijections and full faithfulness of the inclusions. Its cone belongs
to the localizing closure and is right orthogonal to every shifted generator. The
left orthogonal of the right orthogonal is localizing and contains the generators,
so the cone lies in both orthogonals, its identity vanishes, and the cone is zero.
Thus the map is an isomorphism. Repleteness gives the concluded native preservation hJ.
5. Restrict the Brown adjunction through ctfToLocalizing using restrictFullyFaithful;
its counit maps to the actual Brown counit. Apply rightAdjointUniq to this restricted
adjunction and adjPro. Its counit equation gives the stated ambient equality, and
the adjunction Hom bijection forces uniqueness of any isomorphism satisfying it.
-/
theorem nativeEtaleProEtaleAdjunctionTransfer_legacy
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0) (c : Compactification f)
    (encX : FiniteDiscreteOrdinary.Encoding A X)
    (encY : FiniteDiscreteOrdinary.Encoding A Y)
    (encZ : FiniteDiscreteOrdinary.Encoding A c.Z)
    (eX : (etaleProperty (ULift.{u + 1} A) X).FullSubcategory ≌
      ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) X)
    (eY : (etaleProperty (ULift.{u + 1} A) Y).FullSubcategory ≌
      ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) Y)
    (νX : eX.functor ⋙ (constantModelBoundedConstructible
        (FiniteDiscreteOrdinary.coefficient A) X ⊓
          fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).ι ⋙
        encX.fixedDerived.functor ≅
      (etaleProperty (ULift.{u + 1} A) X).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory)
    (νY : eY.functor ⋙ (constantModelBoundedConstructible
        (FiniteDiscreteOrdinary.coefficient A) Y ⊓
          fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).ι ⋙
        encY.fixedDerived.functor ≅
      (etaleProperty (ULift.{u + 1} A) Y).ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).mapDerivedCategory)
    (hEt : ∀ K, etaleProperty (ULift.{u + 1} A) X K →
      etaleProperty (ULift.{u + 1} A) Y
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj K))
    (hN : ∀ K,
      (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X K ∧
        _root_.DerivedCategory.finiteTorAmplitude _ K) →
      (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (FiniteDiscreteOrdinary.coefficient A) c).obj K) ∧
        _root_.DerivedCategory.finiteTorAmplitude _
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (FiniteDiscreteOrdinary.coefficient A) c).obj K)))
    (cf : etaleLowerShriek (ULift.{u + 1} A) c hEt ⋙ eY.functor ≅
      eX.functor ⋙ nativeCtfLowerShriek A c hN)
    (_hcf : ∀ K,
      encY.fixedDerived.functor.map ((cf.hom.app K).hom) =
        νY.hom.app ((etaleLowerShriek (ULift.{u + 1} A) c hEt).obj K) ≫
          unboundedDirectImageComparisonMap (ULift.{u + 1} A) c.g
            ((Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.i).mapDerivedCategory.obj K.obj) ≫
          (ProEtale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.g).rightDerivedFunctor.map
              ((openComparison A c.i).hom.app K.obj) ≫
          (ProEtale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).map (νX.inv.app K) ≫
          (encodingCompactSupportComparison A c encX encZ encY).inv.app
            ((eX.functor.obj K).obj))
    (G : (etaleProperty (ULift.{u + 1} A) Y).FullSubcategory ⥤
      (etaleProperty (ULift.{u + 1} A) X).FullSubcategory)
    (adjEt : etaleLowerShriek (ULift.{u + 1} A) c hEt ⊣ G) :
    ∃ adjPro : nativeCtfLowerShriek A c hN ⊣ (eY.inverse ⋙ G ⋙ eX.functor),
      (∀ N,
        adjPro.counit.app (eY.functor.obj N) =
          (nativeCtfLowerShriek A c hN).map
              (eX.functor.map (G.map (eY.unitIso.inv.app N))) ≫
            cf.inv.app (G.obj N) ≫ eY.functor.map (adjEt.counit.app N)) ∧
      (∀ (hLoc : ∀ K,
          localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X K →
          localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y
            ((CondensedRing.rightDerivedLowerShriekOfCompactification
              (FiniteDiscreteOrdinary.coefficient A) c).obj K))
        (J :
          (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y).FullSubcategory ⥤
          (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).FullSubcategory)
        (adjBrown : CondensedRing.localizingLowerShriek
          (FiniteDiscreteOrdinary.coefficient A) c hLoc ⊣ J),
        ∃ hJ : ∀ N : ConstantModelConstructibleFiniteTor
            (FiniteDiscreteOrdinary.coefficient A) Y,
            constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X
                (J.obj ((ctfToLocalizing A Y).obj N)).obj ∧
              _root_.DerivedCategory.finiteTorAmplitude _
                (J.obj ((ctfToLocalizing A Y).obj N)).obj,
          ∃! γ : (eY.inverse ⋙ G ⋙ eX.functor) ≅
              SmoothPurityFiniteComparison.brownRestriction A J hJ,
            ∀ N,
              (CondensedRing.rightDerivedLowerShriekOfCompactification
                (FiniteDiscreteOrdinary.coefficient A) c).map ((γ.hom.app N).hom) ≫
                  (adjBrown.counit.app ((ctfToLocalizing A Y).obj N)).hom =
                (adjPro.counit.app N).hom) := by
  classical
  let e := eX
  let ac : (etaleLowerShriek (ULift.{u + 1} A) c hEt) ⋙ eY.functor ⊣ eY.inverse ⋙ G :=
    adjEt.comp eY.toAdjunction
  let j : e.inverse ⋙ ((etaleLowerShriek (ULift.{u + 1} A) c hEt) ⋙ eY.functor) ≅
      nativeCtfLowerShriek A c hN :=
    Functor.isoWhiskerLeft e.inverse cf ≪≫
      (Functor.associator e.inverse e.functor (nativeCtfLowerShriek A c hN)).symm ≪≫
      Functor.isoWhiskerRight e.counitIso (nativeCtfLowerShriek A c hN) ≪≫
      Functor.leftUnitor (nativeCtfLowerShriek A c hN)
  let adjPro : nativeCtfLowerShriek A c hN ⊣
      eY.inverse ⋙ G ⋙ eX.functor :=
    (e.symm.toAdjunction.comp ac).ofNatIsoLeft j
  refine ⟨adjPro, ?_, ?_⟩
  · intro N
    rw [Adjunction.ofNatIsoLeft_counit]
    change j.inv.app (eX.functor.obj (G.obj (eY.inverse.obj (eY.functor.obj N)))) ≫
      (e.symm.toAdjunction.comp ac).counit.app (eY.functor.obj N) = _
    rw [Adjunction.comp_counit_app]
    change j.inv.app _ ≫
      ((etaleLowerShriek (ULift.{u + 1} A) c hEt) ⋙ eY.functor).map (e.unitIso.inv.app _) ≫
      ac.counit.app (eY.functor.obj N) = _
    dsimp [j]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    change (nativeCtfLowerShriek A c hN).map (e.counitIso.inv.app _) ≫
      cf.inv.app _ ≫ ((etaleLowerShriek (ULift.{u + 1} A) c hEt) ⋙ eY.functor).map
        (e.unitIso.inv.app _) ≫ ac.counit.app _ = _
    rw [← cf.inv.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc]
    simp only [e, Equivalence.counitIso_functor_comp, Functor.id_obj]
    rw [(nativeCtfLowerShriek A c hN).map_id, Category.id_comp]
    dsimp [ac]
    rw [Adjunction.comp_counit_app]
    change cf.inv.app _ ≫ eY.functor.map (adjEt.counit.app _) ≫
      eY.counitIso.hom.app (eY.functor.obj N) = _
    rw [eY.counit_app_functor]
    rw [← eY.functor.map_comp]
    have hn := adjEt.counit.naturality (eY.unitIso.inv.app N)
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    erw [← hn]
    rw [eY.functor.map_comp]
    erw [← cf.inv.naturality_assoc]
    rfl
  · intro hLoc J adjBrown
    have : (constantModelBoundedConstructible
        (FiniteDiscreteOrdinary.coefficient A) X).IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined
        (FiniteDiscreteOrdinary.coefficient A) X).2.1
    have hJ : ∀ N : (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y ⊓
        fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).FullSubcategory,
        (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X ⊓
          fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)
            ((J.obj ((ctfToLocalizing A Y).obj N)).obj) := by
      have : (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X ⊓
        fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).IsStableUnderShift ℤ :=
        nativeProperty_stableUnderShift A X
      exact rightAdjoint_preserves_generators
        (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X ⊓
          fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)
        (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y ⊓
          fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (FiniteDiscreteOrdinary.coefficient A) c)
        hN hLoc (eY.inverse ⋙ G ⋙ eX.functor) adjPro J adjBrown
    let commL : ctfToLocalizing A X ⋙ CondensedRing.localizingLowerShriek
        (FiniteDiscreteOrdinary.coefficient A) c hLoc ≅
        nativeCtfLowerShriek A c hN ⋙ ctfToLocalizing A Y := Iso.refl _
    let commR : ctfToLocalizing A Y ⋙ J ≅
        SmoothPurityFiniteComparison.brownRestriction A J hJ ⋙ ctfToLocalizing A X :=
      Iso.refl _
    let adjSmall : nativeCtfLowerShriek A c hN ⊣
        SmoothPurityFiniteComparison.brownRestriction A J hJ :=
      adjBrown.restrictFullyFaithful
        (ObjectProperty.fullyFaithfulιOfLE _)
        (ObjectProperty.fullyFaithfulιOfLE _) commL commR
    have hc (N : (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y ⊓
        fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).FullSubcategory) :
        (adjSmall.counit.app N).hom =
          (adjBrown.counit.app ((ctfToLocalizing A Y).obj N)).hom := by
      have hh := adjBrown.map_restrictFullyFaithful_counit_app
        (ObjectProperty.fullyFaithfulιOfLE _)
        (ObjectProperty.fullyFaithfulιOfLE _) commL commR N
      change (ctfToLocalizing A Y).map (adjSmall.counit.app N) =
        𝟙 _ ≫ (CondensedRing.localizingLowerShriek
          (FiniteDiscreteOrdinary.coefficient A) c hLoc).map (𝟙 _) ≫
          adjBrown.counit.app ((ctfToLocalizing A Y).obj N) at hh
      rw [(CondensedRing.localizingLowerShriek
        (FiniteDiscreteOrdinary.coefficient A) c hLoc).map_id] at hh
      simp only [Category.id_comp] at hh
      exact congrArg (fun g ↦ g.hom) hh
    refine ⟨hJ, adjPro.rightAdjointUniq adjSmall, ?_, ?_⟩
    · intro N
      rw [← hc]
      exact congrArg (fun g ↦ g.hom)
        (adjPro.rightAdjointUniq_hom_app_counit adjSmall N)
    · intro γ hγ
      apply Iso.ext
      apply NatTrans.ext
      funext N
      apply (adjSmall.homEquiv _ _).symm.injective
      rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
      apply (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y ⊓
        fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).ι.map_injective
      change (CondensedRing.rightDerivedLowerShriekOfCompactification
          (FiniteDiscreteOrdinary.coefficient A) c).map
        ((γ.hom.app N).hom) ≫ (adjSmall.counit.app N).hom = _
      rw [hc]
      exact hγ N


set_option maxHeartbeats 2000000 in
-- The Hom chain and its counit transport traverse several concrete derived equivalences.
end AlgebraicGeometry.ProEtale.AdjunctionTransfer
