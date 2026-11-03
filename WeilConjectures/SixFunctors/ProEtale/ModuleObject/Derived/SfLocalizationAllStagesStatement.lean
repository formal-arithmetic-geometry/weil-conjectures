/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedLocalization.CondensedClosedLocalization
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteSerreIndConstructible
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence

/-!
# Closed-support localization at all coefficient stages

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/
sk-thm-sf-kunneth-verdier/sk-prop-sf-localization/prop-sf-localization-all-stages.md
and its `.proof.md`, clauses (1)--(4), (1')--(4') and the Weil paragraph
(blueprint: prop-sf-localization-all-stages).

The qualitative theorem uses the existing non-hollow `ClosedLocalization` interface.
The finite bound and integral reduction bounds are separate statements, so no
quantitative Tor bound is imposed at rational coefficients. The two exceptional
identifications use the published finite comparison and the current Brown restriction.
The Weil statement uses `StrictWeilCondensed.action` and the realization of the
current native Weil complexes, rather than the withdrawn `StrictWeil` model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- At finite coefficients the intrinsic normalized encoding and the source
library's etale-origin constructibility predicate agree. -/
private theorem sfFiniteEncodingConstructible
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (e : FiniteDiscreteOrdinary.Encoding A T)
    (K : _root_.DerivedCategory (FiniteDiscreteOrdinary.Internal A T)) :
    constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) T K ↔
      ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A))
        T (e.fixedDerived.functor.obj K) := by
  rw [(FiniteDiscreteOrdinary.encoding_constructibility A T e).2 K]
  constructor
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    obtain ⟨L, hL, he⟩ := fixedDerivedOrigin T (ULift.{u + 1} A)
      (e.fixedDerived.functor.obj K)
      (fun q ↦ (FiniteDiscreteOrdinary.ordinary_constructible_iff A T _).mp (hc q))
      a b (fun q hq ↦ hq.elim
        (fun h ↦ (_root_.DerivedCategory.isGE_iff _ a).mp ha q h)
        (fun h ↦ (_root_.DerivedCategory.isLE_iff _ b).mp hb q h))
    refine ⟨L, ⟨?_, ?_⟩, he⟩
    · obtain ⟨c, d, -, hz⟩ := hL.2
      exact ⟨⟨c, (_root_.DerivedCategory.isGE_iff L c).mpr
        (fun q hq ↦ hz q (.inl hq))⟩,
        ⟨d, (_root_.DerivedCategory.isLE_iff L d).mpr
          (fun q hq ↦ hz q (.inr hq))⟩⟩
    · intro q
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hL.1 q)
  · intro hK
    refine ⟨hK.bounded, fun q ↦ ?_⟩
    apply (FiniteDiscreteOrdinary.ordinary_constructible_iff A T _).mpr
    obtain ⟨L, hL, ⟨i⟩⟩ := hK
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj L) := hL.2 q
    exact isConstructible_of_iso
      (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
        ).mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
        (_root_.DerivedCategory.homologyFunctor _ q).mapIso i)
      (isConstructible_comparisonUpperStar_obj _)

/-- Restrict the actual normalized derived equivalence, using finite constructible
etale descent to identify its full subcategories. -/
private def sfFiniteEncodingEquivalence
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (e : FiniteDiscreteOrdinary.Encoding A T) :
    ConstantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) T ≌
      ProEtale.DerivedCategoryBoundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) T := by
  let P := constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) T
  let Q := ProEtale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let F := Q.lift (P.ι ⋙ e.fixedDerived.functor)
    (fun K ↦ (sfFiniteEncodingConstructible A T e K.obj).mp K.property)
  have : F.Full := by dsimp [F]; infer_instance
  have : F.Faithful := by dsimp [F]; infer_instance
  have : F.EssSurj := by
    constructor
    intro K
    let M := e.fixedDerived.inverse.obj K.obj
    have hM : P M := (sfFiniteEncodingConstructible A T e M).mpr
      (Q.prop_of_iso (e.fixedDerived.counitIso.app K.obj).symm K.property)
    exact ⟨⟨M, hM⟩, ⟨Q.isoMk (e.fixedDerived.counitIso.app K.obj)⟩⟩
  have : F.IsEquivalence := {}
  exact F.asEquivalence

/-- The exceptional functor of any localization is the source closed-support
right adjoint after normalized encoding. This is a natural comparison, obtained
from uniqueness of right adjoints on the full constructible categories. -/
private def sfFiniteClosedEncodingIso
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    (k : Type u) [Field k] (N : ℕ) (hN : (N : k) ≠ 0)
    (hA : (N : ULift.{u + 1} A) = 0)
    {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (L : ClosedLocalization (FiniteDiscreteOrdinary.coefficient A) i j)
    (eX : FiniteDiscreteOrdinary.Encoding A X)
    (eZ : FiniteDiscreteOrdinary.Encoding A Z) :
    L.exceptional ⋙ (constantModelBoundedConstructible
        (FiniteDiscreteOrdinary.coefficient A) Z).ι ⋙ eZ.fixedDerived.functor ≅
      (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X).ι ⋙
        eX.fixedDerived.functor ⋙
        (closedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) i j).rightDerivedFunctor := by
  let PX := constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X
  let PZ := constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Z
  let QX := ProEtale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  let QZ := ProEtale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) Z
  let EX := sfFiniteEncodingEquivalence A X eX
  let EZ := sfFiniteEncodingEquivalence A Z eZ
  let Fi := boundedConstructibleRightDerivedLowerStar i N hN hA s
  let Ri := boundedConstructibleClosedUpperShriek i j N hN hA s hij
  let sourceAdj := boundedConstructibleClosedUpperShriekAdjunction i j N hN hA s hij
  let comparison : L.closedPush ⋙ EX.functor ≅ EZ.functor ⋙ Fi :=
    ((QX.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft PZ.ι
        (FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A i eX eZ)))
  let adj := ((EZ.toAdjunction.comp sourceAdj).comp EX.symm.toAdjunction).ofNatIsoLeft
    (Iso.isoCompInverse (H := EX) comparison).symm
  let h : L.exceptional ≅ EX.functor ⋙ Ri ⋙ EZ.inverse :=
    L.adjunction.rightAdjointUniq adj
  let h' : L.exceptional ⋙ EZ.functor ≅ EX.functor ⋙ Ri :=
    Functor.isoWhiskerRight h EZ.functor ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft EX.functor
        (Functor.associator Ri _ _ ≪≫ Functor.isoWhiskerLeft Ri EZ.counitIso ≪≫
          Functor.rightUnitor Ri)
  exact Functor.isoWhiskerRight h' QZ.ι

/-- Restrict the current exact Frobenius action to Dbc. At field coefficients its
fixed pairs are the same structures as the current Dctf strict pairs.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationAction {T : Scheme.{u}} (g : T ≅ T) :
    ConstantModelBoundedConstructible Λ T ⥤ ConstantModelBoundedConstructible Λ T :=
  (constantModelBoundedConstructible Λ T).lift
    ((constantModelBoundedConstructible Λ T).ι ⋙ StrictWeilCondensed.action Λ g)
    (fun K ↦ ((StrictWeilCondensed.action_preserves Λ g K.obj).1).mpr K.property)

/-- Pullback composition across a commuting automorphism square. This is constructed
from the actual module-derived compositors and the exact Frobenius comparison.
Source: Weil paragraph, derived pullback composition
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationPullExchange {S T : Scheme.{u}} (f : S ⟶ T)
    (gS : S ≅ S) (gT : T ≅ T) (h : f ≫ gT.hom = gS.hom ≫ f) :
    moduleObjectDerivedPullback Λ f ⋙ StrictWeilCondensed.action Λ gS ≅
      StrictWeilCondensed.action Λ gT ⋙ moduleObjectDerivedPullback Λ f :=
  (Functor.isoWhiskerLeft (moduleObjectDerivedPullback Λ f)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ gS.hom)).symm ≪≫
    (leftDerivedUpperStarComp Λ gS.hom f).symm ≪≫
    Functor.leftDerivedFunctorNatIso _ (upperStarCongr Λ h.symm) ≪≫
    leftDerivedUpperStarComp Λ f gT.hom ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ gT.hom)
      (moduleObjectDerivedPullback Λ f)

/-- Forget only the finite-Tor membership proof of a current strict Weil pair.
The Frobenius isomorphism and carrier are unchanged.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationStrictPair {T : Scheme.{u}} (g : T ≅ T)
    (K : StrictWeilCondensed.Complex Λ g) :
    Endofunctor.IsoAlgebra (sfLocalizationAction Λ g) :=
  Endofunctor.IsoAlgebra.mk ⟨K.carrier.obj, K.carrier.property.1⟩
    ((constantModelBoundedConstructible Λ T).isoMk
      ((constantModelBoundedConstructible Λ T ⊓
        _root_.DerivedCategory.finiteTorAmplitude _).ι.mapIso K.str))

/-- Realize a native Weil complex by its specified localized Frobenius structure,
then forget its finite-Tor membership proof. This uses the current native-to-strict
comparison, with no assertion that realization is faithful.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationNativePair {T : Scheme.{u}} (g : T ≅ T)
    (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (K : StrictWeilCondensed.Native Λ g) :
    Endofunctor.IsoAlgebra (sfLocalizationAction Λ g) :=
  sfLocalizationStrictPair Λ g ((StrictWeilCondensed.nativeComparison Λ g ell hΛ).obj K)

private theorem sfLocalizationAction_equivalence {T : Scheme.{u}} (g : T ≅ T) :
    (sfLocalizationAction Λ g).IsEquivalence := by
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := StrictWeilCondensed.action_inverse Λ g
  let P := constantModelBoundedConstructible Λ T
  let F := sfLocalizationAction Λ g
  let G := sfLocalizationAction Λ g.symm
  let aa : F ⋙ G ≅ 𝟭 _ :=
    (P.fullyFaithfulι.whiskeringRight _).preimageIso (Functor.isoWhiskerLeft P.ι a)
  let bb : G ⋙ F ≅ 𝟭 _ :=
    (P.fullyFaithfulι.whiskeringRight _).preimageIso (Functor.isoWhiskerLeft P.ι b)
  exact Functor.IsEquivalence.mk' G aa.symm bb

private theorem sfLocalizationFiberSquare (D : WeilConjectures.FiniteFieldDatum.{u})
    {S T : Over (Spec (.of D.k₀))} (f₀ : S ⟶ T) :
    localizationFiberMap D f₀ ≫ (StrictWeilCondensed.modelFrobenius D T).hom =
      (StrictWeilCondensed.modelFrobenius D S).hom ≫ localizationFiberMap D f₀ := by
  let σ := @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
    (Fintype.ofFinite D.k₀) _ _ _
  change localizationFiberMap D f₀ ≫ D.galoisMap T.hom σ =
    D.galoisMap S.hom σ ≫ localizationFiberMap D f₀
  symm
  apply pullback.hom_ext
  · simp only [Category.assoc, localizationFiberMap, Over.pullback_map_left,
      pullback.lift_fst]
    rw [← Category.assoc, (D.galoisMap_projections S.hom σ).1,
      (D.galoisMap_projections T.hom σ).1]
    simp only [pullback.lift_fst]
  · simp only [Category.assoc, localizationFiberMap, Over.pullback_map_left,
      pullback.lift_snd]
    rw [(D.galoisMap_projections S.hom σ).2, (D.galoisMap_projections T.hom σ).2]
    simp

private theorem sfLocalizationFiberCartesian (D : WeilConjectures.FiniteFieldDatum.{u})
    {S T : Over (Spec (.of D.k₀))} (f : S ⟶ T) :
    IsPullback
      (pullback.fst S.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      (localizationFiberMap D f) f.left
      (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback T.hom _)
  · convert IsPullback.of_hasPullback S.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) using 1 <;>
      simp [localizationFiberMap, Over.pullback]
  · simp [localizationFiberMap, Over.pullback]

private theorem sfLocalization_orthogonal {X Z U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : DerivedCategory (supportModules Λ Z))
    (G : DerivedCategory (supportModules Λ U)) (m : ℤ) :
    Subsingleton (((moduleObjectDerivedPushforward Λ i).obj P) ⟦m⟧ ⟶
      (moduleObjectDerivedPushforward Λ j).obj G) := by
  let := closedSupport_lowerStarExact Λ i j hij
  let I := (lowerStar Λ i).mapDerivedCategory
  let J := (supportPullback Λ j).mapDerivedCategory
  have hz := (condensedSupportDerivedLocalization Λ i j hij).2.2.2.2.1
  have : Subsingleton ((shiftFunctor _ m).obj (I.obj P) ⟶
      (moduleObjectDerivedPushforward Λ j).obj G) :=
    Recollement.subsingleton_hom_shift I J (closedSupportOpenDerivedAdjunction Λ j)
      hz P G m
  let eI := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app P
  exact (((shiftFunctor _ m).mapIso eI).homCongr
    (Iso.refl ((moduleObjectDerivedPushforward Λ j).obj G))).subsingleton

private theorem sfLocalization_triangle_iso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (e₁ : F.obj T.obj₁ ≅ T.obj₁) (e₂ : F.obj T.obj₂ ≅ T.obj₂)
    (e₃ : F.obj T.obj₃ ≅ T.obj₃)
    (h₁ : F.map T.mor₁ ≫ e₂.hom = e₁.hom ≫ T.mor₁)
    (h₂ : F.map T.mor₂ ≫ e₃.hom = e₂.hom ≫ T.mor₂)
    (hsub : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃)) :
    ∃ e : F.mapTriangle.obj T ≅ T,
      e.hom.hom₁ = e₁.hom ∧ e.hom.hom₂ = e₂.hom ∧ e.hom.hom₃ = e₃.hom := by
  have := hsub
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj T) T (F.map_distinguished T hT) hT e₁.hom e₂.hom h₁
  have : Subsingleton ((F.mapTriangle.obj T).obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃) :=
    (((shiftFunctor C (1 : ℤ)).mapIso e₁).homCongr (Iso.refl T.obj₃)).subsingleton
  have hc : c = e₃.hom := Triangle.cancel_mor₂_of_subsingleton
    (F.map_distinguished T hT) (hc₂.trans h₂.symm)
  rw [hc] at hc₃
  exact ⟨Triangle.isoMk _ _ e₁ e₂ e₃ h₁ h₂ hc₃, rfl, rfl, rfl⟩

variable {Λ} {X Z U : Scheme.{u}} {i : Z ⟶ X} {j : U ⟶ X}

variable (Λ)

end AlgebraicGeometry.ProEtale.CondensedRing
