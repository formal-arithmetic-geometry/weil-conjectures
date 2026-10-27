/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Targets.VectorBundlePurity
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.Compactification.Affine
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude
import Sheaf.AlgebraicGeometry.EtaleChartCompactSupportNormalization
import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
import Sheaf.AlgebraicGeometry.ArbitraryFieldOpenComplementControl
import Sheaf.AlgebraicGeometry.EtalePullbackTwistTorWindow
import Sheaf.AlgebraicGeometry.EtaleScalarFlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Exceptional inverse image on a closed affine-space chart

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Locality and Charts; closed-chart supplement
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The literal ordinary etale functor pi^*(-)(r)[2r]. Its Tate sheaf is the recorded
finite etale twist, and tensor and shift act on the entire derived category.
Source: main-20261015, exceptional-reduction Locality and Charts, closed-chart supplement
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation). -/
def closedChartTwistedPullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (V : Scheme.{u}) (r : ℕ) :
    DerivedCategoryModule A V ⥤
      DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin r)) V) :=
  (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V)).mapDerivedCategory ⋙
    derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin r)) V)
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin r)) V) N A hA r)) ⋙
    shiftFunctor _ (2 * (r : ℤ))

/-- The specified compact-support comparison Fu_! -> v_! H i_*: compose, use the
chart equality, decompose, and use the canonical proper and open normalizations.
Source: main-20261015, exceptional-reduction Locality and Charts, proof steps 2--4
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation). -/
def closedChartCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ Y) (v : V ⟶ Y) (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V)
    [IsOpenImmersion u] [IsOpenImmersion v] [IsClosedImmersion i]
    [QuasiCompact u] [QuasiCompact v] [QuasiCompact f]
    [QuasiCompact (u ≫ f)]
    [HasCompactification u] [HasCompactification v] [HasCompactification f]
    [HasCompactification (u ≫ f)]
    [HasCompactification (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V))]
    [HasCompactification ((i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v)]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      (R(lowerStar (ModuleCat.{u + 1} A) i) ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekIsoOfIsOpenImmersion A u).symm _ ≪≫
    unboundedEtaleLowerShriekCompIso A u f ≪≫
    unboundedEtaleLowerShriekCongr A h ≪≫
    (unboundedEtaleLowerShriekCompIso A
      (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) v).symm ≪≫
    Functor.isoWhiskerRight
      (unboundedEtaleLowerShriekCompIso A i
        (AffineSpace (ULift.{u} (Fin r)) V ↘ V)).symm _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) i) _) _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerShriekIsoOfIsOpenImmersion A v)

/-- Counit normalization of the comparison of two composite right adjoints.
This predicate expands to the unique natural isomorphism and its objectwise counit equation;
keeping the chart functors as parameters prevents conversion from unfolding their constructions.
Source: main-20261015, exceptional-reduction Locality and Charts, pasted counit calculation
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation). -/
def counitNormalizedChartComparison
    {C D E B H : Type*}
    [Category* C] [Category* D] [Category* E] [Category* B] [Category* H]
    {Lu : C ⥤ D} {Ru : D ⥤ C} {F : D ⥤ E} {R : E ⥤ D}
    {Li : C ⥤ B} {Ri : B ⥤ C} {Lπ : B ⥤ H} {Rπ : H ⥤ B}
    {Lv : H ⥤ E} {Rv : E ⥤ H}
    (au : Lu ⊣ Ru) (af : F ⊣ R) (ai : Li ⊣ Ri) (aπ : Lπ ⊣ Rπ)
    (av : Lv ⊣ Rv) (e : Lu ⋙ F ≅ (Li ⋙ Lπ) ⋙ Lv) : Prop :=
    ∃! t : R ⋙ Ru ≅ (Rv ⋙ Rπ) ⋙ Ri, ∀ X,
      e.hom.app (Ru.obj (R.obj X)) ≫ ((Li ⋙ Lπ) ⋙ Lv).map (t.hom.app X) ≫
        ((ai.comp aπ).comp av).counit.app X = (au.comp af).counit.app X

/-- The assertion after installing only consequences of the geometric and coefficient
hypotheses. The purity adjunction is quantified universally: in particular the assertion
applies to the adjunction normalized by the integration counit of vector-bundle purity.
Existence is included, so no purity or boundedness assumption is imposed on an input.
The counit equation determines the natural isomorphism uniquely for that specified
adjunction, and is invariant under changing the chosen ambient right adjoint.
Source: main-20261015, exceptional-reduction Locality and Charts, proof steps 1--8
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation). -/
structure ClosedChartExceptionalAssertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    {X Y U V : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ Y) (v : V ⟶ Y) (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V)
    [IsOpenImmersion u] [IsOpenImmersion v] [IsClosedImmersion i]
    [QuasiCompact u] [QuasiCompact v] [QuasiCompact f] [QuasiCompact (u ≫ f)]
    [HasCompactification u] [HasCompactification v] [HasCompactification f]
    [HasCompactification (u ≫ f)]
    [HasCompactification (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V))]
    [HasCompactification ((i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v)]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) : Prop where
  purityAdjunction : Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r)
  comparison : ∀ (F : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ F)
    (adjπ : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r),
    counitNormalizedChartComparison
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u)
      adjF (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))) adjπ
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v)
      (closedChartCompactSupportComparison A u f v r i h)
  preservation : ∀ L : DerivedCategoryModule A Y,
    DerivedCategory.isBoundedConstructible A Y L →
    (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L) →
    DerivedCategory.isBoundedConstructible A U
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        ((closedChartTwistedPullback A N hA V r).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj L))) ∧
    ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A U a b
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        ((closedChartTwistedPullback A N hA V r).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj L)))

/-- Install the Noetherian, compactification and finite-coefficient instances that follow
from the stated field, finite-type and affine-open hypotheses; then assert the closed-chart
comparison and preservation. None of these consequences is an extra input.
Source: main-20261015, exceptional-reduction closed-chart supplement, proof step 1
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation). -/
def ClosedChartExceptionalPreservation
    (ell : ℕ) [Fact ell.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] {X Y U V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsAffine U] [IsAffine V] (u : U ⟶ X) (v : V ⟶ Y)
    [IsOpenImmersion u] [IsOpenImmersion v] (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V) [IsClosedImmersion i]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) : Prop :=
  letI : Finite (Padic.coefficientExtensionRing ell E n) :=
    Padic.finite_coefficientExtensionRing ell E n hn
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : IsNoetherian X := {}
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  letI : IsNoetherian Y := {}
  letI : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion u
  letI : IsNoetherian U := {}
  letI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  letI : IsNoetherian V := {}
  letI : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  letI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  letI : IsSeparated (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  letI : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
  ∃ hA : ((ell ^ n : ℕ) : Padic.coefficientExtensionRing ell E n) = 0,
    ClosedChartExceptionalAssertion (Padic.coefficientExtensionRing ell E n)
      (ell ^ n) hA u f v r i h

-- Normalize comparison and reassociation on abstract functors before instantiating them
-- with the large derived-functor constructions of the chart.
private theorem normalizedUniq {C D : Type*} [Category* C] [Category* D]
    {F J : C ⥤ D} {R S : D ⥤ C} (a : F ⊣ R) (b : J ⊣ S) (e : F ≅ J) :
    ∃! t : R ≅ S, ∀ X, e.hom.app (R.obj X) ≫ J.map (t.hom.app X) ≫
      b.counit.app X = a.counit.app X := by
  let a' := a.ofNatIsoLeft e
  refine ⟨a'.rightAdjointUniq b, ?_, ?_⟩
  · intro X
    have he := Adjunction.rightAdjointUniq_hom_app_counit a' b X
    have hh := congrArg (fun z ↦ e.hom.app (R.obj X) ≫ z) he
    simpa only [a', Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc, Iso.hom_inv_id_app_assoc] using hh
  · intro t ht
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply (b.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
    apply (cancel_epi (e.hom.app (R.obj X))).1
    simpa [Adjunction.homEquiv_counit, a', Adjunction.ofNatIsoLeft_counit] using ht X

private theorem normalizedUniqReassoc
    {C D B E : Type*} [Category* C] [Category* D] [Category* B] [Category* E]
    {F J : C ⥤ D} {R : D ⥤ C} {S : D ⥤ B} {T : B ⥤ E} {U : E ⥤ C}
    (a : F ⊣ R) (b : J ⊣ S ⋙ T ⋙ U) (e : F ≅ J) :
    ∃! t : R ≅ (S ⋙ T) ⋙ U, ∀ X,
      e.hom.app (R.obj X) ≫ J.map (t.hom.app X) ≫ b.counit.app X =
        a.counit.app X := by
  let b' := b.ofNatIsoRight (Functor.associator S T U).symm
  have hb (X : D) : b'.counit.app X = b.counit.app X := by
    simp only [b', Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
      Functor.whiskerRight_app, Iso.symm_inv, Functor.associator_hom_app, Functor.comp_obj]
    rw [J.map_id, Category.id_comp]
  simpa only [hb] using normalizedUniq a b' e

private theorem normalizedChartAdjunction
    {C D E B H : Type*}
    [Category* C] [Category* D] [Category* E] [Category* B] [Category* H]
    {Lu : C ⥤ D} {Ru : D ⥤ C} {F : D ⥤ E} {R : E ⥤ D}
    {Li : C ⥤ B} {Ri : B ⥤ C} {Lπ : B ⥤ H} {Rπ : H ⥤ B}
    {Lv : H ⥤ E} {Rv : E ⥤ H}
    (au : Lu ⊣ Ru) (af : F ⊣ R) (ai : Li ⊣ Ri) (aπ : Lπ ⊣ Rπ)
    (av : Lv ⊣ Rv) (e : Lu ⋙ F ≅ (Li ⋙ Lπ) ⋙ Lv) :
    counitNormalizedChartComparison au af ai aπ av e := by
  unfold counitNormalizedChartComparison
  simpa only [Functor.comp_obj] using
    normalizedUniqReassoc (au.comp af) ((ai.comp aπ).comp av) e

private theorem closedChartTwistedPullback_adjunction
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (V : Scheme.{u}) [IsNoetherian V]
    (hV : IsUnit (N : Γ(V, ⊤))) (r : ℕ) :
    Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r) := by
  exact nonempty_affineSpaceAmbientAdjunction N hN A hA V hV r

private theorem closedChartTwistedPullback_obj
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (V : Scheme.{u}) (r : ℕ) (K : DerivedCategoryModule A V) :
    (closedChartTwistedPullback A N hA V r).obj K =
      pullbackTwistDerived A (AffineSpace (ULift.{u} (Fin r)) V ↘ V)
        N hA K r (2 * (r : ℤ)) := rfl

private theorem closedChartClosedTorAmplitude
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (a b c : ℤ) (_hc : 0 ≤ c)
    (_hcd : ∀ (M : Sheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) (q : ℤ), c < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R(lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) j)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (_hcons : ∀ (M : Sheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) (q : ℤ),
      @Scheme.IsConstructibleEtaleModuleSheaf U (Padic.coefficientExtensionRing l E n)
        inferInstance (Padic.finite_coefficientExtensionRing l E n hn) M →
      @Scheme.IsConstructibleEtaleModuleSheaf T (Padic.coefficientExtensionRing l E n)
        inferInstance (Padic.finite_coefficientExtensionRing l E n hn)
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) j)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) T)
    (_hK : @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
      inferInstance (Padic.finite_coefficientExtensionRing l E n hn) T K)
    (_hTor : DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n)
      T a b K) :
    letI : Finite (Padic.coefficientExtensionRing l E n) :=
      Padic.finite_coefficientExtensionRing l E n hn
    @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
      inferInstance (Padic.finite_coefficientExtensionRing l E n hn) Z
      ((R(lowerStar (ModuleCat.{u + 1}
        (Padic.coefficientExtensionRing l E n)) i)).rightAdjoint.obj K) ∧
    DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Z
      a (b + c + 1) ((R(lowerStar (ModuleCat.{u + 1}
        (Padic.coefficientExtensionRing l E n)) i)).rightAdjoint.obj K) := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  exact closedImmersion_rightAdjoint_torAmplitude l E n hn i j _hij a b c _hc _hcd
    _hcons K _hK _hTor

set_option maxRecDepth 2048 in
private theorem closedChartComparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    {X Y U V : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ Y) (v : V ⟶ Y) (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V)
    [IsOpenImmersion u] [IsOpenImmersion v] [IsClosedImmersion i]
    [QuasiCompact u] [QuasiCompact v] [QuasiCompact f] [QuasiCompact (u ≫ f)]
    [HasCompactification u] [HasCompactification v] [HasCompactification f]
    [HasCompactification (u ≫ f)]
    [HasCompactification (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V))]
    [HasCompactification ((i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v)]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) :
    ∀ (F : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ F)
    (adjπ : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r),
    counitNormalizedChartComparison
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u)
      adjF (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))) adjπ
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v)
      (closedChartCompactSupportComparison A u f v r i h) := by
  intro F adjF adjπ
  exact normalizedChartAdjunction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u)
    adjF (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))) adjπ
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v)
    (closedChartCompactSupportComparison A u f v r i h)

attribute [local irreducible] closedChartCompactSupportComparison
attribute [local irreducible] closedChartTwistedPullback

set_option maxRecDepth 2048 in
/-- Exceptional inverse image on a closed affine-space chart, before any boundedness
restriction, and bounded constructible finite-Tor preservation of its displayed right side.
The normalized vector-bundle purity adjunction is one of the adjunctions quantified in
`ClosedChartExceptionalAssertion`; its explicit counit equation gives the canonical iso.

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Locality and Charts, closed-chart supplement
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation).

Proof:
1. The coefficient ring is finite. In its DVR, ell lies in the uniformizer ideal, so
   ell^n kills A; ell != p makes this exponent invertible on all the schemes. Finite
   type over a field gives Noetherian X,Y. Their affine opens are Noetherian, as are
   the affine space P and its open complement W. Nagata supplies compactifications.
2. Exact open extension has the ordinary derived adjunction u_! |- u^* and v_! |- v^*.
   Compose the unbounded compact-support comparisons using fu = v pi i; normalize
   the open factors by extension by zero, and the proper closed factor by i_*.
   This is exactly `closedChartCompactSupportComparison`.
3. Vector-bundle purity for the trivial rank-r bundle supplies H |- pi^*(-)(r)[2r]
   on all unbounded inputs. Compose it with i_* |- Ri! and v_! |- v^*. The natural
   Hom chain of proof step 3 identifies this composite right adjoint with u^* F.
4. Transpose the identity through that Hom chain. The resulting iso e is the unique
   one satisfying lambda ; J(e) ; epsilon^J = epsilon^(Fu). Expanding the composite
   counits gives the equation in `ClosedChartExceptionalAssertion`. This argument
   works for every choice of the two right-adjoint presentations, in particular for
   the vector-bundle integration normalization. No boundedness of F(L) is used.
5. For bounded constructible L with Tor interval [a,b], exact inverse image along v
   and pi preserves the cohomological bounds, constructibility and Tor interval,
   using constructible pullback and the geometric-stalk Tor test.
6. The ordinary Tate line A_P(r) is finite locally constant, flat and rank one.
   Flat constructible tensor and tensor/stalk comparison preserve the bounds.
   The shift [2r] changes the Tor interval to [a-2r,b-2r], including r=0.
7. Bound the dimensions of all field base changes of W by d. The arbitrary-field
   torsion direct-image dimension theorem and coefficient-forgetting comparison
   give R^q j_* M = 0 for every module sheaf M and q > c = 2d.
8. Finite-type direct-image constructibility supplies the other complement
   hypothesis. The closed-support Tor theorem then makes Ri! of this expression
   bounded constructible with interval [a-2r,b-2r+c+1]. This proves preservation
   independently of the unbounded comparison of steps 2--4. -/
theorem etaleClosedChartExceptionalPreservation
    (ell : ℕ) [Fact ell.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hell : ell ≠ p)
    {X Y U V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsAffine U] [IsAffine V] (u : U ⟶ X) (v : V ⟶ Y)
    [IsOpenImmersion u] [IsOpenImmersion v] (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V) [IsClosedImmersion i]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) :
    ClosedChartExceptionalPreservation ell E n hn k f u v r i h := by
  -- Expose the predicate's installed instances before applying any constructors.
  -- Otherwise kernel conversion repeatedly unfolds their large geometric constructions.
  unfold ClosedChartExceptionalPreservation
  let : Finite (Padic.coefficientExtensionRing ell E n) :=
    Padic.finite_coefficientExtensionRing ell E n hn
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian Y := {}
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion u
  let : IsNoetherian U := {}
  let : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  let : IsNoetherian V := {}
  let : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  let : IsSeparated (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  let : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
  let A := Padic.coefficientExtensionRing ell E n
  let P := AffineSpace (ULift.{u} (Fin r)) V
  let π : P ⟶ V := AffineSpace (ULift.{u} (Fin r)) V ↘ V
  let W : P.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hnrm := etaleChartCompactSupportNormalization ell E n hn k p hp hell
    f u v r i W.ι hij h
  have hA := hnrm.2.1
  have hmaps := hnrm.2.2.2.1
  have hunit : IsUnit ((ell ^ n : ℕ) : k) := by
    have he : IsUnit (ell : k) := isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime) hell.symm)
    simpa only [Nat.cast_pow] using he.pow n
  have hvunit : IsUnit ((ell ^ n : ℕ) : Γ(V, ⊤)) := by
    simpa only [map_natCast] using
      (hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom).map
        (v ≫ (Y ↘ Spec (.of k))).appTop.hom
  refine ⟨hA, ?_⟩
  change ClosedChartExceptionalAssertion A (ell ^ n) hA u f v r i h
  refine ⟨?_, ?_, ?_⟩
  · exact closedChartTwistedPullback_adjunction (ell ^ n)
      (Nat.pow_pos (Fact.out : ell.Prime).pos) A hA V
      hvunit r
  · exact closedChartComparison A (ell ^ n) hA u f v r i h
  · intro L hL hTor
    rw [closedChartTwistedPullback_obj]
    obtain ⟨a₀, b₀, hTor⟩ := hTor
    let a := min a₀ b₀
    let b := max a₀ b₀
    have hab : a ≤ b := by dsimp [a, b]; omega
    have hTor' : DerivedCategory.hasTorAmplitudeIn A Y a b L := by
      intro M q hq
      apply hTor M q
      dsimp [a, b] at hq
      omega
    let TY := Over.mk (Y ↘ Spec (.of k))
    let TV := Over.mk (v ≫ (Y ↘ Spec (.of k)))
    let TP := Over.mk ((π ≫ v) ≫ (Y ↘ Spec (.of k)))
    have : IsSeparated TY.hom := inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
    have : LocallyOfFiniteType TY.hom :=
      inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of k)))
    have : QuasiCompact TY.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
    have hv := hmaps ⟨V, Spec (.of k), v ≫ (Y ↘ Spec (.of k))⟩ (by
      exact List.mem_of_getElem? (i := 15) rfl)
    have hp' := hmaps ⟨P, Spec (.of k), (π ≫ v) ≫ (Y ↘ Spec (.of k))⟩ (by
      exact List.mem_of_getElem? (i := 16) rfl)
    have : IsSeparated TV.hom := hv.1
    have : LocallyOfFiniteType TV.hom := hv.2.1
    have : QuasiCompact TV.hom := hv.2.2.1
    have : IsSeparated TP.hom := hp'.1
    have : LocallyOfFiniteType TP.hom := hp'.2.1
    have : QuasiCompact TP.hom := hp'.2.2.1
    have hV := (etale_pullback_twist_tor_window k p ell hp
      (Fact.out : ell.Prime) hell TY TV
      (Over.homMk v rfl) n A hA a b hab).2 L hL hTor'
    let LV := (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj L
    have hbV : _root_.DerivedCategory.TStructure.t.bounded LV := by
      obtain ⟨c, d, _, hz⟩ := hV.1.2
      exact ⟨⟨c, (_root_.DerivedCategory.isGE_iff _ _).2
        (fun q hq ↦ hz q (.inl hq))⟩,
        ⟨d, (_root_.DerivedCategory.isLE_iff _ _).2 (fun q hq ↦ hz q (.inr hq))⟩⟩
    obtain ⟨Q, hflat, hcons, hzero, hiso⟩ :=
      (exists_etaleScalarFlatModel V A A (RingHom.id A) a b hab
        ⟨LV, hbV⟩ hV.1.1 hV.2).1
    have hK := (etale_pullback_twist_tor_window k p ell hp
      (Fact.out : ell.Prime) hell TV TP
      (Over.homMk π (Category.assoc π v (Y ↘ Spec (.of k))).symm)
      n A hA a b hab).1 LV hV.1 hV.2 Q hiso hflat hcons hzero r (2 * (r : ℤ))
    have hKcons := hK.2.2.2.2.2.1
    have hKtor := hK.2.2.2.2.2.2
    have : QuasiCompact W.ι := (hmaps ⟨W, P, W.ι⟩ (by
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))).2.2.1
    have : LocallyOfFiniteType ((π ≫ v) ≫ (Y ↘ Spec (.of k))) := hp'.2.1
    have : QuasiCompact ((π ≫ v) ≫ (Y ↘ Spec (.of k))) := hp'.2.2.1
    obtain ⟨⟨d, hd⟩, hbound⟩ :=
      Scheme.exists_uniform_dimension_bound_and_hasOpenComplementCondition k A (ell ^ n)
        (Nat.one_le_iff_ne_zero.mpr
          (pow_ne_zero n (Fact.out : ell.Prime).ne_zero)) hunit hA
        ((π ≫ v) ≫ (Y ↘ Spec (.of k))) W.ι
    have hc := hbound d hd
    have hcd : ∀ (M : Sheaf (W : Scheme).smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
        2 * (d : ℤ) < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) W.ι)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) := by
      intro M q hq
      exact (hc.1 M q (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hq)).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
          ((lowerStar (ModuleCat.{u + 1} A) W.ι).rightDerivedFunctorPlusCompatibility.app
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M))).symm
    have hcc : ∀ (M : Sheaf (W : Scheme).smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
        Scheme.IsConstructibleEtaleModuleSheaf M →
        Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((R(lowerStar (ModuleCat.{u + 1} A) W.ι)).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) := by
      intro M q hM
      have hh := hc.2 M q hM
      have hsource : Scheme.IsConstructibleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            (((lowerStar (ModuleCat.{u + 1} A) W.ι).rightDerivedFunctorPlus ⋙
              _root_.DerivedCategory.Plus.ι).obj
                ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M))) :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 hh
      apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      exact Scheme.IsConstructibleSheaf.of_iso
        (F := (_root_.DerivedCategory.homologyFunctor _ q).obj
          (((lowerStar (ModuleCat.{u + 1} A) W.ι).rightDerivedFunctorPlus ⋙
            _root_.DerivedCategory.Plus.ι).obj
              ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M)))
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
          ((lowerStar (ModuleCat.{u + 1} A) W.ι).rightDerivedFunctorPlusCompatibility.app
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M)))
    obtain ⟨hbc, ht⟩ := closedChartClosedTorAmplitude ell E n hn i W.ι hij
      (a - 2 * (r : ℤ)) (b - 2 * (r : ℤ)) (2 * d) (by positivity) hcd hcc
      _ hKcons hKtor
    exact ⟨hbc, _, _, ht⟩

end AlgebraicGeometry.Etale
