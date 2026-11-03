/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionComparisons
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteProCoefficientCounitTransport
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionCompatibilities
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteNormalizedOrientationScalar
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel

/-! # Finite reduction of purity and its geometric coherences

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.md
(blueprint: thm-pur-finite-reduction-of-purity).

All five clauses use the canonical pro-etale scalar, pullback, tensor, compact-support
and exceptional counit comparisons. Finite quotient maps A_{E,n} -> A_{E,m}, including
the zero quotient, are special cases of phi between finite rings killed by a common
invertible exponent N. NormalizedSmoothDatum retains the diagonal/Rees/Kummer equation,
so its alpha is a presentation of that orientation, not a freely chosen purity map.
There is no finite-field-datum restriction: the scheme formulation applies over every
field of characteristic prime to N, as well as over an invertible-exponent base.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compactCoefficientNaturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [HasCompactification f]
    {M M' : proCategory A X} (hM : IsCtf A X M) (hM' : IsCtf A X M')
    (v : M ⟶ M') :
    (proScalar phi Y).map ((proCompact A f).map v) ≫
        proCompactCoefficientMap phi f M' =
      proCompactCoefficientMap phi f M ≫
        (proCompact B f).map ((proScalar phi X).map v) := by
  with_unfolding_all
    have ho := actualOriginCtf A X M hM
    have ho' := actualOriginCtf A X M' hM'
    have hi := originInverseNaturality A X hM hM' v
    have ha := compactSiteNaturality A f ho.1.1.1 ho'.1.1.1 ((origin A X).map v)
    have hy := (ProEtale.pbcComparisonReduction Y phi).hom.naturality
      ((rightDerivedLowerShriek (ModuleCat A) f).map ((origin A X).map v))
    have hb := compactScalarMap_naturality phi (HasCompactification.compactification f)
      ((origin A X).map v)
    have hs := inverseSiteNaturality B f
      (ExceptionalCoefficients.scalar_extension_plus_of_finiteTor phi X _ ho.2)
      (ExceptionalCoefficients.scalar_extension_plus_of_finiteTor phi X _ ho'.2)
      ((ordinaryScalar phi X).map ((origin A X).map v))
    have hx := (ProEtale.pbcComparisonReduction X phi).inv.naturality ((origin A X).map v)
    have hc := (ProEtale.derivedComparisonAdjunction (ModuleCat A) X).counit.naturality v
    dsimp only [Functor.comp_map, Functor.id_map] at hy hx hc
    have ha' := congrArg (proScalar phi Y).map ha
    have hb' := congrArg (comparison B Y).map hb
    have hx' := congrArg (proCompact B f).map hx
    have hc' := congrArg (fun z ↦ (proCompact B f).map ((proScalar phi X).map z)) hc
    simp only [Functor.map_comp] at ha' hb' hx' hc'
    simp only [proCompactCoefficientMap, Functor.map_comp, Category.assoc]
    rw [← (proScalar phi Y).map_comp_assoc, ← (proCompact A f).map_comp, hi]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% ha', reassoc_of% hy, reassoc_of% hb', reassoc_of% hs,
      reassoc_of% hx', hc']
    rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem counitNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {K K' : proCategory A Y}
    (hK : _root_.DerivedCategory.TStructure.t.plus
      ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K)))
    (hK' : _root_.DerivedCategory.TStructure.t.plus
      ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K')))
    (v : K ⟶ K') :
    (proCompact A f).map ((exceptional A f).map v) ≫ proCounit A f K' =
      proCounit A f K ≫ v := by
  with_unfolding_all
    have hs := compactSiteNaturality A f hK hK'
      ((rightDerivedUpperShriek A f).map ((origin A Y).map v))
    have he := (rightDerivedUpperShriekAdjunction A f).counit.naturality
      ((origin A Y).map v)
    have hc := (ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.naturality v
    dsimp only [Functor.comp_map, Functor.id_map] at he hc
    simp only [proCounit, exceptional, Functor.comp_map, Category.assoc]
    rw [reassoc_of% hs, ← (comparison A Y).map_comp_assoc, he,
      (comparison A Y).map_comp_assoc]
    erw [hc]

/-- Scalar extension preserves the intrinsic ctf domain: compute it on a bounded
flat constructible model of the actual etale origin, then transport through the
specified site/scalar comparison and the invertible comparison counit. -/
private theorem scalarCtf
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (Y : Scheme.{u}) [IsNoetherian Y]
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsCtf B Y ((proScalar phi Y).obj K) := by
  with_unfolding_all
    have ho := actualOriginCtf A Y K hK
    obtain ⟨a, b, ht⟩ := ho.2
    have hm := exists_etaleScalarFlatModel Y A B phi a (max a b) (le_max_left _ _)
      ⟨(origin A Y).obj K, ho.1.1⟩
      (fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
        (ho.1.2 i))
      (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
        (ht.mono le_rfl (le_max_right _ _)))
    obtain ⟨L, ⟨eL⟩⟩ := hm.2.2.1
    have hb : DerivedCategory.boundedConstructibleFiniteTor B Y
        ((ordinaryScalar phi Y).obj ((origin A Y).obj K)) := by
      refine ⟨⟨(_root_.DerivedCategory.TStructure.t.bounded).prop_of_iso eL L.property,
        fun i ↦ ?_⟩, a, max a b, ?_⟩
      · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
          (hm.2.2.2.1 i)
      · exact DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hm.2.2.2.2
    have := intrinsicOriginCounit A Y K hK
    exact isCtfOfIso B Y
      (((ProEtale.pbcComparisonReduction Y phi).app ((origin A Y).obj K)).symm ≪≫
        (proScalar phi Y).mapIso
          (asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K)))
      (comparisonCtf B Y _ hb)

/-- The purity square and its vertical isomorphisms on the ctf domain, together with
preservation of that domain. Source: current blueprint, finite reduction of purity.
Proof: use the bounded flat model to preserve ctf. Compare the unit orientations by
Wei Yang #1412: pull both degree-zero line sections to geometric points and compute
the Kummer boundary, then use uniqueness of the normalized Rees specialization.
Tensor this unit equality with the actual pullback of K, using the canonical scalar
projection map. The counit mate gives the exceptional comparison, and site transport
gives the displayed square. This does not infer equality of derived arrows from stalks.
(blueprint: thm-pur-finite-reduction-of-purity). -/
theorem finiteReductionOfPurity
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (DA : NormalizedSmoothDatum A N hN hA f d hX)
    (DB : NormalizedSmoothDatum B N hN hB f d hX)
    (e : CoefficientLineComparison phi N N hA hB X)
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsCtf B Y ((proScalar phi Y).obj K) ∧
    IsIso (proLambda f d e K) ∧ IsIso (proCoefficientMap phi f K) ∧
    (proScalar phi X).map (proGamma A f _ DA.alpha K) ≫ proCoefficientMap phi f K =
      proLambda f d e K ≫ proGamma B f _ DB.alpha ((proScalar phi Y).obj K) := by
  with_unfolding_all
    have hBK := scalarCtf phi Y K hK
    have ha := intrinsicOriginCounit A Y K hK
    have hb := scalarOriginCounit phi Y K hK
    have hp := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor phi Y _
      (actualOriginCtf A Y K hK).2
    have hu := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat B) Y
      ((ordinaryScalar phi Y).obj ((origin A Y).obj K)) hp
    have ho : IsIso (originReductionMap phi Y K) := by
      unfold originReductionMap
      rw [Adjunction.homEquiv_unit]
      infer_instance
    have hs : IsIso (sourceToOrigin A f (line A N hA X d) K) := by
      dsimp only [sourceToOrigin, originInverse]
      rw [dif_pos ha]
      infer_instance
    have hl : IsIso (proLambda f d e K) := by
      dsimp only [proLambda, sourceFromOrigin]
      infer_instance
    have hab := normalizedOrientation_scalar phi N N hN hN (dvd_refl N) hA hB
      hY f d DA.geometry hX hX DA.alpha DB.alpha DA.normalized DB.normalized e
    have heq := proGammaCoefficient phi f N N hA hB d e DA.alpha DB.alpha
      (ordinaryGammaCoefficient phi f N N hA hB d e DA.alpha DB.alpha hab) K hK
    have hga := proGammaIso A N hN hA f d
      (fun y ↦ by simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y trivial).hom)
      _ DA.alpha K hK
    have hgb := proGammaIso B N hN hB f d
      (fun y ↦ by simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y trivial).hom)
      _ DB.alpha _ hBK
    have hprod : IsIso
        ((proScalar phi X).map (proGamma A f _ DA.alpha K) ≫
          proCoefficientMap phi f K) := by
      rw [heq]
      infer_instance
    exact ⟨hBK, hl, IsIso.of_isIso_comp_left
      ((proScalar phi X).map (proGamma A f _ DA.alpha K)) _, heq⟩

/-- Reduction of the Kummer coordinate-boundary orientation of the affine zero
section, in pro-etale coordinates. The Cartier proof is constructed, not assumed.
Source: thm-pur-affine-line-orientation and current finite-reduction proof, affine
clause (node proof Step 6).
Proof: the coordinate torsor t reduces to the same coordinate torsor. Functoriality
of the supported Kummer boundary identifies its two coefficient realizations. Take
exceptional adjuncts using the counit-normalized coefficient mate, then transport
through the site adjunction. The shift and line maps are exactly proKummerInputMap.
(blueprint: thm-pur-finite-reduction-of-purity). -/
theorem finiteReductionOfAffineOrientation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y]
    (hT : IsUnit (N : Γ(AffineSpace (ULift.{u} (Fin 1)) Y, ⊤)))
    (e : CoefficientLineComparison phi N N hA hB
      (AffineSpace (ULift.{u} (Fin 1)) Y)) :
    let T := AffineSpace (ULift.{u} (Fin 1)) Y
    let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y
    let hI : s.ker.IsInvertible := by
      let p : T ⟶ Y := T ↘ Y
      have : SmoothOfRelativeDimension 1 p := by
        simpa only [Nat.card_ulift, Nat.card_fin] using
          AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin 1)) Y
      let l := IsClosedImmersion.lift s s.ker.subschemeι
        (Scheme.IdealSheafData.ker_subschemeι s.ker).ge
      have : IsIso l := IsClosedImmersion.isIso_lift s s.ker.subschemeι
        (Scheme.IdealSheafData.ker_subschemeι s.ker).symm
      have hl : s.ker.subschemeι ≫ p = l := by
        rw [← IsClosedImmersion.lift_fac s s.ker.subschemeι
          (Scheme.IdealSheafData.ker_subschemeι s.ker).ge, Category.assoc,
          AffineSpace.zeroSection_comp_over, Category.comp_id]
      have : IsIso (s.ker.subschemeι ≫ p) := hl ▸ inferInstance
      exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
        inferInstance inferInstance inferInstance
    let LA := (comparison A T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)
    (proScalar phi Y).map (proKummerOrientation A N hN hA s hI hT) ≫
        proCoefficientMap phi s LA ≫
        (exceptional B s).map (proKummerInputMap phi N N hA hB T e) =
      (ProEtale.finiteGeneralRingScalarUnitIso phi Y).hom ≫
        proKummerOrientation B N hN hB s hI hT := by
  sorry

/-- Reduction of the smooth trace for every ctf K, using the actual compact-support
comparison b and the same lambda as in the purity square.
Source: current blueprint proof, trace clause (node proof Step 7).
Proof: expand proTrace as Rf_! of gamma followed by the counit. Apply the purity square
and the defining counit equation of the canonical exceptional coefficient mate.
Naturality of b then gives this equality, with no flatness assumption on phi.
(blueprint: thm-pur-finite-reduction-of-purity). -/
theorem finiteReductionOfSmoothTrace
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (DA : NormalizedSmoothDatum A N hN hA f d hX)
    (DB : NormalizedSmoothDatum B N hN hB f d hX)
    (e : CoefficientLineComparison phi N N hA hB X)
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    (proScalar phi Y).map (proTrace A f _ DA.alpha K) =
      proCompactCoefficientMap phi f ((proSource A f (line A N hA X d)).obj K) ≫
        (proCompact B f).map (proLambda f d e K) ≫
        proTrace B f _ DB.alpha ((proScalar phi Y).obj K) := by
  with_unfolding_all
    have hred := finiteReductionOfPurity phi N hN hA hB f d hX hY DA DB e K hK
    have : HasInvertibleExponent A Y := ⟨N, hN, hA, hY⟩
    have : HasInvertibleExponent B Y := ⟨N, hN, hB, hY⟩
    have hG := ordinaryExceptionalCtf A f d _ (actualOriginCtf A Y K hK)
    have hGB := ordinaryExceptionalCtf B f d _
      (actualOriginCtf B Y _ hred.1)
    have hsource := (proObjectsCtf A N hN hA f d
      (fun y ↦ by simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y trivial).hom)
      _ DA.alpha K hK).1
    have htarget : IsCtf A X ((exceptional A f).obj K) := comparisonCtf A X _ hG
    have hn := compactCoefficientNaturality phi f hsource htarget
      (proGamma A f _ DA.alpha K)
    have hc := finiteProCoefficientCounitTransport phi f K hK hG hGB.1.1.1
    have hi : IsIso (proCompactCoefficientMap phi f ((exceptional A f).obj K)) := by
      change IsIso (proCompactCoefficientMap phi f
        ((comparison A X).obj ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K))))
      rw [compactCoefficientAtOrigin phi f _ hG]
      have hp := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor phi X _ hG.2
      have ha : IsIso (compactSiteMap A f
          ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K))) := by
        unfold compactSiteMap
        rw [dif_pos hG.1.1.1]
        infer_instance
      have hb : IsIso (compactSiteInverse B f ((ordinaryScalar phi X).obj
          ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K)))) := by
        unfold compactSiteInverse
        erw [dif_pos hp]
        infer_instance
      have := ExceptionalCoefficients.compactSupport_isIso phi
        (HasCompactification.compactification f)
        ((rightDerivedUpperShriek A f).obj ((origin A Y).obj K))
      infer_instance
    have hcancel : proCompactCoefficientMap phi f ((exceptional A f).obj K) ≫
        proCompactCoefficientInverse phi f ((exceptional A f).obj K) = 𝟙 _ := by
      unfold proCompactCoefficientInverse
      rw [dif_pos hi]
      exact IsIso.hom_inv_id _
    calc
      _ = (proScalar phi Y).map ((proCompact A f).map (proGamma A f _ DA.alpha K)) ≫
          (proScalar phi Y).map (proCounit A f K) := by
            rw [proTrace, Functor.map_comp]
      _ = proCompactCoefficientMap phi f ((proSource A f (line A N hA X d)).obj K) ≫
          (proCompact B f).map
            ((proScalar phi X).map (proGamma A f _ DA.alpha K)) ≫
          (proCompact B f).map (proCoefficientMap phi f K) ≫
          proCounit B f ((proScalar phi Y).obj K) := by
            rw [hc, ← reassoc_of% hn, reassoc_of% hcancel]
      _ = _ := by
        rw [← (proCompact B f).map_comp_assoc, hred.2.2.2, Functor.map_comp]
        simp only [proTrace, Category.assoc]


/-- Reduction of the smooth trace at the coefficient unit, including the canonical
scalar-unit identification at the output and in the purity source.
Source: current blueprint trace clause, including the unit trace (node proof Step 7).
Proof: specialize the preceding trace equality to the constant unit. Compose with
finiteGeneralRingScalarUnitIso and use naturality of the B-valued smooth trace.
The constant finite free unit is ctf, including for the zero coefficient ring.
(blueprint: thm-pur-finite-reduction-of-purity). -/
theorem finiteReductionOfUnitSmoothTrace
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (DA : NormalizedSmoothDatum A N hN hA f d hX)
    (DB : NormalizedSmoothDatum B N hN hB f d hX)
    (e : CoefficientLineComparison phi N N hA hB X)
    : let UA := (comparison A Y).obj (ordinaryFiniteUnit A Y)
      let UB := (comparison B Y).obj (ordinaryFiniteUnit B Y)
      let unitMap := (ProEtale.finiteGeneralRingScalarUnitIso phi Y).hom
      (proScalar phi Y).map (proTrace A f _ DA.alpha UA) ≫ unitMap =
        proCompactCoefficientMap phi f ((proSource A f (line A N hA X d)).obj UA) ≫
          (proCompact B f).map
            (proLambda f d e UA ≫ (proSource B f (line B N hB X d)).map unitMap) ≫
          proTrace B f _ DB.alpha UB := by
  with_unfolding_all
    dsimp only
    let UA := (comparison A Y).obj (ordinaryFiniteUnit A Y)
    let UB := (comparison B Y).obj (ordinaryFiniteUnit B Y)
    let unitMap := (ProEtale.finiteGeneralRingScalarUnitIso phi Y).hom
    have hUA : IsCtf A Y UA := by
      apply comparisonCtf A Y
      exact ⟨(DerivedCategory.boundedConstructible (ModuleCat A) Y).prop_of_iso
          (singleFunctorObjUnitIso (ModuleCat A) Y).symm (ordinaryUnitCtf A Y).1,
        (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso
          (singleFunctorObjUnitIso (ModuleCat A) Y).symm (ordinaryUnitCtf A Y).2⟩
    have hUB : IsCtf B Y UB := by
      apply comparisonCtf B Y
      exact ⟨(DerivedCategory.boundedConstructible (ModuleCat B) Y).prop_of_iso
          (singleFunctorObjUnitIso (ModuleCat B) Y).symm (ordinaryUnitCtf B Y).1,
        (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso
          (singleFunctorObjUnitIso (ModuleCat B) Y).symm (ordinaryUnitCtf B Y).2⟩
    have hred := finiteReductionOfPurity phi N hN hA hB f d hX hY DA DB e UA hUA
    have : HasInvertibleExponent B Y := ⟨N, hN, hB, hY⟩
    have hG := ordinaryExceptionalCtf B f d _ (actualOriginCtf B Y _ hred.1)
    have hG' := ordinaryExceptionalCtf B f d _ (actualOriginCtf B Y UB hUB)
    have hn := proNaturality B f _ DB.alpha hred.1 hUB unitMap
    have hc := counitNaturality B f hG.1.1.1 hG'.1.1.1 unitMap
    have ht : proTrace B f _ DB.alpha ((proScalar phi Y).obj UA) ≫ unitMap =
        (proCompact B f).map ((proSource B f (line B N hB X d)).map unitMap) ≫
          proTrace B f _ DB.alpha UB := by
      simp only [proTrace, Category.assoc]
      rw [← hc, ← Functor.map_comp_assoc, ← hn, Functor.map_comp_assoc]
    rw [finiteReductionOfSmoothTrace phi N hN hA hB f d hX hY DA DB e UA hUA]
    simp only [Category.assoc, Functor.map_comp]
    rw [ht]


/-- Reduction of geometric composition for smooth X -> Y -> Z: the source
compositor, exceptional counit compositor, and the full composed purity arrow.
Source: thm-pur-composition-coherence and current finite-reduction proof, coherence
clause (node proof Step 8).
Proof: scalar tensor/shift associativity and the generator-normalized roots maps
commute with every factor of proCompositionSource. Uniqueness of counit mates
identifies proCompositionExceptional after coefficient change. Apply the purity
square to f, g, and gf and then the geometric composition equality at B. This gives
the last equation, with the canonical source and exceptional comparisons displayed.
(blueprint: thm-pur-finite-reduction-of-purity). -/
theorem finiteReductionOfCompositionCoherence
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    [IsSeparated f] [IsSeparated g] [IsSeparated (f ≫ g)]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension (d + e) (f ≫ g)]
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (hZ : IsUnit (N : Γ(Z, ⊤)))
    (Af : NormalizedSmoothDatum A N hN hA f d hX)
    (Ag : NormalizedSmoothDatum A N hN hA g e hY)
    (Afg : NormalizedSmoothDatum A N hN hA (f ≫ g) (d + e) hX)
    (Bf : NormalizedSmoothDatum B N hN hB f d hX)
    (Bg : NormalizedSmoothDatum B N hN hB g e hY)
    (Bfg : NormalizedSmoothDatum B N hN hB (f ≫ g) (d + e) hX)
    (eX : CoefficientLineComparison phi N N hA hB X)
    (eY : CoefficientLineComparison phi N N hA hB Y)
    (K : proCategory A Z) (hK : IsCtf A Z K) :
    let QK := (proScalar phi Z).obj K
    let SAg := proSource A g (line A N hA Y e)
    let SBf := proSource B f (line B N hB X d)
    let EqA := (exceptional A g).obj K
    IsIso (proCompositionExceptional A f g K) ∧
    IsIso (proCompositionExceptional B f g QK) ∧
    (proScalar phi X).map (proCompositionSource A N hN hA f g hY d e K).hom ≫
        proLambda f d eX (SAg.obj K) ≫ SBf.map (proLambda g e eY K) =
      proLambda (f ≫ g) (d + e) eX K ≫
        (proCompositionSource B N hN hB f g hY d e QK).hom ∧
    (proScalar phi X).map (proCompositionExceptional A f g K) ≫
        proCoefficientMap phi f EqA ≫ (exceptional B f).map (proCoefficientMap phi g K) =
      proCoefficientMap phi (f ≫ g) K ≫ proCompositionExceptional B f g QK ∧
    (proScalar phi X).map (proGamma A (f ≫ g) _ Afg.alpha K ≫
        proCompositionExceptional A f g K) ≫ proCoefficientMap phi f EqA ≫
        (exceptional B f).map (proCoefficientMap phi g K) =
      proLambda (f ≫ g) (d + e) eX K ≫
        (proCompositionSource B N hN hB f g hY d e QK).hom ≫
        SBf.map (proGamma B g _ Bg.alpha QK) ≫
        proGamma B f _ Bf.alpha ((exceptional B g).obj QK) := by
  sorry

/-- Reduction of the Cartesian source square and of the purity-conjugated smooth
exchange square, together with the two purity/base-change squares themselves.
Source: thm-pur-smooth-base-change-coherence and current finite-reduction proof,
coherence clause (node proof Step 8).
Proof: commute scalar extension with the actual tensor, roots, and pullback
compositors to obtain the source equation. Smooth purity is invertible on ctf,
so its coefficient square also commutes with its inverse. Substitute the defining
three factors of proSmoothExchange and the primed purity square. The resulting
coefficient square is the second equation; cancellation of inverse purity gives
the last two equations. No compatibility of any free adjunction family is assumed.
(blueprint: thm-pur-finite-reduction-of-purity). -/
theorem finiteReductionOfBaseChange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    [HasCompactification f] [HasCompactification f']
    [QuasiCompact f] [QuasiCompact f'] [IsSeparated f] [IsSeparated f']
    (a : X' ⟶ X) (b : Y' ⟶ Y) (sq : IsPullback a f' f b)
    (d : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    (hX : IsUnit (N : Γ(X, ⊤))) (hX' : IsUnit (N : Γ(X', ⊤)))
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤)))
    (DA : NormalizedSmoothDatum A N hN hA f d hX)
    (DA' : NormalizedSmoothDatum A N hN hA f' d hX')
    (DB : NormalizedSmoothDatum B N hN hB f d hX)
    (DB' : NormalizedSmoothDatum B N hN hB f' d hX')
    (eX : CoefficientLineComparison phi N N hA hB X)
    (eX' : CoefficientLineComparison phi N N hA hB X')
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    let QK := (proScalar phi Y).obj K
    let PA := (proPullback A b).obj K
    let PB := (proPullback B b).obj QK
    let SA := proSource A f (line A N hA X d)
    let SB' := proSource B f' (line B N hB X' d)
    let tA := proBaseChangeSource A N hN hA f f' a b sq hX d K
    let tB := proBaseChangeSource B N hN hB f f' a b sq hX d QK
    let exA := proSmoothExchange A N hN hA f f' a b sq hX d DA.alpha DA'.alpha K
    let exB := proSmoothExchange B N hN hB f f' a b sq hX d DB.alpha DB'.alpha QK
    IsIso exA ∧ IsIso exB ∧
    (proScalar phi X').map tA.hom ≫ proLambda f' d eX' PA ≫
        SB'.map (proPullbackMap phi b K) =
      proPullbackMap phi a (SA.obj K) ≫ (proPullback B a).map (proLambda f d eX K) ≫
        tB.hom ∧
    (proScalar phi X').map exA ≫ proCoefficientMap phi f' PA ≫
        (exceptional B f').map (proPullbackMap phi b K) =
      proPullbackMap phi a ((exceptional A f).obj K) ≫
        (proPullback B a).map (proCoefficientMap phi f K) ≫ exB ∧
    (proPullback A a).map (proGamma A f _ DA.alpha K) ≫ exA =
      tA.hom ≫ proGamma A f' _ DA'.alpha PA ∧
    (proPullback B a).map (proGamma B f _ DB.alpha QK) ≫ exB =
      tB.hom ≫ proGamma B f' _ DB'.alpha PB := by
  sorry

end AlgebraicGeometry.Etale.FiniteSmoothPurity
