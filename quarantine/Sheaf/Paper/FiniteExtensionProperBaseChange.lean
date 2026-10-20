/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.ConstructibleCompleteBaseChange
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.CompletedExchangeCoherence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.KrullDimension.Field
import Sheaf.Paper.UniformCompleteTriangulated
import Sheaf.Paper.WeilTensorProduct
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.IntrinsicCompletionCompleted

/-! # Proper base change over a finite extension

Source: Weil blueprint, proper base change, order 1357
(blueprint: thm-weil-pbc-finite-extension).
The rational arrow is the image of the specified completed integral exchange under
raw scalar localization. Its endpoints use the actual completed coefficient datum
of the integral corollary; no change of coefficient realization is made.

## Main definitions

- `AlgebraicGeometry.Scheme.finiteExtensionRationalExchangeComponent`: the specified arrow.

## Main statements

- `AlgebraicGeometry.Scheme.finiteExtension_properBaseChange`: every component is invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The coefficient-presentation round trip, applied degreewise. -/
private def finiteExtensionRoundTripComplex
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    C ≅ ((intrinsicPresentationModulesBack T d).mapHomologicalComplex (.up ℤ)).obj
      ((intrinsicPresentationComplex T d).obj C) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (intrinsicPresentationRoundTrip T d).app (C.X q))
    (by intro i j hij; exact ((intrinsicPresentationRoundTrip T d).hom.naturality (C.d i j)).symm)

/-- Exact conservative restriction detects invertibility of the transported Koszul unit.
Reflection on the derived category is checked on every homology object. -/
private theorem finiteExtensionUnit_isIso_iff
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a C)) ↔
      IsIso ((completedConstantQ _).map
        (completedKoszulUnitComplex T (intrinsicPresentationDatum d) r a
          ((intrinsicPresentationComplex T d).obj C))) := by
  let G := intrinsicPresentationModulesBack T d
  let : G.ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties (pbcCompletedComparison T d).inv).2.2
  let : G.mapDerivedCategory.ReflectsIsomorphisms := ⟨by
    intro M N f hf
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((DerivedCategory.homologyFunctor _ n).map
        (G.mapDerivedCategory.map f)) := inferInstance
    have : IsIso (G.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
      (NatIso.isIso_map_iff (G.mapDerivedCategoryHomologyFunctorIso n) f).mpr
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ G⟩
  let v := completedKoszulUnitComplex T (intrinsicPresentationDatum d) r a
    ((intrinsicPresentationComplex T d).obj C)
  have hunit : intrinsicCompletionComplexUnit T d r a C =
      (finiteExtensionRoundTripComplex T d C).hom ≫ (G.mapHomologicalComplex (.up ℤ)).map v := by
    ext q
    rfl
  rw [hunit, Functor.map_comp]
  rw [isIso_comp_left_iff]
  have h := NatIso.isIso_map_iff G.mapDerivedCategoryFactors v
  simpa only [Functor.comp_map] using h.symm.trans
    (isIso_iff_of_reflects_iso (DerivedCategory.Q.map v) G.mapDerivedCategory)

/-- Canonical intrinsic completeness extends to every representative by descent of the unit.
The quotient-tower criterion then gives the hypothesis of completed identity pullback. -/
private theorem finiteExtensionIntegral_towerComplete
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcBoundedConstructibleComplete T d) : d.TowerComplete T K.obj := by
  apply (d.towerComplete_iff_intrinsic T K.obj).mpr
  intro r a ha C e
  let F := intrinsicPresentationModules T d
  let R := wfCompletionRepresentative T d K.obj
  have hR := wfConstructible_complete T d r a ha K
  have hRu : IsIso (DerivedCategory.Q.map
      (intrinsicCompletionComplexUnit T d r a R)) := by
    have : IsIso (intrinsicCompletionUnit T d r a ha K.obj R
        (DerivedCategory.Q.objObjPreimageIso K.obj)) := hR
    unfold intrinsicCompletionUnit at this
    exact (isIso_comp_left_iff _ _).mp this
  have hRpub := (finiteExtensionUnit_isIso_iff T d r a R).mp hRu
  obtain ⟨H, η, hη⟩ :=
    completedIntrinsicCompletion_descends T (intrinsicPresentationDatum d) r a
  obtain ⟨iR, hiR⟩ := hη ((intrinsicPresentationComplex T d).obj R)
  have hηR : IsIso (η.app (DerivedCategory.Q.obj
      ((intrinsicPresentationComplex T d).obj R))) := by
    have : IsIso (η.app _ ≫ iR.hom) := by
      rw [hiR]
      exact hRpub
    exact (isIso_comp_right_iff _ _).mp this
  let iCR : DerivedCategory.Q.obj ((intrinsicPresentationComplex T d).obj C) ≅
      DerivedCategory.Q.obj ((intrinsicPresentationComplex T d).obj R) :=
    (F.mapDerivedCategoryFactors.app C).symm ≪≫
      F.mapDerivedCategory.mapIso (e ≪≫ (DerivedCategory.Q.objObjPreimageIso K.obj).symm) ≪≫
        F.mapDerivedCategoryFactors.app R
  have hηC := (η.isIso_app_iff_of_iso iCR).mpr hηR
  obtain ⟨iC, hiC⟩ := hη ((intrinsicPresentationComplex T d).obj C)
  have hCpub : IsIso (DerivedCategory.Q.map
      (completedKoszulUnitComplex T (intrinsicPresentationDatum d) r a
        ((intrinsicPresentationComplex T d).obj C))) := by
    rw [← hiC]
    infer_instance
  have hCu := (finiteExtensionUnit_isIso_iff T d r a C).mpr hCpub
  unfold IsDerivedCompleteIntrinsic intrinsicCompletionUnit
  infer_instance

/-- The rational component is precisely the integral completed exchange tensored with one.
The two membership proofs only place its prescribed endpoints in the full subcategory.
Raw localization has the same objects as that integral category.
Source: blueprint order 1357, specified rational exchange
(blueprint: thm-weil-pbc-finite-extension). -/
def finiteExtensionRationalExchangeComponent
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (K : PbcRationalCategory X (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E))
    (hSource : IsPbcBoundedConstructibleComplete Y' l E
      ((constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)).obj K.obj.obj))
    (hTarget : IsPbcBoundedConstructibleComplete Y' l E
      ((constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)).obj K.obj.obj)) :
    (pbcRationalization Y' (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj
        ⟨(constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)).obj K.obj.obj,
          hSource⟩ ⟶
    (pbcRationalization Y' (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj
        ⟨(constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)).obj K.obj.obj,
          hTarget⟩ :=
  (pbcRationalization Y' (pbcPadicCoefficientDatum l E)
    (Padic.coefficientExtensionUniformizer l E)).map
      (ObjectProperty.homMk
        (constructibleCompleteExchangeComponent sq (pbcPadicCoefficientDatum l E) K.obj.obj))

/-- Proper base change for the raw rational categories of a finite extension of Q_l.
The four existential membership witnesses give the restrictions of the actual direct
images and completed pullbacks to the integral constructible categories. Their rational
extensions are those of prop-weil-pbc-rational-transport. The displayed component is
exactly the extension of the completed integral exchange, including its chosen square.
Source: blueprint order 1357 (blueprint: thm-weil-pbc-finite-extension).
Proof:
1. The extending spectral absolute value gives |l| < 1. The maximal ideal is generated
by the recorded uniformizer, so l vanishes in the first coefficient quotient.
2. Pullback pasting identifies the geometric fibers of f' with those of f, retaining
bound e. Identity fibers are spectra of fields and have dimension zero.
3. Use the integral corollary on identity-vertical squares for each pullback, and on
identity-horizontal squares for each proper direct image. Transport membership through
pushId and completedPullId. To apply completedPullId, wfConstructible_complete supplies
intrinsic completeness at each generating tuple on the canonical representative.
The coefficient round trip and conservative exact restriction identify its Koszul unit
with the published one. Descent of that unit transfers invertibility to every
representative, and towerComplete_iff_intrinsic gives quotient-tower completeness.
The unlifted uniform-complete triangulation theorem supplies isomorphism closure.
4. Apply the integral corollary to the given square. Its component equality identifies
its natural isomorphism with the specified completed exchange. Lift this isomorphism
to the full integral subcategory using the four membership witnesses from step 3.
The rationalization functor maps it to an isomorphism whose hom is definitionally
finiteExtensionRationalExchangeComponent. Every raw rational object has its original
integral object, so this covers all objects, including zero and uniformizer torsion. -/
theorem finiteExtension_properBaseChange
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (_dimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (_dimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (_hlX : IsUnit (l : Γ(X, ⊤))) (_hlY : IsUnit (l : Γ(Y, ⊤)))
    (_hlX' : IsUnit (l : Γ(X', ⊤))) (_hlY' : IsUnit (l : Γ(Y', ⊤)))
    (e : ℕ)
    (_hFibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    ∃ (hRf : ∀ K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete Y l E
          (((pbcPadicCoefficientDatum l E).push f).obj K.obj))
      (hRf' : ∀ K : PbcBoundedConstructibleComplete X' (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete Y' l E
          (((pbcPadicCoefficientDatum l E).push f').obj K.obj))
      (hLg : ∀ K : PbcBoundedConstructibleComplete Y (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete Y' l E
          (((pbcPadicCoefficientDatum l E).completedPull g).obj K.obj))
      (hLg' : ∀ K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete X' l E
          (((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj)),
    ∀ K : PbcRationalCategory X (pbcPadicCoefficientDatum l E)
        (Padic.coefficientExtensionUniformizer l E),
      IsIso (finiteExtensionRationalExchangeComponent l E sq K
        (hLg ⟨((pbcPadicCoefficientDatum l E).push f).obj K.obj.obj, hRf K.obj⟩)
        (hRf' ⟨((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj.obj,
          hLg' K.obj⟩)) := by
  have hAnn : (l : Padic.coefficientExtensionRing l E 1) = 0 := by
    have H := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
    have hgen := H.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    change (Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (l : Padic.coefficientExtensionIntegers l E) ∈
      Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1
    change Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E at hgen
    rw [pow_one, hgen]
    apply (H.2.1 _).2
    have h := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
    rw [map_natCast] at h
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [h]
    exact Padic.norm_p_lt_one
  have hFibres' : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y'),
      topologicalKrullDim (pullback f' y : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
    intro Ω _ _ y
    let c : pullback f' y ≅ pullback f (y ≫ g) :=
      ((IsPullback.of_hasPullback f' y).flip.paste_vert
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst
          sq.hom_snd).flip).flip.isoPullback
    rw [(Scheme.homeoOfIso c).isHomeomorph.topologicalKrullDim_eq]
    exact _hFibres Ω (y ≫ g)
  let d := pbcPadicCoefficientDatum l E
  have hpull {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
      (hU : ∃ n : ℕ, topologicalKrullDim U ≤ (n : WithBot ℕ∞))
      (hV : ∃ n : ℕ, topologicalKrullDim V ≤ (n : WithBot ℕ∞))
      (hlU : IsUnit (l : Γ(U, ⊤))) (hlV : IsUnit (l : Γ(V, ⊤)))
      (h : U ⟶ V) (K : PbcBoundedConstructibleComplete V d) :
      IsPbcBoundedConstructibleComplete U l E ((d.completedPull h).obj K.obj) := by
    let s : IsPullback h (𝟙 U) (𝟙 V) h := .of_vert_isIso ⟨by simp⟩
    let square : ChosenCartesianSquare h (𝟙 U) (𝟙 V) h :=
      { w := by simp
        isoPullback := s.isoPullback
        hom_fst := s.isoPullback_hom_fst
        hom_snd := s.isoPullback_hom_snd }
    have hzero : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ V),
        topologicalKrullDim (pullback (𝟙 V) y : Scheme.{u}) ≤
          ((0 : ℕ) : WithBot ℕ∞) := by
      intro Ω _ _ y
      rw [(Scheme.homeoOfIso (asIso (pullback.snd (𝟙 V) y))).isHomeomorph.topologicalKrullDim_eq]
      change topologicalKrullDim (PrimeSpectrum Ω) ≤ 0
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        ringKrullDim_eq_zero_of_field]
    obtain ⟨htriV, htriU, hrest⟩ := constructibleComplete_properBaseChange l E square
      hV hV hU hU l (Fact.out : l.Prime).pos hAnn hlV hlV hlU hlU 0 hzero
    let := htriV
    let := htriU
    let := (pbcUniformComplete_isTriangulated U l E hU hlU).1
    obtain ⟨hF, _, _⟩ := hrest
    exact ObjectProperty.prop_of_iso (IsPbcBoundedConstructibleComplete U l E)
      ((d.completedPull h).mapIso ((d.pushId V).app K.obj)) (hF K)
  have hpush {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
      (hU : ∃ n : ℕ, topologicalKrullDim U ≤ (n : WithBot ℕ∞))
      (hV : ∃ n : ℕ, topologicalKrullDim V ≤ (n : WithBot ℕ∞))
      (hlU : IsUnit (l : Γ(U, ⊤))) (hlV : IsUnit (l : Γ(V, ⊤)))
      (h : U ⟶ V) [IsProper h]
      (he : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ V),
        topologicalKrullDim (pullback h y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
      (K : PbcBoundedConstructibleComplete U d) :
      IsPbcBoundedConstructibleComplete V l E ((d.push h).obj K.obj) := by
    let s : IsPullback (𝟙 U) h h (𝟙 V) := .of_horiz_isIso ⟨by simp⟩
    let square : ChosenCartesianSquare (𝟙 U) h h (𝟙 V) :=
      { w := by simp
        isoPullback := s.isoPullback
        hom_fst := s.isoPullback_hom_fst
        hom_snd := s.isoPullback_hom_snd }
    obtain ⟨htriU, htriV, hrest⟩ := constructibleComplete_properBaseChange l E square
      hU hV hU hV l (Fact.out : l.Prime).pos hAnn hlU hlV hlU hlV e he
    let := htriU
    let := htriV
    let := (pbcUniformComplete_isTriangulated V l E hV hlV).1
    obtain ⟨_, hG, _⟩ := hrest
    have hK : d.TowerComplete U K.obj := finiteExtensionIntegral_towerComplete U d K
    exact ObjectProperty.prop_of_iso (IsPbcBoundedConstructibleComplete V l E)
      ((d.push h).mapIso (d.completedPullId U K.obj hK)) (hG K)
  let hRf := hpush _dimX _dimY _hlX _hlY f _hFibres
  let hRf' := hpush _dimX' _dimY' _hlX' _hlY' f' hFibres'
  let hLg := hpull _dimY' _dimY _hlY' _hlY g
  let hLg' := hpull _dimX' _dimX _hlX' _hlX g'
  refine ⟨hRf, hRf', hLg, hLg', ?_⟩
  intro K
  obtain ⟨htriX, htriY', hrest⟩ := constructibleComplete_properBaseChange l E sq
    _dimX _dimY _dimX' _dimY' l (Fact.out : l.Prime).pos hAnn
    _hlX _hlY _hlX' _hlY' e _hFibres
  let := htriX
  let := htriY'
  obtain ⟨hF, hG, sF, sG, hFtri, hGtri, η, hshift, hη⟩ := hrest
  have hi : IsIso (constructibleCompleteExchangeComponent sq d K.obj.obj) := by
    rw [← hη K.obj]
    exact ((ObjectProperty.ι (IsPbcBoundedConstructibleComplete Y' l E)).mapIso
      (η.app K.obj)).isIso_hom
  let M : PbcBoundedConstructibleComplete Y' d :=
    ⟨(constructibleCompleteSource f g d).obj K.obj.obj,
      hLg ⟨(d.push f).obj K.obj.obj, hRf K.obj⟩⟩
  let N : PbcBoundedConstructibleComplete Y' d :=
    ⟨(constructibleCompleteTarget g' f' d).obj K.obj.obj,
      hRf' ⟨(d.completedPull g').obj K.obj.obj, hLg' K.obj⟩⟩
  let i : M ≅ N := ObjectProperty.isoMk _
    (asIso (constructibleCompleteExchangeComponent sq d K.obj.obj))
  exact ((pbcRationalization Y' d (Padic.coefficientExtensionUniformizer l E)).mapIso i).isIso_hom

end AlgebraicGeometry.Scheme
