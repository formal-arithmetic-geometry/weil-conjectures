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
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.CompletedExchangeCoherence
import Sheaf.Paper.PbcActualRingedExchange

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
1. Every raw rational object is an integral object by def-weil-pbc-rational-category.
Use cor-weil-pbc-constructible-complete on it. The integer l annihilates the first
coefficient quotient, since its valuation is less than one by
def-weil-l-adic-coefficient-extension, and is invertible on all four schemes.
2. Apply the corollary also to the identity-horizontal squares for f and f', and to
the identity-vertical squares for g and g', with fiber bound zero. For a geometric
point y' of Y', the chosen Cartesian identification identifies the fiber of f' at y'
with the fiber of f at g y', so the same bound e applies. Identity direct image does
nothing to a K-injective representative. Identity completed pullback is completion,
whose unit is invertible on complete objects by def-weil-pbc-completed-pullback.
This supplies the four membership witnesses without extracting a common cohomological
interval from local-model bounds. Inverse image and tensor take multiplication by a
to multiplication by the same constant a; inverse limits do so componentwise. For a
K-flat roof C <- P -> D, multiplication by a replaces its second arrow u by au; the
termwise operation sends this to aF(u), leaving the denominator fixed. For right
derivations, lem-weil-pbc-kinjective-hom-derived identifies a derived morphism with a
unique homotopy class between K-injective representatives. The representative of its
scalar multiple is the scalar multiple of that class, since localization is linear
and its Hom map is injective. Termwise direct image and inverse limit preserve these
scalar multiples and homotopies, independently of any choice of resolutions. Shifts
and cones of K-injectives remain K-injective by the Hom characterization. Tensor and
the additive termwise operations preserve the two finite summands and differential
in a cone. Thus the restrictions preserve shifts, triangles and scalars, and
prop-weil-pbc-rlim-functoriality supplies the derived inverse-limit operation.
Apply prop-weil-pbc-rational-transport. Localization of the composite equals the
composite of the localizations on objects and pure tensors, so its specified exchange
is exactly finiteExtensionRationalExchangeComponent.
3. Tensor the inverse integral exchange with one. The composition and identity formulas
of def-weil-linear-scalar-localization make its two composites the identity. Thus every
rational component is invertible, also for zero and uniformizer-power-torsion objects. -/
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
  classical
  let d := pbcPadicCoefficientDatum l E
  have hAnn : (l : Padic.coefficientExtensionRing l E 1) = 0 := by
    have h := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    change Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (l : Padic.coefficientExtensionIntegers l E) ∈
      Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1
    rw [pow_one, hgen]
    apply (h.2.1 _).mpr
    have he := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
    change spectralNorm ℚ_[l] E (l : E) < 1
    simpa only [map_natCast] using he.trans_lt (Padic.norm_p_lt_one (p := l))
  have hId (T : Scheme.{u}) (K : PbcBoundedConstructibleComplete T d) :
      (d.completedPull (𝟙 T)).obj K.obj ≅ K.obj := by
    let J : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete T d) := ⟨K.obj, K.property.1⟩
    exact ((cbcDatumActualStrictTransport d (𝟙 T)).app K.obj).symm ≪≫
      ((pbcActualCompletedPullback_tower d (𝟙 T)).exists.choose.app J) ≪≫
      (pbcActualCompletedPullIdIso d T).app J
  have hIsoX := pbcUniformComplete_isTriangulated X l E _dimX _hlX
  have hIsoY := pbcUniformComplete_isTriangulated Y l E _dimY _hlY
  have hIsoX' := pbcUniformComplete_isTriangulated X' l E _dimX' _hlX'
  have hIsoY' := pbcUniformComplete_isTriangulated Y' l E _dimY' _hlY'
  have := hIsoX.1
  have := hIsoY.1
  have := hIsoX'.1
  have := hIsoY'.1
  have := hIsoX.2
  have := hIsoY.2
  have := hIsoX'.2
  have := hIsoY'.2
  have hFibres' : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y'),
      topologicalKrullDim (pullback f' y : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
    intro Ω _ _ y
    have hs := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
    have ht := ((IsPullback.of_hasPullback f' y).flip.paste_vert hs.flip).flip
    let i := ht.isoPullback
    rw [IsHomeomorph.topologicalKrullDim_eq _ i.hom.homeomorph.isHomeomorph]
    exact _hFibres Ω (y ≫ g)
  have hPush {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
      (h : S ⟶ T) [IsProper h]
      (hdS : ∃ n : ℕ, topologicalKrullDim S ≤ (n : WithBot ℕ∞))
      (hdT : ∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))
      (hlS : IsUnit (l : Γ(S, ⊤))) (hlT : IsUnit (l : Γ(T, ⊤)))
      (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T),
        topologicalKrullDim (pullback h y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
      (K : PbcBoundedConstructibleComplete S d) :
      PbcIsBoundedConstructibleComplete T d ((d.push h).obj K.obj) := by
    let sqh : ChosenCartesianSquare (𝟙 S) h h (𝟙 T) :=
      { w := by simp
        isoPullback := (asIso (pullback.fst h (𝟙 T))).symm
        hom_fst := by simp
        hom_snd := by simp }
    have H := constructibleComplete_properBaseChange l E sqh hdS hdT hdS hdT
      l (Fact.out : l.Prime).pos hAnn hlS hlT hlS hlT e hf
    have := H.1
    have := H.2.1
    obtain ⟨_, hG, _⟩ := H.2.2
    have := (pbcUniformComplete_isTriangulated T l E hdT hlT).1
    exact ObjectProperty.prop_of_iso _ ((d.push h).mapIso (hId S K)) (hG K)
  have hPull {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
      (h : S ⟶ T)
      (hdS : ∃ n : ℕ, topologicalKrullDim S ≤ (n : WithBot ℕ∞))
      (hdT : ∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))
      (hlS : IsUnit (l : Γ(S, ⊤))) (hlT : IsUnit (l : Γ(T, ⊤)))
      (K : PbcBoundedConstructibleComplete T d) :
      PbcIsBoundedConstructibleComplete S d ((d.completedPull h).obj K.obj) := by
    let sqh : ChosenCartesianSquare h (𝟙 S) (𝟙 T) h :=
      { w := by simp
        isoPullback := (asIso (pullback.snd (𝟙 T) h)).symm
        hom_fst := by simp
        hom_snd := by simp }
    have hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T),
        topologicalKrullDim (pullback (𝟙 T) y : Scheme.{u}) ≤ (0 : WithBot ℕ∞) := by
      intro Ω _ _ y
      rw [IsHomeomorph.topologicalKrullDim_eq _
        (asIso (pullback.snd (𝟙 T) y)).hom.homeomorph.isHomeomorph]
      exact topologicalKrullDim_zero_of_discreteTopology _
    have H := constructibleComplete_properBaseChange l E sqh hdT hdT hdS hdS
      l (Fact.out : l.Prime).pos hAnn hlT hlT hlS hlS 0 hf
    have := H.1
    have := H.2.1
    obtain ⟨hF, _, _⟩ := H.2.2
    have := (pbcUniformComplete_isTriangulated S l E hdS hlS).1
    exact ObjectProperty.prop_of_iso _
      ((d.completedPull h).mapIso ((d.pushId T).app K.obj)) (hF K)
  let hRf := hPush f _dimX _dimY _hlX _hlY _hFibres
  let hRf' := hPush f' _dimX' _dimY' _hlX' _hlY' hFibres'
  let hLg := hPull g _dimY' _dimY _hlY' _hlY
  let hLg' := hPull g' _dimX' _dimX _hlX' _hlX
  refine ⟨hRf, hRf', hLg, hLg', ?_⟩
  intro K
  have H := constructibleComplete_properBaseChange l E sq _dimX _dimY _dimX' _dimY'
    l (Fact.out : l.Prime).pos hAnn _hlX _hlY _hlX' _hlY' e _hFibres
  obtain ⟨hF, hG, sF, sG, _, _, η, _, hη⟩ := H.2.2
  have hi : IsIso (constructibleCompleteExchangeComponent sq d K.obj.obj) := by
    rw [← hη K.obj]
    infer_instance
  have : IsIso (ObjectProperty.homMk
      (constructibleCompleteExchangeComponent sq d K.obj.obj)
      (X := ⟨_, hLg ⟨_, hRf K.obj⟩⟩) (Y := ⟨_, hRf' ⟨_, hLg' K.obj⟩⟩)) := by
    exact (ObjectProperty.isIso_hom_iff _).mp hi
  unfold finiteExtensionRationalExchangeComponent
  infer_instance

end AlgebraicGeometry.Scheme
