/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.CompleteProetale
public import Sheaf.Paper.UniformCompleteTriangulated
import Sheaf.Paper.CompletedConstructiblePreservation
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.CompletedDirectImageLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Constructible complete proper base change

Source: blueprint order 1356; Stacks 09C9 and 09C1
(blueprint: cor-weil-pbc-constructible-complete).
The full category and its actual completed coefficient ring are the published ones.
All components are the specified ordered-composite exchange of the coefficient datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A]
variable {X' X Y' Y : Scheme.{u}}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The source composite of the published ordinary direct image and completed pullback.
Source: blueprint order 1356 (blueprint: cor-weil-pbc-constructible-complete). -/
abbrev constructibleCompleteSource (f : X ⟶ Y) (g : Y' ⟶ Y)
    (d : AdicCoefficientDatum A) := d.push f ⋙ d.completedPull g

/-- The target composite of the published completed pullback and ordinary direct image.
Source: blueprint order 1356 (blueprint: cor-weil-pbc-constructible-complete). -/
abbrev constructibleCompleteTarget (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (d : AdicCoefficientDatum A) := d.completedPull g' ⋙ d.push f'

/-- Exactly the published ordered-composite exchange, with its actual coefficient action.
Source: blueprint order 1356 (blueprint: cor-weil-pbc-constructible-complete). -/
abbrev constructibleCompleteExchangeComponent
    (sq : ChosenCartesianSquare g' f' f g) (d : AdicCoefficientDatum A)
    (K : d.derived X) :
    (constructibleCompleteSource f g d).obj K ⟶
      (constructibleCompleteTarget g' f' d).obj K :=
  d.completedExchange sq K

private theorem coefficientPrime_dvd_annihilator
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (N : ℕ) (hN : (N : Padic.coefficientExtensionRing l E 1) = 0) : l ∣ N := by
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hg : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmem : (N : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    rw [← hg]
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    change (Ideal.Quotient.mk
      (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1))
      (N : Padic.coefficientExtensionIntegers l E) = 0 at hN
    rw [pow_one] at hN
    exact hN
  have hlt := (h.2.1 (N : Padic.coefficientExtensionIntegers l E)).1 hmem
  have hext := spectralNorm_extends (K := ℚ_[l]) (L := E) (N : ℚ_[l])
  apply Padic.norm_natCast_lt_one_iff.mp
  change spectralNorm ℚ_[l] E (N : E) < 1 at hlt
  rw [← map_natCast (algebraMap ℚ_[l] E), hext] at hlt
  exact hlt

private theorem completedPull_exact
    {U V : Scheme.{u}} (g : U ⟶ V) (d : AdicCoefficientDatum A) :
    ∃ s : (d.completedPull g).CommShift ℤ,
      @Functor.IsTriangulated _ _ _ _ _ _ (d.completedPull g) s _ _ _ _ _ _ _ _ := by
  obtain ⟨s, hs⟩ := (completedReductionTower_properties V d).2.1
  let := s
  have := hs
  unfold AdicCoefficientDatum.completedPull
  exact ⟨inferInstance, inferInstance⟩

private def completedExchangeNatTrans
    (sq : ChosenCartesianSquare g' f' f g) (d : AdicCoefficientDatum A) :
    constructibleCompleteSource f g d ⟶ constructibleCompleteTarget g' f' d := by
  let p : d.push f' ⋙ completedReductionTower Y' d ⟶
      completedReductionTower X' d ⋙ d.towerPush f' :=
    { app K := d.towerProjection f' K
      naturality K H k := (d.towerProjection_properties f' K).2.1 H k }
  exact Functor.whiskerRight
    (Functor.whiskerLeft (d.push f) (d.reductionTowerPullbackIso g).hom ≫
      Functor.whiskerRight (d.integralExchange sq) (completedReductionTower Y' d) ≫
      Functor.whiskerLeft (d.pull g') p ≫
      Functor.whiskerRight (d.reductionTowerPullbackIso g').inv (d.towerPush f'))
    (completedRlim Y' (d.completedRing Y')) ≫
      Functor.whiskerLeft (completedReductionTower X d ⋙ d.towerPull g')
        (d.directImageRlimIso f').inv

private theorem completedExchangeNatTrans_app
    (sq : ChosenCartesianSquare g' f' f g) (d : AdicCoefficientDatum A)
    (K : d.derived X) :
    (completedExchangeNatTrans sq d).app K = d.completedExchange sq K := by
  dsimp [completedExchangeNatTrans, AdicCoefficientDatum.completedExchange,
    AdicCoefficientDatum.towerV', AdicCoefficientDatum.towerH',
    AdicCoefficientDatum.towerV]
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc]

/-- Proper base change restricts to a natural isomorphism of ordinary triangulated
functors on the recorded full bounded constructible complete subcategories. The last
equality identifies every component definitionally with AdicCoefficientDatum.completedExchange,
the very morphism whose invertibility completeProetale_isIso asserts.
Source: blueprint order 1356; Stacks 09C9 and 09C1
(blueprint: cor-weil-pbc-constructible-complete).
Proof:
1. Membership supplies intrinsic completeness and compatible retained etale origins.
Apply completeProetale_isIso to the specified completed exchange component.
2. Uniform local models in [d0,d1] and the common perfect-quotient resolution in
[-r,0] give the common reduction interval [d0-r,d1]. Detect vanishing on each
stratum cover and then on etale-origin cohomology stalks; the strata need not cover
in the pro-etale topology.
3. Apply pbc_preservation_constructible to this interval. Both displayed endpoints,
as well as the two intermediate outputs, satisfy all three membership clauses.
4. pbcUniformComplete_isTriangulated supplies the inherited triangulations. Reduction
and strict tower pullback are exact total left derivations, and Rlim and direct image
are exact total right derivations. Their composites restrict through the full
subcategories, retaining the ambient maps, shift comparisons and triangles.
5. Naturality of the specified completed exchange holds for every morphism.
Fullness retains its components and their inverses. The naturality equality implies
naturality of the inverse by multiplying by the inverse components on both sides.
Thus these exact functors have the asserted natural isomorphism with precisely the
specified components, without requiring functorial cones in an ordinary category. -/
theorem constructibleComplete_properBaseChange
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
    (N : ℕ) (_hN : 0 < N)
    (_hAnn : (N : Padic.coefficientExtensionRing l E 1) = 0)
    (_hNX : IsUnit (N : Γ(X, ⊤))) (_hNY : IsUnit (N : Γ(Y, ⊤)))
    (_hNX' : IsUnit (N : Γ(X', ⊤))) (_hNY' : IsUnit (N : Γ(Y', ⊤)))
    (e : ℕ)
    (_hFibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    ObjectProperty.IsTriangulated (IsPbcBoundedConstructibleComplete X l E) ∧
    ObjectProperty.IsTriangulated (IsPbcBoundedConstructibleComplete Y' l E) ∧
    ∀ [ObjectProperty.IsTriangulated (IsPbcBoundedConstructibleComplete X l E)]
      [ObjectProperty.IsTriangulated (IsPbcBoundedConstructibleComplete Y' l E)],
    ∃ (hF : ∀ K : ObjectProperty.FullSubcategory
        (IsPbcBoundedConstructibleComplete X l E),
        IsPbcBoundedConstructibleComplete Y' l E
          ((constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)).obj K.obj))
      (hG : ∀ K : ObjectProperty.FullSubcategory
        (IsPbcBoundedConstructibleComplete X l E),
        IsPbcBoundedConstructibleComplete Y' l E
          ((constructibleCompleteTarget g' f'
            (pbcPadicCoefficientDatum l E)).obj K.obj)),
    ∃ (_sF : (ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)) hF).CommShift ℤ)
      (_sG : (ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)) hG).CommShift ℤ),
    @Functor.IsTriangulated _ _ _ _ _ _ (ObjectProperty.lift
        (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)) hF)
      _sF _ _ _ _ _ _ _ _ ∧
    @Functor.IsTriangulated _ _ _ _ _ _ (ObjectProperty.lift
        (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)) hG)
      _sG _ _ _ _ _ _ _ _ ∧
    ∃ η : ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)) hF ≅
      ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)) hG,
      @NatTrans.CommShift _ _ _ _ _ _ η.hom ℤ _ _ _ _sF _sG ∧
      ∀ K : ObjectProperty.FullSubcategory
        (IsPbcBoundedConstructibleComplete X l E),
        (η.hom.app K).hom =
          constructibleCompleteExchangeComponent sq (pbcPadicCoefficientDatum l E) K.obj := by
  have hlN : l ∣ N := coefficientPrime_dvd_annihilator l E N _hAnn
  have hlX : IsUnit (l : Γ(X, ⊤)) :=
    isUnit_of_dvd_unit (map_dvd (Nat.castRingHom _) hlN) _hNX
  have hlY' : IsUnit (l : Γ(Y', ⊤)) :=
    isUnit_of_dvd_unit (map_dvd (Nat.castRingHom _) hlN) _hNY'
  refine ⟨(pbcUniformComplete_isTriangulated X l E _dimX hlX).2,
    (pbcUniformComplete_isTriangulated Y' l E _dimY' hlY').2, ?_⟩
  intro instX instY'
  let d := pbcPadicCoefficientDatum l E
  have hp (K : ObjectProperty.FullSubcategory (IsPbcBoundedConstructibleComplete X l E)) :=
    d.constructible_preservation sq _dimX _dimY _dimX' _dimY' N _hN
      (by
        apply (Ideal.Quotient.eq_zero_iff_mem).2
        have hm := (Ideal.Quotient.eq_zero_iff_mem).1 _hAnn
        simpa only [d, pbcPadicCoefficientDatum, Padic.coefficientExtensionIdeal,
          pow_one] using hm)
      _hNX _hNY _hNX' _hNY' e _hFibres K.obj K.property
  let hF := fun K ↦ (hp K).2.1
  let hG := fun K ↦ (hp K).2.2.2
  refine ⟨hF, hG, ?_⟩
  obtain ⟨s, hs⟩ := completedPull_exact g d
  let := s
  let := hs
  let F := ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
    (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
      constructibleCompleteSource f g d) hF
  let G := ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
    (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
      constructibleCompleteTarget g' f' d) hG
  let τ : F ⟶ G :=
    { app K := ⟨(completedExchangeNatTrans sq d).app K.obj⟩
      naturality K H k := by
        apply ObjectProperty.hom_ext
        exact (completedExchangeNatTrans sq d).naturality k.hom }
  have hτ (K : ObjectProperty.FullSubcategory
      (IsPbcBoundedConstructibleComplete X l E)) : IsIso (τ.app K) := by
    have : IsIso ((completedExchangeNatTrans sq d).app K.obj) := by
      rw [completedExchangeNatTrans_app]
      exact completeProetale_isIso d sq K.obj K.property.1 K.property.2.2
    have : IsIso ((ObjectProperty.ι
        (IsPbcBoundedConstructibleComplete Y' l E)).map (τ.app K)) := this
    exact isIso_of_reflects_iso (τ.app K)
      (ObjectProperty.ι (IsPbcBoundedConstructibleComplete Y' l E))
  have := hτ
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  let η : F ≅ G := asIso τ
  let : F.CommShift ℤ := inferInstance
  have : F.IsTriangulated := inferInstance
  let : G.CommShift ℤ := Functor.CommShift.ofIso η ℤ
  have : NatTrans.CommShift η.hom ℤ := Functor.CommShift.ofIso_compatibility η ℤ
  refine ⟨inferInstance, inferInstance, inferInstance,
    Functor.isTriangulated_of_iso η, η, inferInstance, ?_⟩
  intro K
  exact completedExchangeNatTrans_app sq d K.obj

end AlgebraicGeometry.Scheme
