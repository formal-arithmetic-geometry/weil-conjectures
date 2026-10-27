/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.StrictDirectImageMixedUnitData
import Sheaf.Paper.StrictMixedSystemModels
import Sheaf.Paper.StrictMixedScalarSquare
import Sheaf.Paper.StrictMixedFiniteEvaluation

/-! # Mixed tensor unit of the strict integral direct-image comparison

Source: Stacks Tag 0B56, equation-projection-formula-map.
(blueprint: lem-weil-strict-direct-image-mixed-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.StrictDirectImageMixedUnit
open SfStrictDirectImageScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem scalar_square_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {SX : A ⥤ B} {UX : B ⥤ A} {SY : C ⥤ D} {UY : D ⥤ C}
    (adjX : SX ⊣ UX) (adjY : SY ⊣ UY)
    (G : A ⥤ C) (H : B ⥤ D) (ρ : UX ⋙ G ≅ H ⋙ UY)
    {M : C} {N : A} {P : B} {Q : D}
    (sX : P ≅ SX.obj N) (sY : Q ≅ SY.obj M)
    (r : M ⟶ G.obj N) (t : Q ⟶ H.obj P)
    (hs : sY.inv ≫ t ≫ H.map sX.hom = SY.map r ≫
      (adjY.homEquiv _ _).symm
        (G.map (adjX.unit.app N) ≫ ρ.hom.app (SX.obj N))) :
    (adjY.unit.app M ≫ UY.map sY.inv) ≫ UY.map t =
      r ≫ G.map (adjX.unit.app N ≫ UX.map sX.inv) ≫ ρ.hom.app P := by
  apply (cancel_mono (UY.map (H.map sX.hom))).1
  have ht := congrArg (fun z ↦ adjY.homEquiv M (H.obj (SX.obj N)) z) hs
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply] at ht
  rw [Adjunction.homEquiv_unit] at ht
  simp only [Functor.map_comp, Category.assoc] at ht ⊢
  rw [ht]
  have hρ := ρ.hom.naturality sX.inv
  dsimp only [Functor.comp_map] at hρ
  rw [reassoc_of% hρ]
  simp only [← UY.map_comp, ← H.map_comp,
    sX.inv_hom_id, H.map_id, UY.map_id, Category.comp_id]

private theorem mixedUnit_bijective (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus l E W)
    (SL : CoefficientDerivedSystemCalculus l L W)
    (A : CoefficientExtensionSystems l E L ι W)
    (d : CoefficientExtensionReductionData l E L ι W SE SL A)
    (M : DerivedCategory (scalarReductionSource l E W))
    (Z : coefficientSequenceDerived l L W) :
    Function.Bijective (fun z : SL.reduction.obj
        ((integralScalarExtensionOfUniverses l E L ι W).obj M) ⟶ Z ↦
      mixedUnit l E L ι W SE SL A d M ≫ (restriction l E L ι W).map z) := by
  let s := (coefficientExtensionReductionIso l E L ι W SE SL A d).app M
  let e := (Iso.homCongr s (Iso.refl Z)).trans (A.scalar.adjunction.homEquiv _ _)
  have he : (fun z : SL.reduction.obj
        ((integralScalarExtensionOfUniverses l E L ι W).obj M) ⟶ Z ↦
      mixedUnit l E L ι W SE SL A d M ≫ (restriction l E L ι W).map z) = e := by
    funext z
    simp only [e, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
      Category.comp_id]
    erw [A.scalar.adjunction.homEquiv_unit]
    simp only [s, mixedUnit, Functor.map_comp, Category.assoc, Iso.app_inv]
  rw [he]
  exact e.bijective

/-- Mixed tensor-unit normalization of the inverse prescribed integral scalar
comparison, at every finite exponent and simultaneously on coherent quotient systems.

Source: Stacks Tag 0B56, equation-projection-formula-map; the agent-extracted
normalization of the strict-image comparison
(blueprint: lem-weil-strict-direct-image-mixed-unit).

Proof:
1. Work on ringed sequence sites. The normalized direct-image compositor supplies
restrictionComparison, whose evaluations are the inverse restricted K-injective
resolution maps (lem-weil-proetale-direct-image-restriction-of-scalars and
lem-weil-pbc-ringed-topoi-derived-pushforward-composition). Its conjugate is the
pullback/scalar square by lem-sfb-ringed-comparison-tensor-adjunction.
2. Construct CE and CL from the ordinary sectionwise limit comparison. Transpose
F(u) followed by the direct-image/limit comparison through reduction/limit. The
triangle identity gives r R(psi)=alpha. The actual counit projects to the adjunct
of the total-limit projection by lem-coef-derived-system-evaluation-calculus and
lem-coef-sequence-pushforward-limit-projections; constructibility makes r invertible.
3. Use lem-pur-coefficient-extension-reduction-model for dX,dY. On one flat-term
K-flat representative association sends (x tensor a) tensor b to x tensor ab and
units send x to (x tensor 1) tensor 1. The completion augmentation has zero shifted
Roos coordinate by lem-weil-finite-free-completed-scalar-comparison and
lem-trf-completion-unit-strict-quotient-model. The actual system triangle gives
s R(chi)=e and U(s) eta=zeta, retaining every quotient transition.
4. Let q be the coefficient-adjunction mate of restrictionComparison's inverse.
Its defining equation is U(q) zeta=d G(zeta). Iterated square mates identify q
with the geometric counit/tensor mate. Paste coefficient/reduction squares in both
orders using lem-weil-pbc-mate-pasting and lem-trf-iterated-square-mates. Their
left-adjoint comparisons agree on x tensor s tensor b by multiplication of the
same scalars (lem-sfb-successive-derived-quotient-normalization). This gives the
system equality for ambient comparisons before any finite evaluation.
5. Substitute the conjugation equation HasIntegralLaws for b, r R(psi)=alpha,
and s R(chi)=e. Naturality cancels reconstruction and completion isomorphisms.
Apply U and precompose with eta. Move zeta past r by naturality, apply the
coefficient-mate equation, and cancel the invertible U G(s). The result is
the system equation in CoherentLaws in the derived sequence category itself.
6. Evaluate that constructed equality. lem-coef-semilinear-derived-sections
identifies transposes, units, counits and direct images with their finite versions,
giving FiniteLaws. The coefficient Hom adjunction is a bijection, both on the
sequence site and at every level. Its injectivity is exactly uniqueness of the
B-linear lift. Association coherence is already built into scalar systems and the
reduction-model comparisons. No flatness of quotient inclusions or finite Tor
amplitude is used, and no faithfulness of derived evaluations is asserted. -/
theorem strictDirectImageMixedUnit
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (D : IntegralComparisons l Ω f) (_hD : HasIntegralLaws l Ω f D)
    (e j : AlgebraicallyClosedCoefficients.Index l Ω) (h : e ≤ j) :
    FiniteLaws l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) f
      (D.integral e) (D.integral j) (D.integralComparison e j h).symm ∧
    CoherentLaws l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) f
      (D.integral e) (D.integral j) (D.integralComparison e j h).symm := by
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e
  let L := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j
  let ι := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h
  obtain ⟨EX, EY, LX, LY, AX, AY, dX, dY, CE, CL, C,
    hEX, hEY, hLX, hLY, hPE, hPL, hC, hRE, hRL, hMX, hMY, hIE, hIL⟩ :=
    strictMixedSystemModels l E L ι k _hl f (D.integral e) (D.integral j)
  have hc : CoherentLaws l E L ι f (D.integral e) (D.integral j)
      (D.integralComparison e j h).symm := by
    refine ⟨EX, EY, LX, LY, AX, AY, dX, dY, CE, CL, C,
      hEX, hEY, hLX, hLY, hPE, hPL, hC, hRE, hRL, hMX, hMY, hIE, hIL, ?_, ?_⟩
    · intro K
      exact scalar_square_unit AX.scalar.adjunction AY.scalar.adjunction
        (FrobeniusExchange.systemDirect l E f) (FrobeniusExchange.systemDirect l L f)
        C.derived.symm
        ((coefficientExtensionReductionIso l E L ι X EX LX AX dX).app K.obj)
        ((coefficientExtensionReductionIso l E L ι Y EY LY AY dY).app
          ((D.integral e).image.obj K).obj)
        (reductionMap l E f EX EY CE (D.integral e) K)
        (LY.reduction.map (((D.integralComparison e j h).inv.app K).hom) ≫
          reductionMap l L f LX LY CL (D.integral j)
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K))
        (by simpa only [Category.assoc, coefficientExtensionSystem,
          SemilinearSections.ScalarData.T, Functor.comp_obj,
          Iso.app_hom, Iso.app_inv, Iso.symm_hom] using
          (strictMixedScalarSquare l k _hl Ω f D _hD e j h
            EX EY LX LY AX AY dX dY CE CL C K))
    · intro K Z
      exact mixedUnit_bijective l E L ι Y EY LY AY dY _ Z
  exact ⟨strictMixedFiniteEvaluation l E L ι f _ _ _ hc, hc⟩

attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.StrictDirectImageMixedUnit
