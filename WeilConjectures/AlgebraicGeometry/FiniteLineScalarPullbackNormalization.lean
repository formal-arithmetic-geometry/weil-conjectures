/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.OrdinarySemilinearPullbackSquare
import WeilConjectures.AlgebraicGeometry.ScalarPullbackSingleTransposes
import all WeilConjectures.AlgebraicGeometry.RationalP1FirstScalarTrace

/-! # Finite Tate-line scalar/pullback normalization

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
`sk-prop-diagonal-tower-coefficients.proof.md`, paragraph (3), with the integral and
rational paragraphs of `sk-prop-sfb-cartesian-coefficients-twists.proof.md`.
(blueprint: lem-sfb-finite-line-scalar-pullback-normalization).

## Main statements

- `finiteLine_scalarPullbackNormalization_integral`: the case `a : ℤ_ℓ → 𝒪_E`, with the
  root-projection-normalized bottom-field transition `integralLineMap` and the canonical
  root-projection comparisons `spIntegralComparison`.
- `finiteLine_scalarPullbackNormalization_rational`: the case `a : 𝒪_E → E`, with the
  balanced-tensor unit `rationalLineMap` and the unique scalar-extension-normalized rational
  comparison of `spRationalComparison_existsUnique`.

Both conclude `ScalarPullbackEndpointSquare`, whose single field is the item's degree-two
equation `α_{L_{R,S}[2]} ≫ F_T(e_S^{[2]}) ≫ d_T^{[2]} = S_{a,X}(d_R^{[2]}) ≫ e_X^{[2]}`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] derivedUpper singlePullback
  Endpoint.shift PullEndpoint.shift scalarPullbackComparison
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Mod.derivedExtendMapDerivedCategoryAdjunction

attribute [local irreducible] CondensedRing.upperStarLowerStarAdjunction
  ProEtale.upperStarLowerStarAdjunction CondensedRing.upperStar

set_option maxHeartbeats 600000 in
-- Keep the fixed ordinary adjunctions abstract during endpoint normalization.
private theorem ordinarySquare_of_underlying
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules R S} {M' : Modules R X}
    {N : Modules T S} {N' : Modules T X}
    {v : M.X ⟶ N.X} {w : M'.X ⟶ N'.X}
    {p : (upperStar Ab.{u + 1} f).obj M.X ⟶ M'.X}
    {q : (upperStar Ab.{u + 1} f).obj N.X ⟶ N'.X}
    (dR : PullEndpoint R f M M' p) (eS : Endpoint a M N v)
    (eX : Endpoint a M' N' w) (dT : PullEndpoint T f N N' q)
    (h : (upperStar Ab.{u + 1} f).map v ≫ q = p ≫ w) :
    (CondensedRing.upperStar R f).map eS.semilinear.hom ≫
        (CondensedRing.comapUpperStarIso a f).inv.app N ≫
        (Mod.comap (coefficientMap a X)).map dT.iso.hom =
      dR.iso.hom ≫ eX.semilinear.hom := by
  apply CondensedRing.ordinarySemilinearPullbackSquare
    (R := R) (T := T) a (X := X) (S := S) f M N M' N'
    eS.semilinear.hom eX.semilinear.hom dR.iso.hom dT.iso.hom
  simpa only [eS.semilinear.underlying, eX.semilinear.underlying,
    dR.normalization, dT.normalization, Equiv.symm_apply_apply] using h

set_option maxHeartbeats 600000 in
-- The fixed derived comparison objects need a larger normalization budget.
private theorem endpointSquare_of_underlying
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules R S} {M' : Modules R X}
    {N : Modules T S} {N' : Modules T X}
    {v : M.X ⟶ N.X} {w : M'.X ⟶ N'.X}
    {p : (upperStar Ab.{u + 1} f).obj M.X ⟶ M'.X}
    {q : (upperStar Ab.{u + 1} f).obj N.X ⟶ N'.X}
    (dR : PullEndpoint R f M M' p) (eS : Endpoint a M N v)
    (eX : Endpoint a M' N' w) (dT : PullEndpoint T f N N' q)
    (h : (upperStar Ab.{u + 1} f).map v ≫ q = p ≫ w) :
    ScalarPullbackEndpointSquare a f
      (M₀ := M) (M₀' := M') (M := N) (M' := N')
      (m₀ := p) (m := q) (v := v) (v' := w) dR eS eX dT := by
  have ho := ordinarySquare_of_underlying (R := R) (T := T) a f
    (M := M) (M' := M') (N := N) (N' := N')
    (v := v) (w := w) (p := p) (q := q) dR eS eX dT h
  have hs := scalarPullbackSingleTransposes (R := R) (T := T) a
    (X := X) (S := S) f (M := M) (M' := M') (N := N) (N' := N')
    v w p q eS eX dR dT
  refine ⟨?_⟩
  apply ((Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap a X)).homEquiv
      ((derivedUpper R f).obj
        (((DerivedCategory.singleFunctor (Modules R S) 0).obj M)⟦(2 : ℤ)⟧))
      (((DerivedCategory.singleFunctor (Modules T X) 0).obj N')⟦(2 : ℤ)⟧)).injective
  apply (cancel_mono
    (((Mod.comap (coefficientMap a X)).mapDerivedCategory.commShiftIso
      (2 : ℤ)).hom.app ((DerivedCategory.singleFunctor (Modules T X) 0).obj N'))).mp
  apply (cancel_mono
    ((((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor
      0).hom.app N')⟦(2 : ℤ)⟧')).mp
  simpa only [Category.assoc] using hs.1.trans (by rw [ho]; exact hs.2.symm)

-- Keep the native inverse-limit module abstract in the endpoint calculations.
attribute [local irreducible] spIntegralTwist

/-- Integral finite-line normalization for the actual bottom-field-to-integral
coefficient map and the root-projection-normalized pullback comparisons.
Source: blueprint coefficient changes, paragraph (3)
(blueprint: lem-sfb-finite-line-scalar-pullback-normalization).

Proof:
1. Put `v = eS.semilinear.hom`, `w = eX.semilinear.hom`, `p = e₀.iso.hom`,
   `q = e.iso.hom`. The semilinear normalizations give underlying maps `integralLineMap`
   on `S` and on `X`. The PullEndpoint normalizations, followed by the inverse ordinary
   sheaf-adjunction bijection, give `p♭ = spIntegralComparison f l (bottomField l)` and
   `q♭ = spIntegralComparison f l E`. The needed underlying square is therefore
   `f⁻¹(u_S) ≫ m_T = m_R ≫ u_X`.
2. Test this square after every target finite root projection. Each path factors through
   `f⁻¹` of the corresponding bottom-field root projection. At level `n` both maps send a
   local generator `u ⊗ b` to `res_f(u) ⊗ i_n(b)`: root pullback is the canonical root
   comparison and the coefficient factors agree by the coefficient-change square. Balanced
   tensor relations extend this to finite sums and sheafification. The target is the
   specified inverse limit, so equality at every coordinate gives equality of the sheaf
   maps. Restricting along `ℤ_ℓ → 𝒪_{ℚ_ℓ}` does not change these underlying arrows.
3. Apply the ordinary semilinear pullback-square lemma
   (lem-sfb-ordinary-semilinear-pullback-square) to `v, w, p, q`, with its specified
   `G_R`, ordinary restrictions and the coefficient-square comparison `σ`. Step 1 gives
   its `p♭, q♭` and step 2 its underlying-square hypothesis. Hence
   `G_R(v) ≫ σ⁻¹ ≫ V_X⁰(q) = p ≫ w`.
4. By the two shifted transpose formulas of lem-sfb-scalar-pullback-single-transposes,
   the transposes of both sides of the goal agree by step 3, functoriality of the
   degree-zero single functor and shift by two. Cancel the common isomorphism `z` and use
   injectivity of the derived scalar-adjunction Hom-bijection on `X`. This is the field
   `comm`. -/
theorem finiteLine_scalarPullbackNormalization_integral
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)]
    (e₀ : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X) (spIntegralComparison f l (bottomField l)))
    (eS : Endpoint (integralMap l E) (zlLine l S) (spIntegralTwist S l E)
      (integralLineMap l E S))
    (eX : Endpoint (integralMap l E) (zlLine l X) (spIntegralTwist X l E)
      (integralLineMap l E X))
    (e : PullEndpoint (Profinite.padicIntegersRingObj.{u} l E.1) f
      (spIntegralTwist S l E) (spIntegralTwist X l E)
      (spIntegralComparison f l E)) :
    ScalarPullbackEndpointSquare (integralMap l E) f e₀ eS eX e := by
  apply endpointSquare_of_underlying (integralMap l E) f e₀ eS eX e
  obtain ⟨ρ, κ, hρ, hκ, hcart, hqbar, hi, hrat, hroot⟩ := spTwists_cartesian f l
  exact hi (bottomField l) E
    (show (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≤ E.1 from bot_le)

set_option maxHeartbeats 600000 in
-- Reuse the normalized tensor-unit square and uniqueness of its comparison.
private theorem rationalLineMap_pull_natural
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)]
    (m : (upperStar Ab.{u + 1} f).obj (spRationalTwist S l E).X ⟶
      (spRationalTwist X l E).X)
    (hm : m = Classical.choose (spRationalComparison_existsUnique f l E)) :
    (upperStar Ab.{u + 1} f).map (rationalLineMap l E S) ≫ m =
      spIntegralComparison f l E ≫ rationalLineMap l E X := by
  have he := (Classical.choose_spec (spRationalComparison_existsUnique f l E)).2
    ((RationalP1.adicComparison l f).rational E)
    ((RationalP1.adicComparison l f).rational_scalar E)
  rw [hm, ← he]
  exact RationalP1.rational_root_scalar_square l E f

-- Keep the native scalar-extension endpoint conversion within this declaration.
set_option maxHeartbeats 600000 in
-- Specializing the derived endpoint square compares the native scalar-extension modules.
/-- Rational finite-line normalization for the actual integral-to-rational
balanced-tensor unit and its scalar-extension-normalized pullback comparison. The
comparison `m` is pinned by `hm` to the unique map of `spRationalComparison_existsUnique`
(sk-prop-sfb-cartesian-coefficients), not an arbitrary isomorphism of lines.
Source: blueprint coefficient changes, paragraph (3)
(blueprint: lem-sfb-finite-line-scalar-pullback-normalization).

Proof:
1. Put `v = eS.semilinear.hom`, `w = eX.semilinear.hom`, `p = e₀.iso.hom`,
   `q = e.iso.hom`. The semilinear normalizations give underlying maps `rationalLineMap`
   on `S` and on `X`. The PullEndpoint normalizations, followed by the inverse ordinary
   sheaf-adjunction bijection, give `p♭ = spIntegralComparison f l E` and `q♭ = m`. The
   needed underlying square is `f⁻¹(u_S) ≫ m = spIntegralComparison f l E ≫ u_X`.
2. `u_V` is the balanced-tensor unit `x ↦ 1 ⊗ x`. By `hm` and the defining equation of
   `spRationalComparison_existsUnique`, `m` sends a pulled local tensor `b ⊗ x` to
   `α_f^E(b) ⊗ m_R(x)`. Both maps out of `f⁻¹ L_{R,S}` therefore send a local `x` to
   `1 ⊗ m_R(x)`, as the coefficient comparison is unital. These local formulas respect
   restriction and glue through sheafification.
3. Apply the ordinary semilinear pullback-square lemma
   (lem-sfb-ordinary-semilinear-pullback-square) to `v, w, p, q`, with its specified
   `G_R`, ordinary restrictions and the coefficient-square comparison `σ`. Step 1 gives
   its `p♭, q♭` and step 2 its underlying-square hypothesis. Hence
   `G_R(v) ≫ σ⁻¹ ≫ V_X⁰(q) = p ≫ w`.
4. By the two shifted transpose formulas of lem-sfb-scalar-pullback-single-transposes,
   the transposes of both sides of the goal agree by step 3, functoriality of the
   degree-zero single functor and shift by two. Cancel the common isomorphism `z` and use
   injectivity of the derived scalar-adjunction Hom-bijection on `X`. This is the field
   `comm`. -/
theorem finiteLine_scalarPullbackNormalization_rational
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)]
    (e₀ : PullEndpoint (Profinite.padicIntegersRingObj.{u} l E.1) f
      (spIntegralTwist S l E) (spIntegralTwist X l E)
      (spIntegralComparison f l E))
    (eS : Endpoint (padicIntegersRingObjToContinuousMapRingObj l E)
      (spIntegralTwist S l E) (spRationalTwist S l E)
      (rationalLineMap l E S))
    (eX : Endpoint (padicIntegersRingObjToContinuousMapRingObj l E)
      (spIntegralTwist X l E) (spRationalTwist X l E)
      (rationalLineMap l E X))
    (m : (upperStar AddCommGrpCat.{u + 1} f).obj (spRationalTwist S l E).X ⟶
      (spRationalTwist X l E).X)
    (hm : m = Classical.choose (spRationalComparison_existsUnique f l E))
    (e : PullEndpoint (Profinite.continuousMapRingObj.{u} E.1) f
      (spRationalTwist S l E) (spRationalTwist X l E) m) :
    ScalarPullbackEndpointSquare (padicIntegersRingObjToContinuousMapRingObj l E)
      f e₀ eS eX e := by
  apply endpointSquare_of_underlying
    (padicIntegersRingObjToContinuousMapRingObj l E) f
    (M := spIntegralTwist S l E) (M' := spIntegralTwist X l E)
    (N := spRationalTwist S l E) (N' := spRationalTwist X l E)
    (v := rationalLineMap l E S) (w := rationalLineMap l E X)
    (p := spIntegralComparison f l E) (q := m) e₀ eS eX e
  exact rationalLineMap_pull_natural l E f m hm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
