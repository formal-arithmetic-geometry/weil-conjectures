module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import Sheaf.AlgebraicGeometry.LocalDvrBaseChange
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility
import Sheaf.AlgebraicGeometry.DivisorClassCurve
import Sheaf.AlgebraicGeometry.GenusInvariant
import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Boundary principal divisors and algebraically closed base change

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
  affine-case proof, unit quotient paragraph (blueprint: lem-sc-affine-unit-divisor-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **Boundary principal divisors are unchanged by algebraically closed base change.**
Let `k ⊆ k'` be algebraically closed, `C` a smooth affine connected curve over `k` with a
smooth proper connected compactification `c : C ↪ X = c.Z`, boundary
`S = {P ∈ X closed, P ∉ C}`, and `X' = X ×_k k'` the compactification `c.baseChange` of
`C' = C ×_k k'`, with boundary `S'`. Then:
* every `P ∈ S` has exactly one point `e P ∈ S'` above it and no other point of `X'` lies over
  `P`, giving a bijection `e : S ≃ S'`, hence `ι = Finsupp.domCongr e`;
* for every unit `u` of `𝒪_C(C)` with pullback `u'` along `C' ⟶ C`, the boundary part of
  `div(u')` on `X'` is `ι` of the boundary part of `div(u)` on `X` (units are viewed in the
  function fields through the restriction maps `φ`, `φ'`, tied to the germs at the points of
  `C`, `C'`);
* `ι` maps the set of boundary divisors of units on `C` onto that on `C'`.

Proof (blueprint): by lem-sc-pic-affine-base-change-compatibility (1), `X'` is a smooth proper
connected compactification of `C'` with boundary `{P' : P ∈ S}`, each `P` being a `k`-rational
point with a single point `P'` above it; this gives `ι`. For a unit `u`, the coefficient of
`[P]` in `div u` is `v_P(u)`, and `v_{P'}(u') = v_P(u)` by lem-sc-local-dvr-base-change.
Hence `ι(L) ⊆ L'`. Conversely, a boundary divisor `D' = ι D` of a unit on `C'` is principal,
so `𝒪_{X'}(D')` is trivial and `deg D = 0`; `𝒪_X(D)` pulls back to `𝒪_{X'}(D')`, and
`Pic⁰(X) → Pic⁰(X')` is the injective Jacobian map `J_X(k) → J_X(k')`, so `D = div f`; then
`f` has order `0` at every closed point of `C`, so `f ∈ 𝒪_C(C)ˣ` by the divisor exact
sequence, and `D ∈ L`.

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
  affine-case proof, unit quotient paragraph (blueprint: lem-sc-affine-unit-divisor-base-change). -/
theorem affine_unit_divisor_base_change
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g] :
    ∃ (_ : IsIntegral c.Z) (_ : IsNoetherian c.Z)
      (_ : IsIntegral (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z)
      (_ : IsNoetherian (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z),
    ∃ (φ : Γ(C, ⊤) →+* c.Z.functionField)
      (φ' : Γ(CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤) →+*
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.functionField),
      (∀ (x : C) (s : Γ(C, ⊤)) (y : c.Z.presheaf.stalk (c.i.base x)),
        c.i.stalkMap x y = C.presheaf.germ ⊤ x trivial s →
          φ s = algebraMap (c.Z.presheaf.stalk (c.i.base x)) c.Z.functionField y) ∧
      (∀ (x : (CategoryTheory.Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :
          Scheme.{u}))
        (s : Γ(CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤))
        (y : (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.presheaf.stalk
          ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base x)),
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.stalkMap x y =
            (CategoryTheory.Limits.pullback f
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).presheaf.germ
              ⊤ x trivial s →
          φ' s = algebraMap
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.presheaf.stalk
              ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base x))
            (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.functionField
            y) ∧
    ∃ e : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base} ≃
        {P : closedPoints (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z //
          P.val ∉
            Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base},
      (∀ P : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base},
        (CategoryTheory.Limits.pullback.fst c.g
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base
            (e P).val.val = P.val.val ∧
          ∀ Q : (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z,
            (CategoryTheory.Limits.pullback.fst c.g
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base Q =
              P.val.val → Q = (e P).val.val) ∧
      (∀ u : Γ(C, ⊤)ˣ,
        Finsupp.subtypeDomain
            (fun P : closedPoints (c.baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z ↦
              P.val ∉
                Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base)
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.div
              (Additive.ofMul (Units.map φ'.toMonoidHom
                (Units.map (CategoryTheory.Limits.pullback.fst f
                  (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop.hom.toMonoidHom
                  u)))) =
          Finsupp.domCongr e
            (Finsupp.subtypeDomain (fun P : closedPoints c.Z ↦ P.val ∉ Set.range c.i.base)
              (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom u))))) ∧
      Finsupp.domCongr e ''
          Set.range (fun u : Γ(C, ⊤)ˣ ↦
            Finsupp.subtypeDomain (fun P : closedPoints c.Z ↦ P.val ∉ Set.range c.i.base)
              (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom u)))) =
        Set.range (fun u' : Γ(CategoryTheory.Limits.pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ ↦
          Finsupp.subtypeDomain
            (fun P : closedPoints (c.baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z ↦
              P.val ∉
                Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base)
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.div
              (Additive.ofMul (Units.map φ'.toMonoidHom u')))) := by
  sorry

end AlgebraicGeometry
