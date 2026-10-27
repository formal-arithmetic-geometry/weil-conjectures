/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.RigidifiedLines
public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent

/-! # Extension of identity-rigidified lines over a regular base

Source: Deligne, Le lemme de Gabber, Section 4.2, printed p.142
(blueprint: lem-sfb-regular-group-rigidified-line-extension).

The restriction functor is the canonical tensor inverse image on line modules with
their actual rigidifications. Cartesian squares allow arbitrary models of base changes.
The second clause specifies its compatibility with every étale change of scheme base.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction across a dense open of a regular locally Noetherian scheme is an
equivalence on identity-rigidified lines of a separated smooth finitely presented
commutative group space with integral geometric fibres. In particular it extends every
object and every specified isomorphism uniquely. The comparison for every étale
change of base is normalized by the existing canonical tensor composition maps.

Source: Deligne, Le lemme de Gabber, Section 4.2, printed p.142
(blueprint: lem-sfb-regular-group-rigidified-line-extension).
Proof:
1. Work over affine opens of S. By lem-sfb-smooth-integral-fibre-vertical-divisors,
G is regular Noetherian separated and G_V is dense. Apply the divisor-line dictionary
lem-sfb-regular-space-divisor-line-dictionary.
2. Choose a rational section of the given line on G_V. Close its prime divisors in
G. The resulting Weil divisor gives an unrigidified extension H.
3. Replace H by H tensor p-star(e-star(H)-dual). Evaluation rigidifies it. On V the
specified original rigidification identifies this corrected extension with the original
line and preserves that rigidification (lem-trf-space-enlarged-etale-ringed-site-model).
4. A specified isomorphism over G_V gives a rational section s of M1-dual tensor M2.
Its divisor is supported outside G_V. The vertical-divisor lemma uniquely writes it
as p-star(D), for a divisor D supported outside V.
5. The divisor-line dictionary identifies this pair with p-star(O(D),s_D). Pullback
along the identity identifies its rational section with 1, since the specified
isomorphism preserves rigidifications. Therefore D=div(1)=0. The section extends
and generates everywhere. Maps agreeing on the dense open agree, proving uniqueness.
6. Glue the affine-local extensions and their comparisons. Uniqueness gives the
cocycle; lem-trf-algebraic-space-invertible-descent supplies effective descent on
an étale scheme atlas and the Hom bijection. Thus restriction is an equivalence.
7. Étale pullback preserves regularity, local Noetherianity, density and the group
hypotheses. Tensor associativity identifies the two restrictions and their identity
rigidifications. Full faithfulness makes extension of this comparison unique and
compatible with further base change. The tensor formula below fixes that comparison.
The empty base and the identity open immersion are included. -/
theorem regularGroupRigidifiedLineExtension
    (S : Scheme.{u}) [IsLocallyNoetherian S] [IsRegular S]
    (G : AlgebraicSpace S) (H : CommutativeSpaceGroup G)
    (hG : IsSmoothIntegralGroupSpace G)
    (V : Scheme.{u}) (j : V ⟶ S) [IsOpenImmersion j] (hj : DenseRange j.base)
    (Gᵥ : AlgebraicSpace S) (pᵥ : Gᵥ ⟶ schemeSpace (Over.mk j)) (i : Gᵥ ⟶ G)
    (hcart : IsPullback i pᵥ (groupSpaceProjection G)
      (groupSchemeMap (Over.homMk j (by simp))))
    (eᵥ : schemeSpace (Over.mk j) ⟶ Gᵥ)
    (we : groupSchemeMap (Over.homMk j (by simp)) ≫ H.identity = eᵥ ≫ i)
    (heᵥ : eᵥ ≫ pᵥ = 𝟙 _) :
    (rigidifiedLinePullback H.identity eᵥ
      (groupSchemeMap (Over.homMk j (by simp))) i we).IsEquivalence ∧
    ∀ (T U : Over S) (a : T ⟶ Over.mk (𝟙 S)) (k : U ⟶ Over.mk j) (d : U ⟶ T),
      Etale a.left → IsPullback k.left d.left j a.left →
      ∀ (G' Gᵥ' : AlgebraicSpace S) (p' : G' ⟶ schemeSpace T)
        (pᵥ' : Gᵥ' ⟶ schemeSpace U) (e' : schemeSpace T ⟶ G')
        (eᵥ' : schemeSpace U ⟶ Gᵥ') (b : G' ⟶ G) (c : Gᵥ' ⟶ Gᵥ) (i' : Gᵥ' ⟶ G'),
        IsPullback b p' (groupSpaceProjection G) (groupSchemeMap a) →
        IsPullback c pᵥ' pᵥ (groupSchemeMap k) →
        IsPullback i' pᵥ' p' (groupSchemeMap d) →
        e' ≫ p' = 𝟙 _ → eᵥ' ≫ pᵥ' = 𝟙 _ →
        ∀ (w₂ : groupSchemeMap a ≫ H.identity = e' ≫ b)
          (w₃ : groupSchemeMap k ≫ eᵥ = eᵥ' ≫ c)
          (w₄ : groupSchemeMap d ≫ e' = eᵥ' ≫ i') (hb : c ≫ i = i' ≫ b),
          ∃ z : rigidifiedLinePullback H.identity eᵥ
                (groupSchemeMap (Over.homMk j (by simp))) i we ⋙
              rigidifiedLinePullback eᵥ eᵥ' (groupSchemeMap k) c w₃ ≅
            rigidifiedLinePullback H.identity e' (groupSchemeMap a) b w₂ ⋙
              rigidifiedLinePullback e' eᵥ' (groupSchemeMap d) i' w₄,
            ∀ L : RigidifiedLines H.identity,
              (rigidifiedLineForget eᵥ').map (z.hom.app L) =
                (moduleTensorComposition c i).hom.app
                    ((rigidifiedLineForget H.identity).obj L) ≫
                  (eqToIso (congrArg moduleTensorPullback hb)).hom.app
                    ((rigidifiedLineForget H.identity).obj L) ≫
                  (moduleTensorComposition i' b).inv.app
                    ((rigidifiedLineForget H.identity).obj L) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
