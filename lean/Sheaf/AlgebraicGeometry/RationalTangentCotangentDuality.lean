/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Rational tangent spaces and cotangent duality

Source: Stacks Project, Tags 0B2E, 0B2C and 0B2F
(blueprint: lem-sc-rational-tangent-cotangent-duality).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- At rational points the dual-number tangent spaces are canonically the duals of the
maximal ideals modulo their squares, and the differential is dual to the stalk-induced map.
The maps `rX`, `rY` are the structural maps from `k` to the residue fields; their
bijectivity expresses rationality, and scalars on tangent and cotangent spaces are
restricted along them, in the forms of
`exists_rationalPoint_tangent_cotangent_linearEquiv`
(lem-sc-rational-point-tangent-derivation-identification). The equivalences `EX`, `EY`
are characterized exactly as there, by the epsilon coefficient `D` of the stalk map of a
tangent vector; `U` is characterized on maximal-ideal representatives.
Source: Stacks Project, Tags 0B2E, 0B2C and 0B2F
(blueprint: lem-sc-rational-tangent-cotangent-duality).

Proof for stage 3:
1. Apply lem-sc-rational-point-tangent-derivation-identification at `x` and `f x`.
   A tangent vector corresponds to a local map `a ↦ residue(a) + D(a) * epsilon`.
   Its derivation kills the square of the maximal ideal, giving the displayed equivalences.
2. By def-weil-locally-ringed-space-morphism the stalk map carries the maximal ideal and
   its square into their counterparts, giving `U` with the representative formula below.
   By def-weil-residue-field and `hf` the induced residue map is compatible with `rX`,
   `rY`; both being bijective it is bijective, and the tangent map of
   def-sc-scheme-tangent-space applies.
3. By lem-weil-pbc-scheme-stalk-map-composition, postcomposition of a tangent vector
   with `f` composes its local ring map with `f.stalkMap x`. Taking epsilon coefficients
   gives `D` precomposed with the stalk map. On maximal-ideal classes this is exactly
   `EY (schemeTangentMap ... theta) = (EX theta).comp U`, the asserted duality.
-/
theorem rational_tangent_cotangent_duality
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X) :
    let RX := X.presheaf.stalk x
    let RY := Y.presheaf.stalk (f x)
    let KX := X.residueField x
    let KY := Y.residueField (f x)
    let rX : k →+* KX :=
      (StructureSheaf.toStalk k (pX x) ≫ pX.stalkMap x ≫ X.residue x).hom
    let rY : k →+* KY :=
      (StructureSheaf.toStalk k (pY (f x)) ≫ pY.stalkMap (f x) ≫ Y.residue (f x)).hom
    Function.Bijective rX → Function.Bijective rY →
    letI : Module k (schemeTangentSpace k X pX x) :=
      Module.compHom (schemeTangentSpace k X pX x) rX
    letI : Module k (schemeTangentSpace k Y pY (f x)) :=
      Module.compHom (schemeTangentSpace k Y pY (f x)) rY
    letI : Module KX (IsLocalRing.CotangentSpace RX) :=
      inferInstanceAs (Module (IsLocalRing.ResidueField RX) (IsLocalRing.CotangentSpace RX))
    letI : Module KY (IsLocalRing.CotangentSpace RY) :=
      inferInstanceAs (Module (IsLocalRing.ResidueField RY) (IsLocalRing.CotangentSpace RY))
    letI : Module k (IsLocalRing.CotangentSpace RX) :=
      Module.compHom (IsLocalRing.CotangentSpace RX) rX
    letI : Module k (IsLocalRing.CotangentSpace RY) :=
      Module.compHom (IsLocalRing.CotangentSpace RY) rY
    ∃ he : Function.Bijective (f.residueFieldMap x).hom,
      ∃ (EX : schemeTangentSpace k X pX x ≃ₗ[k] (IsLocalRing.CotangentSpace RX →ₗ[k] k))
        (EY : schemeTangentSpace k Y pY (f x) ≃ₗ[k] (IsLocalRing.CotangentSpace RY →ₗ[k] k))
        (U : IsLocalRing.CotangentSpace RY →ₗ[k] IsLocalRing.CotangentSpace RX),
        (∀ θ : schemeTangentSpace k X pX x,
          ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber KX)) = x,
            let sharp : RX →+* DualNumber KX :=
              (eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) hx.symm) ≫
                Scheme.stalkClosedPointTo θ.val).hom
            ∃! D : RX → k,
              (∀ a : RX, sharp a =
                TrivSqZeroExt.inl ((X.residue x).hom a) + TrivSqZeroExt.inr (rX (D a))) ∧
              (∀ a : IsLocalRing.maximalIdeal RX,
                EX θ ((IsLocalRing.maximalIdeal RX).toCotangent a) = D a)) ∧
        (∀ θ : schemeTangentSpace k Y pY (f x),
          ∃ hy : θ.val (IsLocalRing.closedPoint (DualNumber KY)) = f x,
            let sharp : RY →+* DualNumber KY :=
              (eqToHom (congrArg (fun z : Y ↦ Y.presheaf.stalk z) hy.symm) ≫
                Scheme.stalkClosedPointTo θ.val).hom
            ∃! D : RY → k,
              (∀ a : RY, sharp a =
                TrivSqZeroExt.inl ((Y.residue (f x)).hom a) + TrivSqZeroExt.inr (rY (D a))) ∧
              (∀ a : IsLocalRing.maximalIdeal RY,
                EY θ ((IsLocalRing.maximalIdeal RY).toCotangent a) = D a)) ∧
        (∀ b : IsLocalRing.maximalIdeal RY,
          ∃ hb : (f.stalkMap x).hom b ∈ IsLocalRing.maximalIdeal RX,
            U ((IsLocalRing.maximalIdeal RY).toCotangent b) =
              (IsLocalRing.maximalIdeal RX).toCotangent ⟨(f.stalkMap x).hom b, hb⟩) ∧
        ∀ θ : schemeTangentSpace k X pX x,
          EY (schemeTangentMap k X Y pX pY f hf x he θ) = (EX θ).comp U := by
  sorry

end AlgebraicGeometry
