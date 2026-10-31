/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarBalancingExistence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarLineNormalizationOfBalancing
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceCompatibilitiesOfBalancing

/-! # Existence of normalized finite Tate scalar balancing families -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Existence of the normalized finite Tate balancing family and its compatibility laws.
This is the construction part of the normalization theorem, without uniqueness or the
comparison for an arbitrary flat sheaf.

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4
(blueprint: lem-pur-finite-tate-scalar-source-existence).

Proof: define the rank-one balancing by the adjoint of the root generator map.
On generators it sends (a tensor z) tensor b to phi(a)b tensor z. The inverse
inserts 1 in the old coefficient factor. The balancing relations make these maps
inverse and compatible with restrictions; hence they induce inverse sheaf maps.
Use the specified ordinary scalar oplax unit at degree zero and the ordinary
oplax tensorator recursively for positive powers. The root-generator formula is
preserved by the recursion, because the tensorator inserts 1 in the first new
coefficient factor and the product of the other coefficients in the second.
The degree-zero and successor equations then hold by construction.

Each Tate power is flat. Its single complex is K-flat, so the scalar adjunction
transpose agrees with the representative comparison and is invertible. The
specified scalar/shift comparison gives the shifted line isomorphisms. At zero
power, ordinary multiplication is the normalized scalar unit. Naturality of the
shift-zero comparison transports this equality to the required zero-line equation.
The specified source map is the tensorator followed by scalar/pullback and the line
map, hence is invertible for every unbounded input. Finally, apply the published
scalar tensor-unit and scalar/pullback-unit coherence. Naturality transports the
left-unit equation through the single/unit maps. Cancel the scalar/pullback
isomorphism to obtain the coefficient-unit square. Transport the scalar right-unit
equation through the zero-line equality to obtain the zero-power source equation.
All arrows are the specified comparisons; no flatness of B over A is used. -/
theorem finite_tate_scalar_source_normalization_exists [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x)) :
    ∃ β : ∀ r : ℕ,
        (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
          Scheme.finiteEtaleTateTwist X N B hB r,
      IsFiniteTateScalarBalancing φ N hA hB X β ∧
      IsFiniteTateScalarLineNormalized φ N hA hB X β ∧
      IsFiniteTateScalarSourceInvertible φ N hA hB X β ∧
      IsFiniteTateScalarSourceUnitNormalized φ N hA hB X β ∧
      IsFiniteTateScalarSourceZeroNormalized φ N hA hB X β  := by
  obtain ⟨β, hβ⟩ := finite_tate_scalar_balancing_exists φ N hN hA hB X hX
  have hline := finite_tate_scalar_line_normalization_of_balancing
    φ N hN hA hB X hX β hβ
  have hsource := finite_tate_scalar_source_compatibilities_of_balancing
    φ N hN hA hB X hX β hβ hline
  exact ⟨β, hβ, hline, hsource.1, hsource.2.1, hsource.2.2⟩

end WeilConjectures.PurityFiniteSetting
