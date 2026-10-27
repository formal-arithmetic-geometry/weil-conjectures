/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CubicalTensorPowerIso
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Quadratic multiplication for symmetric cubical rigidified lines

Source: Moret-Bailly, Pinceaux de varietes abeliennes, I 5.5; the cube substitutions
in blueprint sec-abelian-varieties/sk-prop-av-mult-n-pullback/lem-sc-mult-n-pullback.
(blueprint: lem-sfb-cubical-symmetric-multiplication-square)
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.CubicalRigidifiedLine

/-- Multiplication by a positive integer pulls a symmetric cubical rigidified line back
to its square-exponent tensor power, preserving rigidifications and cube sections.
Multiplicative notation on Hom(G,G) denotes the additive group-scheme law; the bundled
power below is the sum of d copies of the identity homomorphism.

Source: Moret-Bailly I 5.5, used in II 3.3.3
(blueprint: lem-sfb-cubical-symmetric-multiplication-square).

Proof: Put A_j = [j]*L. Tensor products, duals and homomorphism pullbacks preserve
cubical structures by their tensor-frame formulas; the pullback/tensor and composition
comparisons are lem-weil-pbc-invertible-pullback-tensor. Evaluation cancels dual factors
and their inverse cube sections. The rigidification gives A_0 = 1 and A_1 = L.
By lem-sfb-cube-section-cubical-compatibility, pulling the actual cube section along
(a,b,c) gives the cubical relation
A(a+b+c) tensor A(a) tensor A(b) tensor A(c) =
A(a+b) tensor A(a+c) tensor A(b+c), with zero factors trivialized by the rigidification.
Apply this at (id,id,-id), and use the supplied cubical symmetry, to obtain A_2 = L^4.
For n >= 1 apply it at (id,id,[n-1]) to get
A_(n+1) tensor L^2 tensor A_(n-1) = A_2 tensor A_n^2.
Induct simultaneously on the consecutive pair A_(n-1), A_n, starting with A_0,A_1.
Tensor cancellation gives exponent 4+2*n^2-2-(n-1)^2 = (n+1)^2 at the next step.
All identifications preserve the rigidification and the actual cube section. This
proves both clauses of IsTensorPowerIso. No division or invertibility of d is used. -/
theorem symmetric_multiplication_square {S : Scheme.{u}} (G : Over S) [CommGrpObj G]
    (L : CubicalRigidifiedLine G) (symmetry : Iso (L.pullback (𝟙 G)⁻¹) L)
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ f : (L.pullback ((𝟙 (Grp.mk G) ^ d).hom.hom)).line ≅ L.line.tensorPow (d ^ 2),
      IsTensorPowerIso L (L.pullback ((𝟙 (Grp.mk G) ^ d).hom.hom)) (d ^ 2) f := by
  sorry

end AlgebraicGeometry.CubicalRigidifiedLine
