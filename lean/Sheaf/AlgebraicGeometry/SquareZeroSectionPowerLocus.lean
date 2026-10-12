/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology
import Sheaf.Paper.BoundaryDerivationSquareZero

/-! # Lifting the nonvanishing open of a section across a square-zero immersion

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, square-zero case,
from the tensor exact sequence through the lifting of a power of a section.
(blueprint: lem-sc-square-zero-section-power-locus).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- An affine nonvanishing open downstairs is the inverse image of the nonvanishing
locus of a section of a positive multiple of the original tensor degree upstairs.
This asserts neither ampleness nor affineness of the open upstairs.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1)
and the next paragraph, ending with the lift of a power of the section.
(blueprint: lem-sc-square-zero-section-power-locus).

Proof:
1. Put N = j^*L and M_d = I tensor L^d. Since L^d is invertible, tensoring
   0 -> I -> O_X -> j_*O_Z -> 0 is exact. The closed-immersion unit quotient
   identifies its quotient with j_*j^*(L^d). Pullback commutes with tensor powers,
   so this is j_*(N^d). The ideal and all M_d are quasi-coherent, and I M_d = 0.
2. The annihilated-module lemma identifies M_d with j_*G_d for G_d = j^*M_d.
   The affine-morphism cohomology edge identifies H^1(X,M_d) with H^1(Z,G_d).
   Let xi be the connecting class of s in degree n.
3. Form the commutative graded algebras sum_d L^d and sum_d j_*(N^d).
   Their kernel sum_d M_d has square zero, since products of two ideal factors
   lie in I^2. The square-zero boundary derivation, projected to each degree,
   gives partial(s^k) = k s^(k-1) xi. To see the degree identification, include
   the degree-d exact sequence in the summed sequence and project back; naturality
   of the connecting map identifies the two boundaries. The formula follows by
   induction from Leibniz: partial(s^(k+1)) = s partial(s^k) + s^k partial(s).
4. Apply the affine-open killing lemma on Z with line bundle N^n, section s,
   module G_n, and cohomological degree one. Z is quasi-compact and quasi-separated
   by its Noetherian hypotheses. It supplies e with s^e xi = 0. Naturality of the
   edge comparison for multiplication by s^e identifies this with multiplication
   on H^1(X,M_n), after the tensor-power identifications. Thus the boundary of
   s^(e+1) vanishes. Exactness lifts it to t in Gamma(X,L^(n*(e+1))). Set k = e+1.
5. On fibres over z the pullback of t is s^k. The residue-value tensor formula
   for invertible modules and the injective residue-field map show that t is
   nonzero at j(z) exactly when s is nonzero at z: in a one-dimensional vector
   space a positive tensor power is zero exactly when its factor is zero.
   Consequently j^{-1}(X_t) = U. This concerns only the nonvanishing set;
   openness and affineness of X_t are separate steps. -/
theorem exists_section_power_locus_of_square_zero
    {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian Z] [CompactSpace Z]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (s : (((tensorPullback j).obj L).tensorPow n).val.presheaf.obj
      (Opposite.op ⊤)) (U : Z.Opens)
    (hU : (U : Set Z) = nonvanishingLocus (((tensorPullback j).obj L).tensorPow n) s)
    (hAffine : IsAffineOpen U) :
    ∃ k : ℕ, 0 < k ∧
      ∃ t : (L.tensorPow (n * k)).val.presheaf.obj (Opposite.op ⊤),
        ∀ z : Z, j z ∈ nonvanishingLocus (L.tensorPow (n * k)) t ↔ z ∈ U := by sorry

end AlgebraicGeometry.Scheme.Modules
