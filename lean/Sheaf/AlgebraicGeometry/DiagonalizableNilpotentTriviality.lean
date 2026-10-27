module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.AlgebraicGeometry.Thickening
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyAffineSections
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Nilpotent rigidity of trivial homomorphisms from diagonalizable groups

Source: Conrad, Reductive group schemes, Corollary B.2.7, printed p.287
(blueprint: lem-sfb-diagonalizable-nilpotent-triviality).

Reduction is the scheme base-change functor along Spec(A/J) → Spec(A). Applying it to
an identity-valued map gives the identity-valued map on the base-changed group schemes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A homomorphism from Spec A[M] which is trivial modulo a nilpotent ideal is trivial.
There are no smoothness, flatness, separatedness or presentation conditions on G.
Source: Conrad, Reductive group schemes, Corollary B.2.7, printed p.287, split case
(blueprint: lem-sfb-diagonalizable-nilpotent-triviality).

Proof:
1. First suppose J² = 0. Coefficientwise reduction A[M] → (A/J)[M] has kernel J[M],
   whose square is zero (def-sbc-first-order-thickening). The same holds for M × M.
   The tensor pushout identifies A[M] ⊗[A] A[M] with A[M × M]
   (lem-weil-pbc-algebra-tensor-pushout-universal-property). Multiplication and the two
   projections act on basis vectors by m ↦ (m,m), m ↦ (m,0), and m ↦ (0,m).
2. Apply lem-sfb-space-square-zero-lift-linearization to H₀ ⊂ H and the identity-valued
   map. The difference f♯ − (e_G p)♯ corresponds bijectively to a homomorphism from the
   pulled-back cotangent module into J[M]. It sends the identity-valued map to zero.
   By lem-sfb-group-space-square-zero-difference-additive, this very difference map
   sends products of points reducing to the identity to sums. The cotangent module
   pulled back along e_G over Spec(A/J) is quasi-coherent: use
   def-sc-relative-differential-sheaf, lem-weil-pbc-module-pullback-quasi-coherent,
   lem-sfb-scheme-etale-relative-differentials-comparison and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence. No finiteness is needed.
3. Write P for its global sections over Spec(A/J). By
   lem-weil-pbc-affine-tilde-gamma-adjunction and lem-pc-flat-affine-base-change-sections,
   the difference is a linear map (A/J)[M] ⊗[A/J] P → J[M], equivalently a map
   d : P → J[M] (def-weil-pbc-module-tensor-product). The same description holds on
   H × H with coefficient module J[M × M]. This does not commute Hom with tensor.
4. The homomorphism identity for f, additivity of the actual difference coordinate
   (lem-sfb-group-space-square-zero-difference-additive), and its naturality under
   composition (lem-sfb-space-square-zero-lift-linearization) give, for every q ∈ P,
   Δ(d(q)) = L(d(q)) + R(d(q)). These are the three basis maps of step 1. The tensor
   and sections identifications commute with them, as checked on pure tensors.
5. Write d(q) = ∑ i_m e_m. Comparing the (m,m) coefficient for m ≠ 0 gives i_m = 0.
   The (0,0) coefficient gives i_0 = i_0 + i_0, hence i_0 = 0 by cancellation.
   Thus d = 0, the difference coordinate vanishes, and its injectivity gives f = e_G p.
   This works with torsion, in characteristic 2, and over the zero ring.
6. In general use def-pc-base-change and induct on 1 ≤ r ≤ N over A/J^r.
   The initial case is the hypothesis. In A/J^(r+1), the ideal J^r/J^(r+1) has square
   zero because 2r ≥ r+1. Apply steps 1--5 to deduce triviality at r+1 from that at r.
   Finally J^N = 0 identifies the last base change with the original homomorphism.
   For N = 1 the initial case already gives the conclusion. -/
theorem diagonalizable_nilpotent_triviality (A : Type u) [CommRing A]
    (J : Ideal A) (N : ℕ) (hN : 1 ≤ N) (hJ : J ^ N = ⊥)
    (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (G : Over (Spec (.of A))) [GrpObj G]
    (f : (ringDiagonalizableGroup A M).X ⟶ G) [IsMonHom f]
    (hf : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map
        (toUnit (ringDiagonalizableGroup A M).X ≫ η[G])) :
    f = toUnit (ringDiagonalizableGroup A M).X ≫ η[G] := by
  sorry

end AlgebraicGeometry
