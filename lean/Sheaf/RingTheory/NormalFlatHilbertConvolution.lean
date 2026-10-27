module

public import Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.FlatGradedFibreRegularLift
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.RingTheory.RegularSequenceGradedPolynomial

/-!
# Hilbert convolution along a normally flat regular quotient

Source: Hironaka, Certain numerical characters of singularities (1970), section 2,
p.153 and the paragraph after Example (4.2), p.157; the filtered-algebra proof
in the DAG (blueprint: lem-trf-normal-flat-hilbert-convolution).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- The degree-j vector subspace of the canonical normal-cone residue fibre.
It is spanned by the initial classes of elements of I^j. Since homogeneous
inclusion into the direct sum is split, tensoring it is still split; this
subspace is canonically (I^j/I^(j+1)) tensor_(R/I) k. The existing fibre uses
the symmetric tensor order k tensor_(R/I) gr_I R.
Source: Hironaka (1970), section 2, p.153, normal-cone fibre construction
(blueprint: lem-trf-normal-flat-hilbert-convolution). -/
noncomputable def normalConeFibrePiece {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (j : ℕ) :
    Submodule (IsLocalRing.ResidueField R) (normalConeFibre I hI) :=
  Submodule.span (IsLocalRing.ResidueField R) (Set.range (normalConeFibreClass I hI j))

/-- The normal-cone fibre pieces are finite dimensional, and the Hilbert-Samuel
lengths are their Hilbert function convolved with that of the regular centre.
Source: Hironaka, Certain numerical characters of singularities (1970), section 2,
p.153 and the paragraph after Example (4.2), p.157; the DAG's algebraic synthesis
(blueprint: lem-trf-normal-flat-hilbert-convolution).

Proof: (1) Apply lem-trf-flat-graded-fibre-regular-lift to obtain finite free
A=R/I-modules G_j. Their ranks equal the dimensions h_j of their residue fibres.
Lift a regular system of s parameters of A to y_i in m, and put J=(y_i).
By lem-weil-pbc-regular-local-generators-regular-sequence these parameters are
regular on A and hence on each finite free G_j. Also m=I+J.
(2) Every I^a is finite by lem-weil-pbc-noetherian-submodule-finite. Apply
lem-trf-adic-degree-zero-regular-strict-powers to its shifted I-adic filtration:
J^q I^a intersect I^(a+p) = J^q I^(a+p), including zero modules.
(3) Expand m^N=(I+J)^N. For z in I^j intersect m^N, eliminate terms I^a J^(N-a)
with a<j successively, using step (2) with p=1 to absorb each into the next.
Modulo I^(j+1) the remaining image is precisely n^(N-j) G_j, for N>=j.
(4) Filter R/m^N by L_j=(I^j+m^N)/m^N, from L_0=R/m^N to L_N=0.
The kernel of I^j to L_j/L_(j+1) is I^(j+1)+(I^j intersect m^N).
Thus its factor is G_j/n^(N-j)G_j, isomorphic to (A/n^(N-j))^h_j.
(5) By lem-pur-regular-sequence-graded-polynomial the n-adic graded ring of A
is k[Y_1,...,Y_s]. Its monomials of degree below t form the factors of A/n^t.
Length additivity (lem-weil-pbc-length-additive-short-exact) and stars and bars
therefore give length_R(A/n^t)=choose(t-1+s,s), also for s=0.
(6) Apply the same length-additivity theorem along L_j for N=n+1. The factors
of step (4) give the displayed sum. If I=0 only degree zero contributes;
if I=m then s=0 and all binomial factors are 1; at n=0, h_0=1.
No coefficient field, reducedness, excellence or completeness is used. -/
theorem normal_flat_hilbert_convolution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ I)] (s : ℕ)
    (hs : ringKrullDim (R ⧸ I) = (s : WithBot ℕ∞))
    [Module.Flat (R ⧸ I) (associatedGraded I)] :
    (∀ j : ℕ, Module.Finite (IsLocalRing.ResidueField R) (normalConeFibrePiece I hI j)) ∧
    ∀ n : ℕ, Module.length R (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) =
      ∑ j ∈ Finset.range (n + 1),
        (Module.finrank (IsLocalRing.ResidueField R) (normalConeFibrePiece I hI j) : ℕ∞) *
          (Nat.choose (n - j + s) s : ℕ∞) := by
  sorry

end Ideal
