module

public import Sheaf.FieldTheory.StableNonarchimedeanField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The completed algebraic closure of a stable field

Source: Bosch--Güntzer--Remmert, Non-Archimedean Analysis, Proposition 3.4.1/3,
Corollary 2.4.3/10, and their application in Section 5.3.4, pp. 218--219
(blueprint: lem-trf-completed-algebraic-closure-cartesian).
-/

@[expose] public section

set_option autoImplicit false

universe u v

/-- The completed algebraic closure of a complete stable nonarchimedean field is
algebraically closed, complete, and cartesian over the base field.
Source: Bosch--Güntzer--Remmert, Non-Archimedean Analysis, Proposition 3.4.1/3 and
Corollary 2.4.3/10, as used in Section 5.3.4, pp. 218--219
(blueprint: lem-trf-completed-algebraic-closure-cartesian).

The chosen algebraic closure is `L`. Its compatible multiplicative norm is exactly the
spectral norm by `NormedAlgebra.norm_eq_spectralNorm K`. Such a structure exists by
`spectralNorm.normedField` and `spectralNorm.normedAlgebra`; hence the normed-algebra
interface adds no restriction to the choice of algebraic closure. `Completion L` carries
Mathlib's canonical field operations, norm, and scalar action. The maximum is taken in
`ℝ≥0`, so its value for an empty basis is zero.

Proof plan:
1. The spectral norm extends that of K by `lem-trf-spectral-norm-algebraic-extension`.
Apply `lem-sfb-normed-field-completion` to get a complete normed field, an isometric
inclusion of L, and density. Passing the strong triangle inequality to limits gives
ultrametricity of the completion. The composite inclusion of K is isometric.
2. For a monic polynomial f of positive degree n over the completion, choose a root a
in an algebraic closure of the completion equipped with its spectral norm. Put
M = max (norm a) 1. For r > 0 choose epsilon = (r/M)^n/(n+1). By
`lem-sfb-monic-dense-approximation`, approximate f by a monic polynomial g over L of
the same degree with all coefficient errors less than epsilon.
3. By `lem-weil-alg-closed-linear-factorization`, g factors into linear factors over L.
Apply `lem-sfb-roots-coefficient-proximity` to get a root b of g with norm (a-b) < r.
The factorization forces b to equal one of those roots in L. Thus a lies in the closure
of the completed field inside its algebraic closure, in every characteristic.
4. By `lem-sfb-finite-dimensional-subspace-closed`, that completed field, viewed as a
one-dimensional subspace over itself, is closed. Hence a belongs to it. Normalize a
nonconstant polynomial by its leading coefficient to conclude algebraic closedness.
5. Every finite-dimensional subspace U of L is contained in a finite extension E/K:
apply `lem-weil-pbc-algebraic-generators-finite-extension` to a finite basis of U.
Its restricted norm equals its spectral norm because minimal polynomials are unchanged
by embedding E in L. Stability gives an orthogonal basis of E, and
`lem-trf-cartesian-subspace` gives one for U. The zero subspace has its empty basis.
6. For a positive-dimensional subspace V of the completion, apply
`lem-trf-finite-ultrametric-almost-orthogonal-basis` with r = 1/2 to get a basis e_i
and alpha > 0 with norm (sum a_i e_i) >= alpha * max (norm a_i). By density choose
w_i in L with norm (w_i-e_i) < alpha for every i.
7. For a nonzero coefficient family, set A = max (norm a_i), x = sum a_i e_i,
y = sum a_i w_i. The ultrametric inequality gives norm (y-x) < alpha*A <= norm x.
The strong triangle inequalities in both directions force norm y = norm x. The same
holds for the zero coefficient family. Thus e_i mapped to w_i defines a linear isometry
from V onto their span U in L, with injectivity from definiteness of the norm.
8. Apply step 5 to U and transfer its orthogonal basis back along that isometry.
For dimension zero use the empty basis; both the finite sum and its maximum are zero.
No spherical completeness, discrete valuation, or characteristic assumption is used. -/
theorem completedAlgebraicClosure_cartesian
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (hK : IsStableNonarchimedeanField K)
    (L : Type v) [NormedField L] [NormedAlgebra K L] [IsAlgClosure K L] :
    IsAlgClosed (UniformSpace.Completion L) ∧
      CompleteSpace (UniformSpace.Completion L) ∧
      IsUltrametricDist (UniformSpace.Completion L) ∧
      Isometry (algebraMap K (UniformSpace.Completion L)) ∧
      ∀ (V : Submodule K (UniformSpace.Completion L)) [FiniteDimensional K V],
        ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
          ∀ a : Fin (Module.finrank K V) → K,
            ‖∑ i, a i • b i‖₊ = Finset.univ.sup (fun i ↦ ‖a i‖₊ * ‖b i‖₊) := by
  sorry
