module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeFunctionNorm
import Sheaf.AlgebraicGeometry.FiniteTrivializeInvertibleUpstairs
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen

/-! # Existence of ample invertible modules under finite locally free surjections

Source: Stacks Project, Divisors, Tag 0BD4, proposition-push-down-ample, case (1),
and Tag 0BD0, lemma-norm-ample
(blueprint: lem-sfb-finite-locally-free-ample-existence).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A surjective finite locally free morphism descends the existence of an absolutely
ample invertible module. The given module needs no descent datum, and the resulting
module is not required to pull back to it. The degree need not be constant.

Source: Stacks Project, Divisors, Tag 0BD4, proposition-push-down-ample, case (1),
using Tags 0BD0, 0BD2, 0BCY and 0BCZ
(blueprint: lem-sfb-finite-locally-free-ample-existence).

Proof:
1. Choose an ample invertible module `M` on `Y`. Its ampleness makes `Y` quasi-compact
   by `def-weil-pbc-ample-invertible-module`. Pull an open cover of `X` back to `Y`,
   choose a finite subcover, and use `def-weil-surjective-morphism` to conclude that
   `X` is quasi-compact. The morphism is finite by `def-pc-finite-locally-free`.
2. By `lem-weil-pbc-finite-locally-free-degree-locally-constant`, decompose `X` into
   open and closed degree pieces `X_d`. Surjectivity makes `X_0` empty: a degree-zero
   fibre has zero coordinate algebra, hence empty spectrum. For each positive degree
   use `lem-sfb-finite-locally-free-function-norm` on that piece. For every open `V`
   and regular function `b` upstairs, glue these norms on the disjoint open cover
   `V ∩ X_d`, using the structure-sheaf axiom from `def-pc-scheme`. Multiplicativity,
   preservation of one, compatibility with restriction and residue-field vanishing
   are checked on the pieces. This gives one norm family without a constant degree
   or a global scalar-power identity. On empty `X`, use the unique sections.
3. Use `lem-sfb-finite-trivialize-invertible-upstairs` to choose an open cover `V_i`
   of `X` and frames `e_i` of `M` on their inverse images. Apply
   `lem-sfb-norm-frame-tensor-section-gluing` to the family from step 2. Fix the
   resulting invertible module `N` and frames `q_i` before choosing any power or
   section. For every `n ≥ 1` and section `s` of `M.tensorPow n` this produces a
   section `t` of `N.tensorPow n`, locally `ν(b_i) q_i^n` when `s = b_i e_i^n`.
4. Apply `lem-sfb-finite-function-norm-nonvanishing` to the local coefficients.
   Finiteness and all its norm hypotheses hold by steps 1 and 2. Frames identify
   nonvanishing with nonvanishing of their coefficients, so `X_t` consists exactly
   of points whose entire fibre is contained in `Y_s`.
5. Given `x : X`, choose an affine open neighbourhood `V` by `def-pc-scheme`.
   Its fibre `E` is finite by `lem-weil-pbc-finite-closed-map-finite-fibres`.
   By `lem-sc-ample-finite-principal-affine`, there are `n > 0` and a section `s`
   of `M.tensorPow n` with `E ⊆ Y_s ⊆ f⁻¹ V`. Its norm section `t` from step 3
   satisfies `x ∈ X_t` by step 4. Surjectivity gives a point over each `z ∈ X_t`,
   which lies in `Y_s ⊆ f⁻¹ V`; hence `X_t ⊆ V`.
6. By `lem-sc-affine-cap-section-open`, `V ∩ X_t` is affine. Since `X_t ⊆ V`,
   this is `X_t` itself. Every point therefore has an affine nonvanishing
   neighbourhood given by a positive-power global section of the single module `N`.
   Together with quasi-compactness from step 1, this is precisely
   `def-weil-pbc-ample-invertible-module`. On empty `X` the point condition is vacuous.
-/
theorem exists_isAmple_of_finiteLocallyFree_surjective
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Surjective f] [f.IsFiniteLocallyFree]
    (hY : ∃ M : Y.Modules, ∃ hM : M.IsInvertible, @IsAmple Y M hM) :
    ∃ N : X.Modules, ∃ hN : N.IsInvertible, @IsAmple X N hN := by
  sorry

end AlgebraicGeometry.Scheme.Modules
