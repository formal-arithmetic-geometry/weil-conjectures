/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.MeromorphicDenominatorIdeal
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.RingTheory.Lasker
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk

/-! # Regular-section exact sequences give lower-dimensional differences

Source: Stacks Project, Divisors, Tag 02P2 (Lemma 31.25.5, label
`divisors-lemma-make-maps-regular-section`); Varieties, Tag 0BEM (blueprint:
lem-sc-hilbert-difference).
-/

@[expose] public section

universe u

open scoped AlgebraicGeometry.Scheme.Modules
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Regular meromorphic sections give coherent lower-dimensional cokernels and the
forward-difference identity for Euler characteristics.
Source: Stacks Project, Divisors, Tag 02P2; Varieties, Tag 0BEM
(blueprint: lem-sc-hilbert-difference).

Proof:
1. Trivialize L on affine opens and write s = a/b with a and b non-zero-divisors.
   The denominator ideal has sections I = {x | x(a/b) lies in A}. Since F has full
   support and no embedded associated points, a and b are also regular on its finite
   section module M. The affine calculation constructs the injective maps IM to M
   and IM to M tensor L. They agree on overlaps and glue
   [lem-sc-hilbert-affine-denominator-module,
   lem-sc-hilbert-denominator-ideal-nowhere-dense].
2. The denominator ideal is quasi-coherent and finitely generated on Noetherian affines,
   hence coherent [pqf-lem-coherent-ft-locnoeth]. Its product with F is the image of
   multiplication and has sections IM
   [lem-weil-pbc-ideal-times-quasi-coherent-affine-sections]. This submodule of F and
   the two cokernels are coherent by kernel/cokernel closure; F tensor L is coherent
   on the trivializing opens [lem-weil-pbc-coherent-kernel-cokernel-locnoeth].
3. The two cokernels are annihilated locally by I and s(I), respectively. Their supports
   lie in closed nowhere-dense subsets
   [lem-sc-hilbert-denominator-ideal-nowhere-dense]. Nonemptiness and finite dimension
   give strict dimension drop [lem-sc-hilbert-nowhere-dense-dimension-drop].
4. Tensor the two short exact sequences by L^n, which is exact for every integer n
   [lem-sc-ext-tensor-exact]. Apply Euler-characteristic additivity and cancel the common
   term IF tensor L^n [lem-pc-euler-additive], giving the displayed signs.

The first map uses the recorded ideal-module product. The second map is characterized
by factoring the tensor of the denominator map through the image of multiplication.
That image factor is an epimorphism, so the factorization determines the map uniquely.
The cokernels below are those of IF to F and IF to F tensor L, not those of I itself.
The denominator ideal I is the pullback of s along L to K_X(L), with projections to O_X
and L, written out explicitly. Integer twists L^n use `tensorPow` for nonnegative n and
powers of `dual` for negative n, inline as in lem-sc-snapper-numerical-polynomial.
-/
theorem hilbert_difference {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [Nonempty X]
    [IsLocallyNoetherian X] (d : ℕ)
    (hDim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (F : X.Modules)
    (hFcoh : AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace F)
    (hFsupport : ∀ x : X, ¬ Subsingleton ((presheaf F).stalk x))
    (hFnoEmbedded : ∀ (U : X.Opens) (_ : IsAffineOpen U)
      (p : Ideal (Γ(X, U))),
      p ∈ associatedPrimes (Γ(X, U)) (Γ(F, U)) →
        Minimal (fun q : Ideal (Γ(X, U)) =>
          q ∈ associatedPrimes (Γ(X, U)) (Γ(F, U))) p)
    (L : X.Modules) [L.IsInvertible]
    (s : unit X ⟶ meromorphicModule X L)
    (hs : Mono (meromorphicSectionMap X L s)) :
    ∃ jF : idealModuleProduct (pullback.fst s (toMeromorphicModule X L)) F ⟶ tensorObj F L,
      factorThruImage ((pullback.fst s (toMeromorphicModule X L)) ▷ F ≫ (λ_ F).hom) ≫ jF =
        (pullback.snd s (toMeromorphicModule X L)) ▷ F ≫ (β_ L F).hom ∧
      (Mono (idealModuleProductι (pullback.fst s (toMeromorphicModule X L)) F) ∧ Mono jF) ∧
      (AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace
          (cokernel (idealModuleProductι (pullback.fst s (toMeromorphicModule X L)) F)) ∧
        AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace (cokernel jF)) ∧
      topologicalKrullDim {x : X |
          ¬ Subsingleton ((presheaf (cokernel (idealModuleProductι
            (pullback.fst s (toMeromorphicModule X L)) F) : X.Modules)).stalk x)} <
        topologicalKrullDim X ∧
      topologicalKrullDim {x : X | ¬ Subsingleton ((presheaf (cokernel jF : X.Modules)).stalk x)} <
        topologicalKrullDim X ∧
      ∀ (n : ℤ),
        eulerChar k (tensorObj F (if 0 ≤ n + 1 then L.tensorPow (n + 1).toNat
            else L.dual.tensorPow (-(n + 1)).toNat)) -
            eulerChar k (tensorObj F (if 0 ≤ n then L.tensorPow n.toNat
            else L.dual.tensorPow (-n).toNat)) =
          eulerChar k (tensorObj (cokernel jF) (if 0 ≤ n then L.tensorPow n.toNat
            else L.dual.tensorPow (-n).toNat)) -
            eulerChar k (tensorObj
              (cokernel (idealModuleProductι (pullback.fst s (toMeromorphicModule X L)) F))
              (if 0 ≤ n then L.tensorPow n.toNat
            else L.dual.tensorPow (-n).toNat)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
