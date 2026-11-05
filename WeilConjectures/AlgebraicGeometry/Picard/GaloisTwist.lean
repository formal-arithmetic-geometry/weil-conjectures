/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.SpecAlgebraicClosure

/-!
# The Galois action on the degree-`d` Picard functor of a geometric curve

Let `C₀` be a proper curve over a field `k`, `k̄` an algebraic closure and `C = C₀ ×_k k̄`. An
automorphism `σ` of `k̄` over `k` acts on `Pic^d_{C/k̄}`: for a scheme `T` over `k̄` let `T^σ` be
`T` with structure morphism composed with `Spec σ`; then `T` and `T^σ` are the same `k`-scheme,
and the canonical identification of `Pic^d_{C/k̄}` with the restriction of `Pic^d_{C₀/k}` to
`k̄`-schemes (`AlgebraicGeometry.picardFunctorDegreeIsoOfIsPullback`) gives a map
`σ_C^* : Pic^d_{C/k̄}(T) ⟶ Pic^d_{C/k̄}(T^σ)` (`AlgebraicGeometry.picardFunctorDegreeGaloisMap`).

If `J₀` represents `Pic^d_{C₀/k}`, then `J = J₀ ×_k k̄` represents `Pic^d_{C/k̄}` by base
change, and an endomorphism `s` of `J` over `Spec σ` and over `J₀`, such as `𝟙 × Spec σ`, induces
`σ_C^*` on the represented functor (`AlgebraicGeometry.homEquiv_galoisTwistHom`). By Yoneda, the
endomorphism of `J` over `Spec σ` inducing `σ_C^*` is unique
(`AlgebraicGeometry.eq_of_homEquiv_galoisTwistHom`, blueprint `lem-pc-representable-unique`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

variable {C₀ C : Scheme.{u}} [C₀.Over (Spec (.of k))] [C.Over (Spec (.of (AlgebraicClosure k)))]
  [IsProper (C₀ ↘ Spec (.of k))] [LocallyOfFinitePresentation (C₀ ↘ Spec (.of k))]
  (q : C ⟶ C₀) (h : IsPullback q (C ↘ Spec (.of (AlgebraicClosure k))) (C₀ ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) (d : ℤ)

variable {q h d} {J₀ : Over (Spec (.of k))}
  {r : (picardFunctorDegree (C₀ ↘ Spec (.of k)) d).obj.RepresentableBy J₀}
  {rK : (picardFunctorDegree (C ↘ Spec (.of (AlgebraicClosure k))) d).obj.RepresentableBy
    (Over.mk (pullback.snd J₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))}

/-! ### The geometric fiber of a curve -/

namespace Scheme.Hom

variable {C₀ : Scheme.{u}} (p : C₀ ⟶ Spec (.of k)) [IsProper p] [LocallyOfFinitePresentation p]
  (d : ℤ)

variable {p d} {J₀ : Over (Spec (.of k))}
  {r : (picardFunctorDegree p d).obj.RepresentableBy J₀}
  {rK : (picardFunctorDegree p.geometricFiberToAlgebraicClosure d).obj.RepresentableBy
    (Over.mk J₀.hom.geometricFiberToAlgebraicClosure)}

end Scheme.Hom

end AlgebraicGeometry
