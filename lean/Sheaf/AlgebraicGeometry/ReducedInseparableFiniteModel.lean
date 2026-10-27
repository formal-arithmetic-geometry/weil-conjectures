/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.NormalScheme

import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Finite normal models over reduced purely inseparable base changes

Source: Stacks Project, Varieties, Tag 0C3N, finite-model part of the affine reduced
field-change comparison; supplied finite model variant
(blueprint: lem-trf-reduced-inseparable-finite-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite normal models after a finite purely inseparable extension.
Source: Stacks Project, Varieties, Tag 0C3N, affine reduced comparison, specialized to a
supplied finite model whose field base change is normal
(blueprint: lem-trf-reduced-inseparable-finite-model).

Here `X = W.nilradical.subscheme`, `Y = N ×_k K`, `Z = (W ×_k K)_red`.
The structure map of `N` is `(f ≫ W.nilradical.subschemeι) ≫ σ`.
`IsNormalScheme Y` includes both integrality and normality. The two equations for
`p` characterize its composite with the reduction immersion by both pullback projections;
the uniqueness clause concerns all such factorizations. Likewise the equations for `e`
and `eU` mean that the isomorphisms commute with the maps to `W ×_k K`.
The open `U ×_k K` is the inverse image of `U` under `X ×_k K → X`.

Proof (the seven steps of the DAG node):
1. By lem-pc-homeo-pure-insep, the projections `Y → N` and `W_K → W` are
   homeomorphisms. By lem-weil-pbc-reduction-universal-homeomorphism, both reduction
   immersions are homeomorphisms and their sources are reduced. The assumed local
   domains make `Y` reduced (def-pc-reduced-scheme). Its space, and that of `Z`, is
   nonempty and irreducible; hence both are integral (def-pc-integral-scheme).
   The local-ring assumption also gives normality of `Y`.
2. Apply lem-weil-pbc-reduced-source-factors-through-closed-subscheme to `Y → W_K`
   and to `Z → W`, giving `p` and `q`. Closed immersions are monomorphisms
   (def-weil-closed-immersion), giving uniqueness. The equation for `q` expresses it
   as a composite of the preceding homeomorphisms and the inverse of `X → W`.
3. The base change `a : X_K → W_K` is a closed immersion by
   lem-weil-pbc-closed-immersion-base-change and a homeomorphism by
   lem-weil-pbc-reduction-universal-homeomorphism. Write `T = (X_K)_red` with
   immersion `j`. Factor `Z → W_K` through `a`, then through `j`, giving `c : Z → T`.
   Factor `a j` through `Z`, giving `d : T → Z`. The reduced-source factorization
   lemma and cancellation of the closed immersions show `dc = 1` and `cd = 1`.
   Thus `d` is the asserted isomorphism `e` over `W_K`.
4. The map `h = f_K : Y → X_K` is finite and surjective by
   lem-trf-finite-radicial-basechange and lem-weil-pbc-surjective-base-change,
   using def-pc-base-change. Put `p̃ = cp`. Cancellation of `a` gives `jp̃ = h`,
   and `dp̃ = p` follows from `dc = 1`.
5. The square with maps `p̃`, `h`, `j`, and the identity of `Y` is cartesian:
   for `hu = jv`, cancellation of `j` gives `p̃u = v`, and `u` is the unique lift.
   Thus `p̃` is finite by lem-trf-finite-radicial-basechange. It is surjective because
   `h` is surjective and `j` is bijective. Transport across `d` gives both properties of `p`.
6. Base change of the given isomorphism over `U` identifies `h⁻¹(U_K)` with `U_K`.
   This is an open of reduced `Y`, so `U_K` is reduced (def-pc-reduced-scheme).
   Under `e`, the inverse image of `U_K` is `V = q⁻¹(U)`, by cancellation of `X → W`.
   On each affine open of `U_K`, its reduction is the quotient by the zero nilradical
   (def-weil-pbc-scheme-reduction). Hence `eU : U_K ≅ V` over `W_K`, and `p` restricts
   to the base-changed isomorphism followed by the inverse of this identification.
7. The homeomorphism `q` makes `V` dense. Density of `U` and nonemptiness of integral `X`
   imply that `U` is nonempty. Surjectivity of `f` makes `f⁻¹(U)` nonempty; it is open
   in irreducible `N`, hence dense. The homeomorphism `Y → N` carries `p⁻¹(V)` to
   `f⁻¹(U)`, proving its density.
-/
theorem reduced_inseparable_finite_model
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [IsPurelyInseparable k K]
    (W N : Scheme.{u}) (σ : W ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType σ] [QuasiCompact σ]
    [IsIntegral W.nilradical.subscheme] [IsIntegral N]
    (f : N ⟶ W.nilradical.subscheme) [IsFinite f] [Surjective f]
    (U : W.nilradical.subscheme.Opens)
    (hU : Dense (U : Set W.nilradical.subscheme))
    (hfU : IsIso (f ∣_ U))
    (hnormal : ∀ y : ↥(pullback ((f ≫ W.nilradical.subschemeι) ≫ σ) (Spec.map (CommRingCat.ofHom
              (algebraMap k K)))),
      IsDomain ((pullback ((f ≫ W.nilradical.subschemeι) ≫ σ) (Spec.map (CommRingCat.ofHom
              (algebraMap k K)))).presheaf.stalk y) ∧
      IsIntegrallyClosed ((pullback ((f ≫ W.nilradical.subschemeι) ≫ σ) (Spec.map
              (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk y)) :
    IsNormalScheme (pullback ((f ≫ W.nilradical.subschemeι) ≫ σ) (Spec.map (CommRingCat.ofHom
              (algebraMap k K)))) ∧
    IsIntegral (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subscheme ∧
    ∃ p : (pullback ((f ≫ W.nilradical.subschemeι) ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))) ⟶ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subscheme,
      p ≫ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι ≫
              pullback.fst σ (Spec.map (CommRingCat.ofHom (algebraMap k K))) = pullback.fst ((f ≫
              W.nilradical.subschemeι) ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ f ≫
              W.nilradical.subschemeι ∧
      p ≫ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι ≫
              pullback.snd σ (Spec.map (CommRingCat.ofHom (algebraMap k K))) = pullback.snd ((f ≫
              W.nilradical.subschemeι) ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      (∀ p' : (pullback ((f ≫ W.nilradical.subschemeι) ≫ σ) (Spec.map (CommRingCat.ofHom
              (algebraMap k K)))) ⟶ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subscheme,
        p' ≫ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι ≫
              pullback.fst σ (Spec.map (CommRingCat.ofHom (algebraMap k K))) = pullback.fst ((f ≫
              W.nilradical.subschemeι) ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ f ≫
              W.nilradical.subschemeι →
        p' ≫ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι ≫
              pullback.snd σ (Spec.map (CommRingCat.ofHom (algebraMap k K))) = pullback.snd ((f ≫
              W.nilradical.subschemeι) ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) → p' =
              p) ∧
      IsFinite p ∧ Surjective p ∧
      ∃ q : (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subscheme ⟶
              W.nilradical.subscheme,
        q ≫ W.nilradical.subschemeι = (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subschemeι ≫ pullback.fst σ (Spec.map (CommRingCat.ofHom
              (algebraMap k K))) ∧
        IsHomeomorph q.base ∧
        Dense ((q ⁻¹ᵁ U) : Set (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subscheme) ∧
        Dense ((p ⁻¹ᵁ (q ⁻¹ᵁ U)) : Set ↥(pullback ((f ≫ W.nilradical.subschemeι) ≫ σ) (Spec.map
              (CommRingCat.ofHom (algebraMap k K))))) ∧
        IsIso (p ∣_ (q ⁻¹ᵁ U)) ∧
        ∃ e : (pullback (W.nilradical.subschemeι ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subscheme ≅ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subscheme,
          e.hom ≫ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subschemeι ≫ pullback.fst σ (Spec.map (CommRingCat.ofHom
              (algebraMap k K))) = (pullback (W.nilradical.subschemeι ≫ σ) (Spec.map
              (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι ≫ pullback.fst
              (W.nilradical.subschemeι ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
              W.nilradical.subschemeι ∧
          e.hom ≫ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subschemeι ≫ pullback.snd σ (Spec.map (CommRingCat.ofHom
              (algebraMap k K))) = (pullback (W.nilradical.subschemeι ≫ σ) (Spec.map
              (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι ≫ pullback.snd
              (W.nilradical.subschemeι ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
          IsReduced (pullback.fst (W.nilradical.subschemeι ≫ σ) (Spec.map (CommRingCat.ofHom
              (algebraMap k K))) ⁻¹ᵁ U).toScheme ∧
          ∃ eU : (pullback.fst (W.nilradical.subschemeι ≫ σ) (Spec.map (CommRingCat.ofHom
              (algebraMap k K))) ⁻¹ᵁ U).toScheme ≅ (q ⁻¹ᵁ U).toScheme,
            eU.hom ≫ (q ⁻¹ᵁ U).ι ≫ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subschemeι ≫ pullback.fst σ (Spec.map (CommRingCat.ofHom
              (algebraMap k K))) = (pullback.fst (W.nilradical.subschemeι ≫ σ) (Spec.map
              (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ U).ι ≫ pullback.fst
              (W.nilradical.subschemeι ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
              W.nilradical.subschemeι ∧
            eU.hom ≫ (q ⁻¹ᵁ U).ι ≫ (pullback σ (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))).nilradical.subschemeι ≫ pullback.snd σ (Spec.map (CommRingCat.ofHom
              (algebraMap k K))) = (pullback.fst (W.nilradical.subschemeι ≫ σ) (Spec.map
              (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ U).ι ≫ pullback.snd
              (W.nilradical.subschemeι ≫ σ) (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  sorry

end AlgebraicGeometry
