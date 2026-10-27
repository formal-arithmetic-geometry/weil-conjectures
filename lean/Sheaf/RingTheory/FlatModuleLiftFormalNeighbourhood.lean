/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Flat.Localization
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange
import WeilConjectures.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso

/-!
# Flat module lifts and formal neighbourhoods

Source: Stacks Project, Tag 0DZ2, lemma-lift-equivalence-module, square-zero part
of the proof, with the finite-module hypothesis used in that proof.
(blueprint: lem-sfb-flat-module-lift-formal-neighbourhood)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace Algebra

/-- Existence of a coefficient-flat module lift, including its reduction isomorphism.
Scalar extension along `q` is the ordinary tensor product `P ⊗[P'] L`.
Source: Stacks Project, Tags 0DZ1 and 0DZ2, module liftability.
(blueprint: lem-sfb-flat-module-lift-formal-neighbourhood) -/
def HasCoefficientFlatModuleLift
    {R P' P : Type u} [CommRing R] [CommRing P'] [CommRing P]
    (c : R →+* P') (q : P' →+* P) (M : ModuleCat.{max u v} P) : Prop :=
  ∃ L : ModuleCat.{max u v} P',
    Module.Flat R ((ModuleCat.restrictScalars c).obj L) ∧
      Nonempty ((ModuleCat.extendScalars q).obj L ≅ M)

/-- The map on special fibres induced by the given algebra map `S' → T'`.
It sends `a ⊗ s` to `a ⊗ image(s)`; no comparison map is chosen.
Source: Stacks Project, Tag 0DZ2, the bottom horizontal map in the scalar-extension square.
(blueprint: lem-sfb-flat-module-lift-formal-neighbourhood) -/
def formalNeighbourhoodSpecialFibreMap
    (A' A S' T' : Type u) [CommRing A'] [CommRing A] [CommRing S'] [CommRing T']
    [Algebra A' A] [Algebra A' S'] [Algebra S' T'] [Algebra A' T']
    [IsScalarTower A' S' T'] : A ⊗[A'] S' →+* A ⊗[A'] T' :=
  (Algebra.TensorProduct.map (AlgHom.id A' A) (IsScalarTower.toAlgHom A' S' T')).toRingHom

/-- Flat liftability of a finite module is detected by a flat formal neighbourhood.
The special fibres are written with `A` on the left. Localization uses the image
of `g` under the canonical map to the special fibre. A reduction along `P' → P`
is canonically the coefficient reduction along `A' → A`, with its `P`-module structure.

Source: Stacks Project, Tag 0DZ2, lemma-lift-equivalence-module, square-zero part
of the proof; finiteness of `M` is explicitly used for Ext base change there.
(blueprint: lem-sfb-flat-module-lift-formal-neighbourhood)

Proof plan:
1. Put J = IS', J_T = IT', and let K be the image of K'. Tensor associativity
   gives T = S ⊗[S'] T', flatness of A → S → T, and flatness of the localized maps,
   using lem-weil-pbc-localization-flat. Reducing the given quotient isomorphism
   gives S/K ≅ T/KT. Noetherianity makes K finitely generated.
2. Apply lem-sfb-flat-module-derived-lift-criterion and
   lem-sfb-square-zero-complex-obstruction to S', T', and each S'_g. Flatness over A
   identifies the obstruction coefficient with B = M ⊗[A] I in degree zero.
   The obstruction w in Hom_D(S)(M[0], B[2]) vanishes exactly when the required
   coefficient-flat module lift with its reduction isomorphism exists.
3. By lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion, M[0] is
   pseudo-coherent. Use lem-trf-pseudocoherent-rhom-flat-base-change and
   lem-trf-flat-projective-hom-models to identify obstruction groups after flat
   extension with tensor products. The flat base-change clause of
   lem-sfb-square-zero-complex-obstruction sends w to w ⊗ 1 and to w/1 locally.
4. The assumed local lifts give w/1 = 0 for every g in K'. For generators g_i of K',
   choose n_i ≥ 1 with g_i^n_i w = 0. Every monomial of degree
   1 + sum_i (n_i - 1) kills w, hence a power of K kills w. When K' = 0, Kw = 0.
5. Apply lem-weil-pbc-torsion-submodule-flat-base-change-iso: the map on K-power
   torsion is injective. Consequently w = 0 iff w ⊗ 1 = 0. The obstruction criterion
   translates these vanishings into the two liftability assertions.
-/
theorem flatModuleLift_formalNeighbourhood_iff
    (A' A S' T' : Type u) [CommRing A'] [CommRing A] [CommRing S'] [CommRing T']
    [IsNoetherianRing A'] [IsNoetherianRing A]
    [IsNoetherianRing S'] [IsNoetherianRing T']
    [Algebra A' A] [Algebra A' S'] [Algebra S' T'] [Algebra A' T']
    [IsScalarTower A' S' T']
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsquare : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (hflatS : (algebraMap A' S').Flat) (hflatT : (algebraMap S' T').Flat)
    (K' : Ideal S')
    (hquot : Function.Bijective
      (Ideal.quotientMap (K'.map (algebraMap S' T')) (algebraMap S' T')
        Ideal.le_comap_map))
    (M : ModuleCat.{max u v} (A ⊗[A'] S'))
    [Module.Finite (A ⊗[A'] S') M]
    (hflatM : Module.Flat A ((ModuleCat.restrictScalars
      (algebraMap A (A ⊗[A'] S'))).obj M))
    (hlocal : ∀ g : S', g ∈ K' →
      HasCoefficientFlatModuleLift
        ((algebraMap S' (Localization.Away g)).comp (algebraMap A' S'))
        (Localization.awayMap
          (Algebra.TensorProduct.includeRight : S' →ₐ[A'] A ⊗[A'] S').toRingHom g)
        ((ModuleCat.extendScalars (algebraMap (A ⊗[A'] S')
          (Localization.Away
            ((Algebra.TensorProduct.includeRight : S' →ₐ[A'] A ⊗[A'] S') g)))).obj M)) :
    HasCoefficientFlatModuleLift (algebraMap A' S')
      (Algebra.TensorProduct.includeRight : S' →ₐ[A'] A ⊗[A'] S').toRingHom M ↔
    HasCoefficientFlatModuleLift (algebraMap A' T')
      (Algebra.TensorProduct.includeRight : T' →ₐ[A'] A ⊗[A'] T').toRingHom
      ((ModuleCat.extendScalars (formalNeighbourhoodSpecialFibreMap A' A S' T')).obj M) := by
  sorry

end Algebra
