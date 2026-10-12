/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePointsElementary

/-!
# Elementary localization of already split fibre points

Source: Stacks Project, More on Morphisms, proof of Lemma 02LM, lines 12083--12089.
(blueprint: lem-weil-pbc-elementary-localize-split-points).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, More on Morphisms, proof of Lemma 02LM,
lines 12083--12089 and its omitted verification using Schemes, Lemma 01JT
(blueprint: lem-weil-pbc-elementary-localize-split-points).

Proof:
1. Regard the finite sigma family `y` as a list `Fin N` using a finite-type equivalence.
   Apply `exists_etale_local_finite_multiple_points_elementary` to `pullback.snd f φ`.
   Its local-finite-type instance comes from base change. The result is an elementary
   étale neighborhood `ψ : U' → U`, with `ψ u' = u`, and one finite open for each `y i j`,
   with a unique point over `u'` and an unchanged residue field over `y i j`.
2. Identify the iterated pullback with `pullback f (ψ ≫ φ)` by pullback pasting. Transport
   the opens, points, finiteness and unique-fibre-point assertions along this isomorphism.
   The first projection sends the chosen point to `y i j` and then to `x i`.
3. The residue-field square commutes and its base and point vertical maps are isomorphisms.
   Transport the given finite purely inseparable extension across these isomorphisms.
4. Distinct output points follow by projecting to the injective sigma family `y`.
   Any point of the final pullback above `u'` and `x i` projects to `y i j` by `hex`.
   Its lifts over `(y i j,u')` correspond to primes of
   `κ(y i j) ⊗[κ(u)] κ(u')`. Since the second factor map is an isomorphism, this is a
   field, hence has one prime. The chosen point is that sole lift, proving exhaustion.
For an empty sigma family the identity neighborhood and no opens work. These hypotheses
explicitly retain the purely inseparable residue extensions; uniqueness alone is insufficient. -/
theorem exists_elementary_localize_split_points
    {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (φ : U ⟶ S) (u : U) (n : ℕ) (x : Fin n → X) (m : Fin n → ℕ)
    (y : (i : Fin n) → Fin (m i) → ↥(pullback f φ))
    (hyx : ∀ i j, pullback.fst f φ (y i j) = x i)
    (hy : ∀ i j, ∃ (h : pullback.snd f φ (y i j) = u),
      letI := ((U.residueFieldCongr h.symm).hom ≫
        (pullback.snd f φ).residueFieldMap (y i j)).hom.toAlgebra
      Module.Finite (U.residueField u) ((pullback f φ).residueField (y i j)) ∧
        IsPurelyInseparable (U.residueField u) ((pullback f φ).residueField (y i j)))
    (hisolated : ∀ i j, IsOpen ({(pullback.snd f φ).asFiber (y i j)} :
      Set ((pullback.snd f φ).fiber ((pullback.snd f φ) (y i j)))))
    (hinj : Function.Injective (fun a : (i : Fin n) × Fin (m i) ↦ y a.1 a.2))
    (hex : ∀ (i : Fin n) (w : ↥(pullback f φ)),
      pullback.snd f φ w = u → pullback.fst f φ w = x i →
        ∃ j : Fin (m i), w = y i j) :
    ∃ (U' : Scheme.{u}) (ψ : U' ⟶ U) (u' : U'), Etale ψ ∧ ψ u' = u ∧
      ∃ (V : (i : Fin n) → Fin (m i) → (pullback f (ψ ≫ φ)).Opens)
        (v : (i : Fin n) → (j : Fin (m i)) → (V i j).toScheme),
        (∀ (i : Fin n) (j : Fin (m i)),
          IsFinite ((V i j).ι ≫ pullback.snd f (ψ ≫ φ)) ∧
          ∃ (hv : ((V i j).ι ≫ pullback.snd f (ψ ≫ φ)) (v i j) = u'),
            (∀ w : (V i j).toScheme,
              ((V i j).ι ≫ pullback.snd f (ψ ≫ φ)) w = u' → w = v i j) ∧
            (letI := ((U'.residueFieldCongr hv.symm).hom ≫
              ((V i j).ι ≫ pullback.snd f (ψ ≫ φ)).residueFieldMap (v i j)).hom.toAlgebra
             Module.Finite (U'.residueField u') ((V i j).toScheme.residueField (v i j)) ∧
               IsPurelyInseparable (U'.residueField u')
                 ((V i j).toScheme.residueField (v i j))) ∧
            ((V i j).ι ≫ pullback.fst f (ψ ≫ φ)) (v i j) = x i) ∧
        Function.Injective
          (fun a : (i : Fin n) × Fin (m i) ↦ (V a.1 a.2).ι (v a.1 a.2)) ∧
        (∀ (i : Fin n) (w : ↥(pullback f (ψ ≫ φ))),
          pullback.snd f (ψ ≫ φ) w = u' → pullback.fst f (ψ ≫ φ) w = x i →
            ∃ j : Fin (m i), w = (V i j).ι (v i j)) := by
  sorry

end AlgebraicGeometry
