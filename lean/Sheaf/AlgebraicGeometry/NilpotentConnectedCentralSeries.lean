/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q56
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Connected central series of nilpotent algebraic groups

Source: Milne, Algebraic Groups (2017), Proposition 6.38 and Corollary 6.39,
pp.133--134, with the commutator formulation of Remark 6.35
(blueprint: lem-sfb-nilpotent-connected-central-series).

A term is represented by a group scheme with a closed embedding into the fixed
ambient group. Inclusions are factorizations of those embeddings, and commutator
containment is tested on every commutative algebra, including nonreduced algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth connected affine nilpotent group over a perfect field admits a finite
central series of smooth connected closed subgroup schemes. The supplied series
may have nonsmooth or disconnected terms. For a trivial ambient group the output
can have length zero.
Source: Milne, Proposition 6.38 and Corollary 6.39, pp.133--134, Remark 6.35
(blueprint: lem-sfb-nilpotent-connected-central-series).

Proof:
1. Starting with C₀ = G, recursively set Cⱼ₊₁ = [G,Cⱼ] using
   lem-sfb-smooth-connected-relative-commutator. This supplies a smooth connected
   normal closed subgroup contained in Cⱼ and containing every relative commutator
   on every algebra's points. Iterate through the length s of the supplied series.
2. Prove Cⱼ is contained in Hⱼ by induction. At zero both are G. If Cⱼ is contained
   in Hⱼ, the supplied commutator condition puts every [g,c] in Hⱼ₊₁(R).
   The minimality clause of lem-sfb-smooth-connected-relative-commutator, applied
   to the arbitrary closed subgroup Hⱼ₊₁, gives Cⱼ₊₁ contained in Hⱼ₊₁. This
   needs no smoothness, connectedness or normality of Hⱼ₊₁.
3. Thus Cₛ is contained in Hₛ = 1, so Cₛ = 1. Take t = s. When G is trivial,
   instead take t = 0 and the single term G; this also covers s = 0. -/
theorem nilpotent_connected_central_series
    (k : Type u) [Field k]
    (hperfect : CharZero k ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧ ∀ x : k, ∃ y : k, y ^ p = x)
    (G : Grp (Over (Spec (.of k))))
    (haff : IsAffine G.X.left)
    (hft : LocallyOfFiniteType G.X.hom) (hqc : QuasiCompact G.X.hom)
    (hsm : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (hseries : ∃ (s : ℕ) (H : Fin (s + 1) → Grp (Over (Spec (.of k))))
      (i : ∀ j : Fin (s + 1), H j ⟶ G),
      (∀ j : Fin (s + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
        IsAffine (H j).X.left ∧ LocallyOfFiniteType (H j).X.hom ∧
        QuasiCompact (H j).X.hom) ∧
      IsIso (i 0) ∧ Nonempty (H (Fin.last s) ≅ Grp.trivial _) ∧
      (∀ j : Fin s, ∃ l : H j.succ ⟶ H j.castSucc, l ≫ i j.castSucc = i j.succ) ∧
      ∀ (j : Fin s) (R : Type u) [CommRing R] [Algebra k R]
        (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G.X)
        (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶
          (H j.castSucc).X),
        ∃ z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ (H j.succ).X,
          z ≫ (i j.succ).hom.hom =
            g * (h ≫ (i j.castSucc).hom.hom) * g⁻¹ *
              (h ≫ (i j.castSucc).hom.hom)⁻¹) :
    ∃ (t : ℕ) (C : Fin (t + 1) → Grp (Over (Spec (.of k))))
      (i : ∀ j : Fin (t + 1), C j ⟶ G),
      (∀ j : Fin (t + 1), IsClosedSubgroupScheme (i j).hom.hom ∧
        IsAffine (C j).X.left ∧ LocallyOfFiniteType (C j).X.hom ∧
        QuasiCompact (C j).X.hom ∧ Smooth (C j).X.hom ∧ ConnectedSpace (C j).X.left) ∧
      IsIso (i 0) ∧ Nonempty (C (Fin.last t) ≅ Grp.trivial _) ∧
      (Nonempty (G ≅ Grp.trivial _) → t = 0) ∧
      (∀ j : Fin t, ∃ l : C j.succ ⟶ C j.castSucc, l ≫ i j.castSucc = i j.succ) ∧
      ∀ (j : Fin t) (R : Type u) [CommRing R] [Algebra k R]
        (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G.X)
        (c : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶
          (C j.castSucc).X),
        ∃ z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ (C j.succ).X,
          z ≫ (i j.succ).hom.hom =
            g * (c ≫ (i j.castSucc).hom.hom) * g⁻¹ *
              (c ≫ (i j.castSucc).hom.hom)⁻¹ := by
  sorry

end AlgebraicGeometry
