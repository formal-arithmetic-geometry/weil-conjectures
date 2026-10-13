/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Algebra.Homology.ModuleHomComplex
public import Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal
public import Sheaf.AlgebraicGeometry.KoszulOpenSystem

/-! # Increasing-wedge Koszul boundary evaluation

Source: Stacks Project, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-boundary-evaluation).
-/

@[expose] public section

universe uK

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type uK) [CommRing A] (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Evaluation of the negative tail boundary on an increasing wedge, before localization.
Source: Stacks Project, Tags 08D0 and 08D1, the first differential calculation.
(blueprint: lem-sc-koszul-cech-boundary-evaluation)
Proof: since card(J)>1, both tail degrees and every erased subset are supported.
Use extendXIso to transport the differential to minus koszulBoundary. Include the
exterior powers into the exterior algebra and apply the contraction recursion
contractLeft_ι_mul to the increasing product of basis generators. This gives one
summand per deleted generator, with coefficient (-1)^position*f(j)^(e+1).
The increasing enumeration of the erased subset is the original enumeration with
that position removed, so position equals the number of indices smaller than j.
Apply the linear component of z to this finite sum. Its source degree is
1-card(J.erase j)=2-card(J), by card_erase_add_one. The corresponding target
degree equality is principalCech_erase_degree; transporting through z gives the
coefficient eqToHom displayed here. Linearity pulls out the negative and scalars.
There is no division, restriction, Hom differential sign or totalization sign
in this identity. The smallest supported subset has two indices, where the
formula is minus (f(i)^(e+1)*e_j - f(j)^(e+1)*e_i). -/
theorem koszulCechBoundary_evaluation (e : ℕ)
    (B : ∀ J : {J : Finset (Fin r) // J.Nonempty},
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X
        (1 - (J.val.card : ℤ)))
    (hB : ∀ J, B J =
      ((koszulOpenTail A r f e).extendXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f (J.val.card - 1) =
          1 - (J.val.card : ℤ) by
          simp only [ComplexShape.embeddingDownNat_f]
          have h : 0 < J.val.card := Finset.card_pos.mpr J.property
          omega)).inv
        (exteriorPower.ιMulti A (J.val.card - 1 + 1)
          (fun i ↦ Finsupp.single (J.val.orderEmbOfFin
            (show J.val.card = J.val.card - 1 + 1 by
              have h : 0 < J.val.card := Finset.card_pos.mpr J.property
              omega) i) (1 : A)))) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n)
    (J : {J : Finset (Fin r) // J.Nonempty}) (hJ : 1 < J.val.card) :
    ((((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).d
      (1 - (J.val.card : ℤ)) (2 - (J.val.card : ℤ)) ≫
      z.v (2 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)) (by ring)) (B J)) =
    -(∑ j : J.val, if h : (J.val.erase j.val).Nonempty then
      ((-1 : A) ^ ((J.val.filter (fun i ↦ i < j.val)).card) * f j.val ^ (e + 1)) •
        (affineOpenSections A ⊤).map
          (eqToHom (congrArg F.X
            (principalCech_erase_degree r J.val j.val j.property n)))
          ((z.v (1 - ((J.val.erase j.val).card : ℤ))
            (n + 1 - ((J.val.erase j.val).card : ℤ)) (by ring))
              (B ⟨J.val.erase j.val, h⟩))
      else 0) := by sorry

end AlgebraicGeometry
