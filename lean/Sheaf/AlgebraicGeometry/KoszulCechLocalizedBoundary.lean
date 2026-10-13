/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.AlgebraicGeometry.KoszulCechLocalizedEvaluation

/-! # The horizontal localized Koszul boundary calculation

Source: Stacks Project, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-localized-boundary).
-/

@[expose] public section

universe uK

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type uK) [CommRing A] (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- The precomposition term alone becomes the alternating Cech deletion sum.
Source: Stacks Project, Tag 08D0, the two displayed differential calculations,
and Tag 08D1, the correction of totalization signs.
(blueprint: lem-sc-koszul-cech-localized-boundary)
Proof: put p=card(J)-1. The hypothesis card(J)>1 makes every erased subset
nonempty and places both tail degrees in the supported range. Transport the tail
differential to the negative Koszul contraction. On the
increasing wedge it is minus the sum over j in J of (-1)^position times
f(j)^(e+1) times the increasing wedge for J.erase j. Here position is the
number of elements of J smaller than j. Apply z and restriction and use their
A-linearity to distribute the sum. The product identity
prod(J)=f(j)*prod(J.erase j) and the invertibility of these products on D(prod(J))
identify division of f(j)^(e+1) times the restricted numerator by prod(J)^(e+1)
with restriction of division by prod(J.erase j)^(e+1). Naturality composes the
two restrictions. The equality of vertical degrees is principalCech_erase_degree;
its eqToHom is exactly the transport in the right side. The negative boundary
and the Hom sign (n+1).negOnePow leave n.negOnePow. Finally the difference
S(p,n+1)+n-S(p-1,n) is even, where S(p,n)=p*(n-p)+p*(p-1)/2.
This matches the displayed signs term by term. No coefficient differential is
involved. The singleton case is proved directly in the original theorem and is excluded here.
The empty cover has no J; zero or nilpotent products give empty opens
and zero section modules, so the argument also applies there. -/
theorem koszulCechLocalized_boundary (e : ℕ)
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
    (Int.negOnePow
      ((J.val.card - 1 : ℕ) * ((n + 1) + 1 - (J.val.card : ℤ)) +
        ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
      koszulCechScalarDivision A (F.X ((n + 1) + 1 - (J.val.card : ℤ)))
        (∏ j ∈ J.val, f j) (e + 1)
        ((modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
          (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
          (((n + 1).negOnePow •
            ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).d
              (1 - (J.val.card : ℤ)) (2 - (J.val.card : ℤ)) ≫
            z.v (2 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)) (by ring))
              (B J))) =
      ∑ j : J.val, if h : (J.val.erase j.val).Nonempty then
        (-1 : A) ^ ((J.val.filter (fun i ↦ i < j.val)).card) •
          (modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
            (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op
            ((affineOpenSections A (principalCechIntersection r f (J.val.erase j.val))).map
              (eqToHom (congrArg F.X
                (principalCech_erase_degree r J.val j.val j.property n)))
              (koszulCechLocalizedDegreeMap A r f F e n B z ⟨J.val.erase j.val, h⟩))
      else 0 := by sorry

end AlgebraicGeometry
