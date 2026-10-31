/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.RingTheory.ProEtale.IntegralLocal

/-!
# Normalization of a strictly henselian local domain

Source: Stacks Project, more-algebra.tex, Tag 06DM (lemma-geometrically-unibranch),
proof of (2) implies (1), specialized to a strictly henselian domain; also used in
Tag 0DQ1 (lemma-invariance-number-branches-smooth), proof of (1).
(blueprint: lem-dl-a1-smooth-local-branch-normalization-local)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsStrictlyHenselianLocalRing

/-- The normalization of a strictly henselian local domain in its fraction field is a
local normal domain, and its canonical residue-field extension is purely inseparable.
Source: Stacks Project, more-algebra.tex, Tag 06DM, proof of (2) implies (1), with
`A` strictly henselian and its unique minimal prime equal to zero; Tag 0DQ1, proof of (1).
(blueprint: lem-dl-a1-smooth-local-branch-normalization-local)

Proof:
1. The integral closure is an integral domain integral over A. The existing theorem
   `IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain` therefore makes it local.
   Integral-closure normality gives integral closedness in the same fraction field,
   hence integral closedness as a domain.
2. By lem-weil-pbc-integral-maximal-contracts-maximal, the maximal ideal contracts
   to a maximal ideal of A, which must be its unique maximal ideal. Thus the map is local.
3. Apply `Algebra.IsAlgebraic.residueField_of_isIntegral` to the canonical residue map.
   This reduces a monic integral equation for a representative of each residue class.
4. The residue field of A is separably closed. Apply
   lem-dl-a1-sepclosed-algebraic-purely-inseparable to the extension in Step 3.

The existential local structures let Lean form the residue field and its canonical
map. The algebra used for pure inseparability is explicitly the one induced by that
map, rather than an independently chosen field extension. -/
theorem normalization_isLocalRing_and_isPurelyInseparable
    (A : Type u) [CommRing A] [IsDomain A] [IsStrictlyHenselianLocalRing A] :
    ∃ (_ : IsLocalRing (integralClosure A (FractionRing A))),
      (IsDomain (integralClosure A (FractionRing A)) ∧
        IsIntegrallyClosed (integralClosure A (FractionRing A))) ∧
      ∃ (_ : IsLocalHom (algebraMap A (integralClosure A (FractionRing A)))),
        @IsPurelyInseparable (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (integralClosure A (FractionRing A))) _ _
          (IsLocalRing.ResidueField.map
            (algebraMap A (integralClosure A (FractionRing A)))).toAlgebra := by
  let C := integralClosure A (FractionRing A)
  let K := FractionRing A
  let f : A →+* C := algebraMap A C
  have hlocal : IsLocalRing C := by
    exact IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain (R := A)
  let : IsLocalRing C := hlocal
  have hmap : IsLocalHom f := by
    apply ((IsLocalRing.local_hom_TFAE f).out 4 0).mp
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (IsLocalRing.maximalIdeal C))
  have hclosed : IsIntegrallyClosed C := by
    apply (isIntegrallyClosed_iff_isIntegrallyClosedIn K).2
    infer_instance
  let k := IsLocalRing.ResidueField A
  let l := IsLocalRing.ResidueField C
  let rf : k →+* l := IsLocalRing.ResidueField.map f
  have halg : Algebra.IsAlgebraic k l :=
    Algebra.IsAlgebraic.residueField_of_isIntegral (R := A) (S := C)
  have hAlg : (inferInstance : Algebra k l) = rf.toAlgebra := by
    apply Algebra.algebra_ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) x
    rfl
  have hpure : @IsPurelyInseparable k l _ _ rf.toAlgebra := by
    rw [← hAlg]
    infer_instance
  exact ⟨hlocal, ⟨inferInstance, hclosed⟩, ⟨hmap, hpure⟩⟩

end IsStrictlyHenselianLocalRing
