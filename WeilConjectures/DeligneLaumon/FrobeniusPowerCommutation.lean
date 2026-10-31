/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Transport

/-! # Commutation of iterated Weil returns

Source: geometric orbit argument of `sk-i-dl-general-real`, step 2 of
`lem-zl-geometric-power-orbit-stalk`.
(blueprint: lem-zl-frobenius-power-return-commutation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Endofunctor
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf
open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Compare geometric Frobenius power pullback with repeated single pullback.
Source: recursive definition of the iterated Weil return.
(blueprint: lem-zl-frobenius-power-return-commutation). -/
noncomputable def frobeniusPowPullbackIterateIso : (n : ℕ) →
    frobeniusPowPullback k₀ l X n ≅ (WeilSheaf.frobeniusPullback k₀ l X).iterate n
  | 0 => adicLowerStarCongr l (by rw [pow_zero]; rfl) ≪≫ adicLowerStarId l _
  | n + 1 =>
    adicLowerStarCongr l (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]) ≪≫
      (adicLowerStarComp l _ _).symm ≪≫
      Functor.isoWhiskerRight (frobeniusPowPullbackIterateIso n) _

private theorem frobeniusPowIso_eq_iterate (K : ProEtaleWeilSheaf k₀ l X) (n : ℕ) :
    K.frobeniusPowIso n =
      (frobeniusPowPullbackIterateIso n).app K.carrier ≪≫ K.strIterate n := by
  induction n with
  | zero => apply Iso.ext; simp [frobeniusPowIso, frobeniusPowPullbackIterateIso]
  | succ n ih =>
    rw [frobeniusPowIso, frobeniusPowPullbackIterateIso, ih]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.map_comp,
      IsoAlgebra.strIterate_succ, Functor.mapIso_hom, Category.assoc]

/-- Both successive power pullbacks identify with the sum of the iterates.
Source: composition of iterated pullbacks.
(blueprint: lem-zl-frobenius-power-return-commutation). -/
noncomputable def frobeniusPowerCompositionIso (m n : ℕ) :
    frobeniusPowPullback k₀ l X m ⋙ frobeniusPowPullback k₀ l X n ≅
      (WeilSheaf.frobeniusPullback k₀ l X).iterate (m + n) :=
  Functor.isoWhiskerRight (frobeniusPowPullbackIterateIso m) _ ≪≫
    Functor.isoWhiskerLeft _ (frobeniusPowPullbackIterateIso n) ≪≫
      eqToIso ((WeilSheaf.frobeniusPullback k₀ l X).iterate_add m n).symm

private theorem frobeniusPowerCompositionIso_return
    (K : ProEtaleWeilSheaf k₀ l X) (m n : ℕ) :
    (frobeniusPowerCompositionIso m n).hom.app K.carrier ≫
        (K.strIterate (m + n)).hom =
      (frobeniusPowPullback k₀ l X n).map (K.frobeniusPowIso m).hom ≫
        (K.frobeniusPowIso n).hom := by
  rw [frobeniusPowIso_eq_iterate, frobeniusPowIso_eq_iterate,
    IsoAlgebra.strIterate_add_hom]
  simp only [frobeniusPowerCompositionIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app, Iso.app_hom, Functor.map_comp,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← NatTrans.naturality_assoc]


/-- The commutor of two geometric power pullbacks, using their ordered iterates.
Source: the two orders of iterating one Frobenius.
(blueprint: lem-zl-frobenius-power-return-commutation). -/
noncomputable def frobeniusPowerCommIso (j r : ℕ) :
    frobeniusPowPullback k₀ l X j ⋙ frobeniusPowPullback k₀ l X r ≅
      frobeniusPowPullback k₀ l X r ⋙ frobeniusPowPullback k₀ l X j :=
  frobeniusPowerCompositionIso j r ≪≫
    eqToIso (congrArg (WeilSheaf.frobeniusPullback k₀ l X).iterate (Nat.add_comm j r)) ≪≫
      (frobeniusPowerCompositionIso r j).symm

private theorem strIterate_congr (K : ProEtaleWeilSheaf k₀ l X)
    (m n : ℕ) (h : m = n) :
    eqToHom (Functor.congr_obj
        (congrArg (WeilSheaf.frobeniusPullback k₀ l X).iterate h) K.carrier) ≫
      (K.strIterate n).hom = (K.strIterate m).hom := by
  subst n
  simp

/-- Two iterated returns of the same Weil object commute with the canonical
pullback comparisons. Source: geometric orbit argument, cancellation step.
(blueprint: lem-zl-frobenius-power-return-commutation).

Proof: Identify each geometric power pullback recursively with the corresponding
iterate of the single Frobenius functor. The return is then `strIterate`. Its
addition identity identifies both ordered composites with the return of degree
j+r=r+j. Undo the two comparisons. This includes zero powers, whose return is
the identity comparison. -/
theorem frobeniusPowIso_comm (K : ProEtaleWeilSheaf k₀ l X) (j r : ℕ) :
    (frobeniusPowerCommIso j r).hom.app K.carrier ≫
        (frobeniusPowPullback k₀ l X j).map (K.frobeniusPowIso r).hom ≫
          (K.frobeniusPowIso j).hom =
      (frobeniusPowPullback k₀ l X r).map (K.frobeniusPowIso j).hom ≫
        (K.frobeniusPowIso r).hom := by
  rw [← frobeniusPowerCompositionIso_return, ← frobeniusPowerCompositionIso_return]
  simp only [frobeniusPowerCommIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, eqToIso.hom, eqToHom_app]
  rw [strIterate_congr K (j + r) (r + j) (Nat.add_comm j r)]


end AlgebraicGeometry.ProEtaleWeilSheaf
