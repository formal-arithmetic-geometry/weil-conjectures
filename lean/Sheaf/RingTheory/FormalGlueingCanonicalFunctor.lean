/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.RingTheory.FormalGlueingData
import Sheaf.Paper.FormalGlueingCanonicalMaps

/-!
# Construction of the canonical formal glueing functor

Source: Stacks Project, More on Algebra, Remark 05EL.
(blueprint: lem-weil-pbc-formal-glueing-canonical-functor).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

/-- The prescribed objects and maps form the canonical functor, without any flatness
or quotient hypothesis.
Source: Stacks Project, More on Algebra, Remark 05EL; steps 1–2 of the proof of
[ prop-weil-pbc-formal-glueing-equivalence ].
(blueprint: lem-weil-pbc-formal-glueing-canonical-functor).
Proof: equip the scalar extension and the localized chart modules with comparison
and swap linear equivalences, using their bijectivity from the canonical-map lemma.
The restricted module of each chart equals the original localized R-module: their
additive groups agree, and algebraMap_smul identifies their scalar actions. Transport
along these equalities to type the structural maps. The square sends every double
fraction of a pure tensor to the same swapped fraction of that tensor on both paths;
tensor induction and additivity give equality. Each cocycle path reverses the order
of the same three denominators. For a linear map use its scalar extension and its
localizations; the comparison and swap fraction formulas prove both morphism equations.
Localization and base change preserve identity maps and composition, so the prescribed
maps satisfy the functor laws componentwise. Equality of Hom structures follows from
equality of prime and chart components, since the remaining fields are proofs. These
arguments include an empty chart family, zero generators and zero localizations. -/
theorem exists_canonical_functor {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R) :
    ∃ Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f,
      (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))) ∧
      (∀ (M N : ModuleCat.{max u v w} R) (h : M ⟶ N),
        HEq (Can.map h).prime (extendMap φ h.hom) ∧
        ∀ i : Fin t, HEq ((Can.map h).chart i) (localMap (f i) h.hom)) := by
  sorry

end FormalGlueing
