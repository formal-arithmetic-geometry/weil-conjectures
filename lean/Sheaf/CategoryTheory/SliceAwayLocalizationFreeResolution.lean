/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.SliceAwayLocalization
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The free telescope resolution of a localized ring sheaf

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af, displayed resolution
(blueprint: lem-weil-pbc-localization-free-resolution).
-/

@[expose] public section

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The localization on a slice has the stated two-term free resolution. The formulas on
coordinate inclusions determine the maps uniquely and imply the finite-support formulas
on local representatives. Rings are commutative, as in the Stacks convention.

Source: Stacks Project, Tag 0997, lemma-hom-from-Af, displayed resolution.
(blueprint: lem-weil-pbc-localization-free-resolution).

Proof plan:
1. On the slice (def-pur-localized-ringed-site), form the presheaves P of finite-support
sequences and L of fractions, with the restriction maps on coefficients. Define D by
identity minus the f-weighted forward shift and Q by summing x_n/f^n.
2. Coordinate induction makes D injective. Telescoping gives QD = 0, and a single
coordinate gives every fraction, so Q is surjective sectionwise.
3. For x in ker Q with support bounded by N, put a = sum_{i=0}^N f^(N-i)x_i.
The localization relation gives f^k a = 0 for some k, without cancelling f.
4. With M = N+k, the partial sums s_j = sum_{i=0}^j f^(j-i)x_i satisfy s_M = 0.
Set y_j = s_j for j < M and zero afterwards. Then Dy = x, also when M = 0.
5. Apply lem-weil-pbc-ringed-site-module-sheafification-exact to this exact sequence;
its Mathlib instances are imported through Presheaf.Sheafification.
6. The adjunction def-weil-presheaf-modules-sheafification identifies P's sheafification
with the countable coproduct of unit modules. The coordinate formulas descend to the
sheafification and give precisely d and q. -/
theorem sliceAwayLocalization_free_resolution {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (O : Sheaf J CommRingCat.{u}) (U : C)
    (f : O.obj.obj (op U))
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ∃ L : SliceAwayLocalization O U f,
    ∃ d : (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        O).over
        U)) (ULift.{u} ℕ)) ⟶
        (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
            O).over U))
            (ULift.{u} ℕ)),
    ∃ q : (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        O).over
        U)) (ULift.{u} ℕ)) ⟶
        (PresheafOfModules.sheafification (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            O).over U).obj)).obj L.val,
      (∃ h : d ≫ q = 0, (ShortComplex.mk
        (C := ringedSiteModules
          (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).over U))
        d q h).ShortExact) ∧
      (∀ (V : (Over U)ᵒᵖ) (n : ℕ) (a : O.obj.obj (op V.unop.left)),
        d.val.app V ((SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat
            RingCat)).obj O).over U)) (ULift.up n)).val.app V a) =
          (SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              O).over
              U)) (ULift.up n)).val.app V a -
          (SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              O).over
              U)) (ULift.up (n + 1))).val.app V
            (O.obj.map V.unop.hom.op f * a)) ∧
      (∀ (V : (Over U)ᵒᵖ) (n : ℕ) (a : O.obj.obj (op V.unop.left)),
        q.val.app V ((SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat
            RingCat)).obj O).over U)) (ULift.up n)).val.app V a) =
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (((sheafCompose J (forget₂ CommRingCat
              RingCat)).obj O).over U).obj)).unit.app
            L.val).app V ((L.equiv V).symm
              (algebraMap _ _ a * IsLocalization.Away.invSelf
                (O.obj.map V.unop.hom.op f) ^ n))) := by
  sorry

end CategoryTheory
