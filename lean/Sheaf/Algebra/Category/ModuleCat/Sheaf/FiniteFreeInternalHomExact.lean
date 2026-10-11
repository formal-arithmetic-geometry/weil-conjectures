/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Exactness of internal Hom from finite free sheaves

Source: literature/stacks-project/cohomology.tex, Tag 0GM8, finite locally free Hom
calculation used in case (2) (blueprint: lem-sc-finite-free-internal-hom-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  {R : Sheaf J CommRingCat.{u}}

/-- Internal Hom from a finite free sheaf preserves a short exact sequence, with the
canonical finite-sum identifications and the induced coordinatewise sequence maps.
Source: literature/stacks-project/cohomology.tex, Tag 0GM8, finite locally free calculation
(blueprint: lem-sc-finite-free-internal-hom-exact).

Proof:
1. On every localized site, precompose with the chosen isomorphism `hE.inv` and evaluate
   on the `r` basis sections. This identifies each internal Hom with the corresponding
   finite direct sum, compatibly with restriction (`def-pur-sheaf-hom`). The coordinate
   equation below specifies exactly these identifications, for `N = ![A, B, C]`.
2. Postcomposition by the sequence maps becomes their coordinatewise finite direct sums.
   Finite direct sums preserve short exact sequences in the abelian category of sheaves
   of modules (`def-weil-sheaf-of-modules-category`), also when `r = 0`.
3. The two displayed commutative squares transport that exactness to the internal-Hom
   sequence and provide the claimed canonical identifications.
-/
theorem finiteFreeInternalHomExact
    (r : ℕ)
    (E : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hE : E ≅ SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (ULift.{u} (Fin r)))
    (S : ShortComplex (SheafOfModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hS : S.ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (𝟙 E) S.f ≫
        SheafOfModules.homObjMap (𝟙 E) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (𝟙 E) S.f)
        (SheafOfModules.homObjMap (𝟙 E) S.g) hz).ShortExact ∧
      let N : Fin 3 → SheafOfModules
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
        ![S.X₁, S.X₂, S.X₃]
      ∃ i : ∀ k : Fin 3, SheafOfModules.homObj E (N k) ≅
          ∐ (fun _ : ULift.{u} (Fin r) ↦ N k),
        (∀ (k : Fin 3) (U : C) (φ : (SheafOfModules.homObj E (N k)).val.obj
            (Opposite.op U)) (j : ULift.{u} (Fin r)),
          ((Limits.Sigma.desc (fun l : ULift.{u} (Fin r) ↦
            if l = j then 𝟙 (N k) else 0)).val.app (Opposite.op U))
              (((i k).hom.val.app (Opposite.op U)) φ) =
            (φ.app (Opposite.op (Over.mk (𝟙 U))))
              ((hE.inv.val.app (Opposite.op U))
                (((SheafOfModules.ιFree
                  (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) j).val.app
                    (Opposite.op U)) (1 : R.obj.obj (Opposite.op U))))) ∧
        SheafOfModules.homObjMap (𝟙 E) S.f ≫ (i 1).hom =
          (i 0).hom ≫ Limits.Sigma.map (fun _ ↦ S.f) ∧
        SheafOfModules.homObjMap (𝟙 E) S.g ≫ (i 2).hom =
          (i 1).hom ≫ Limits.Sigma.map (fun _ ↦ S.g) := by sorry

end SheafOfModules
