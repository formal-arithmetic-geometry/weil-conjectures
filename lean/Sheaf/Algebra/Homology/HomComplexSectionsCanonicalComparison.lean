/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Canonical comparison for sections of a sheaf Hom complex

Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(blueprint: lem-pur-hom-complex-sections-canonical-comparison)
-/

@[expose] public section

universe u v
open CategoryTheory Opposite
namespace CategoryTheory

/-- The canonical shifted section comparison, specified on cocycle representatives.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(blueprint: lem-pur-hom-complex-sections-canonical-comparison)

Proof: sections preserve the product cone specifying the sheaf Hom complex.
Its projections therefore identify degree-n sections with all degree-n cochains
between the restricted complexes. The differential projection formula identifies
the kernel with Mathlib's cocycles, giving e with the component formula below.
The same formula in degree n-1 identifies images of differentials with coboundaries.
Thus e descends to a bijection of the quotients. Compose that bijection with
Mathlib's equivalence from cohomology classes to shifted homotopy-category maps
to obtain a. On cocycles this composite is the quotient of equivHomShift.symm,
which proves the asserted representative formula. This construction works for
unbounded complexes since it uses products. Zero complexes give singleton
quotients; n=0 is the usual unshifted comparison. -/
theorem homComplex_sections_canonical_comparison
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (n : ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero R₀ U
    let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Q := HomotopyCategory.quotient (SheafOfModules.{max u v} (R₀.over U))
      (ComplexShape.up ℤ)
    let S := E.obj (homComplex (R := R) L I)
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    ∃ e : S.cycles n ≃ CochainComplex.HomComplex.Cocycle (res.obj L) (res.obj I) n,
      (∀ (z : S.cycles n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
        ((e z).val.v p q hpq).val.app W =
          (((π L I n p q hpq).val.app (op U)) (S.iCycles n z)).app W) ∧
      ∃ a : S.homology n ≃ (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I)⟦n⟧)),
        ∀ z : S.cycles n, a (S.homologyπ n z) =
          Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e z)) := by
  sorry

end CategoryTheory
