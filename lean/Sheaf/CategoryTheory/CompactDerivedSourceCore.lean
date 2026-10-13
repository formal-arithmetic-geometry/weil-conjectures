/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Sheaf.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Equivalence

/-! The compact derived source component of the derived presentation. -/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- A compactly generated triangulated model for the derived category of modules.
Source: Stacks Project, Tags 0F5V and 0F5X.

(blueprint: new-stage3-compact-derived-source-core)

Proof in words: construct the small-Hom derived category of modules by the
Grothendieck construction.  The rank-one free module in degree zero represents
cohomology, so its shifted Hom groups are the corresponding cohomology groups;
these commute with the displayed coproducts, proving compactness.  The same
calculation shows that vanishing of all shifted Hom groups detects the zero
object.  The coproduct construction is compatible with the triangulated
structure and shifts.  Choose the resulting small-Hom model, lift its object
universe to the displayed universe, and transport its zero object,
preadditive structure, shifts, distinguished triangles, coproducts, and the
compact-generation property along the chosen equivalence.  The equivalence
therefore commutes with integer shifts and its functor is triangulated.
-/
theorem compact_derived_source_core
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    {S : Type w} [rS : Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)] :
    ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B),
      letI := zB
      letI := sB
      letI := pB
      ∃ aB : ∀ n : ℤ, (shiftFunctor B n).Additive,
      letI := aB
      ∃ tB : Pretriangulated B,
      letI := tB
      ∃ (iB : IsTriangulated B) (sumsB : HasCoproducts.{max w vH} B),
      letI := iB
      letI := sumsB
      IsCompactlyGeneratedTriangulated.{max w vH} B ∧
      ∃ (e : B ≌ DerivedCategory (ModuleCat.{max w vH} S))
        (se : e.functor.CommShift ℤ),
      letI := se
      e.functor.IsTriangulated := by
  sorry

end CategoryTheory
