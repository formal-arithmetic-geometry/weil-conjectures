/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

import Sheaf.CategoryTheory.Triangulated.DerivedFunctorDerivedLimit
import Sheaf.AlgebraicGeometry.TruncationDerivedLimit
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison

/-! # Affine-basis lower truncation tower inputs
Source: Stacks Project, Tags 0BKT, 0D64, 071B and 08D4. -/

@[expose] public section
universe u wC wA
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Derived abelian sections reconstruct the lower tail from its canonical lower
truncations. This is only the reconstruction step, with no homology conclusion.
Source: Stacks Project, Tag 0D64 (lemma-is-limit-dimension), Tag 071B
(lemma-K-injective) and Tag 0BKT (lemma-cohomology-over-U-trivial).
(blueprint: lem-sc-affine-basis-lower-tail-sections-reconstruction).

Proof: Restrict to V. Exact restriction identifies the homology of E with the
restriction of H^r(F) for r < a and with zero for r >= a. Affine opens inside V
form a basis of V. On each such open, the module-to-abelian cohomology comparison
transfers hhomology to zero positive derived module sections. Thus Tag 0D64 applies
on V with local bound zero and reconstructs E from its lower truncations. Restriction
preserves K-injectives by the exact extension-by-zero adjoint, so derived sections
of this restriction are the given derived evaluation, followed by exact forgetting.
Sections and forgetting preserve products. Apply the derived-functor product
comparison to the Roos triangle, identifying its first map by its product
projections. This gives precisely the displayed triangle. The argument works for
empty V, all integer a, arbitrary unbounded F and arbitrary derived universes. -/
theorem affineBasisLowerTail_sections_reconstruction
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{u}]
    (F : CochainComplex X.Modules ℤ)
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1)))
    (a : ℤ) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    let G := S ⋙ forget₂
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
    let t := DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let E := (t.truncLT a).obj (DerivedCategory.Q.obj F)
    ∃ δ : (∏ᶜ (fun n : ℕ => G.rightDerivedFunctor.obj
        ((t.truncGE (-(n : ℤ))).obj E))) ⟶ (G.rightDerivedFunctor.obj E)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (fun n : ℕ => G.rightDerivedFunctor.map
        ((t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E))
        (G.rightDerivedFunctor.obj E)
        (Pi.lift (fun n : ℕ => G.rightDerivedFunctor.map
          ((t.truncGEπ (-(n : ℤ))).app E))) δ := by sorry

end AlgebraicGeometry
