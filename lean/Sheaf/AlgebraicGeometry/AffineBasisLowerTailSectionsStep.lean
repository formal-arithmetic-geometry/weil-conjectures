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


import Sheaf.Algebra.Homology.LowerTruncationStepTriangle
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison

/-! # Affine-basis lower truncation tower inputs
Source: Stacks Project, Tags 0BKT, 0D64, 071B and 08D4. -/

@[expose] public section
universe u wC wA
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Positive acyclicity of actual homology sheaves makes the successive lower
truncation transition invertible in degree i once n >= 1-i.
Source: Stacks Project, Tag 0BKT (lemma-cohomology-over-U-trivial), bounded-below
hypercohomology argument, and Tag 08D4, proof of (2).
(blueprint: lem-sc-affine-basis-lower-tail-sections-step).

Proof: The lower-truncation step triangle has first object H^(-n)(E)[n].
Below a this sheaf is H^(-n)(F), and above or at a it is zero. Apply derived
sections and exact forgetting to this triangle. Its first object's homology in
degrees i and i+1 identifies by the shifted-single comparison with positive
right-derived sections in degrees n+i and n+i+1. These are positive since n >= 1-i.
The hypothesis on W=V and the module-cohomology-source comparison on the restriction
to V make both zero. The long exact homology sequence then makes the displayed
transition monic and epic, hence invertible. No termwise acyclicity, quasi-coherence,
boundedness or K-injectivity is required. Empty V obeys the same calculation. -/
theorem affineBasisLowerTail_sections_step_isIso
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{u}]
    (F : CochainComplex X.Modules ℤ)
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1)))
    (a i n : ℤ) (hn : 1 - i ≤ n) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    let G := S ⋙ forget₂
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
    let t := DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let E := (t.truncLT a).obj (DerivedCategory.Q.obj F)
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      (G.rightDerivedFunctor.map ((t.natTransTruncGEOfLE
        (-n) (-n + 1) (Int.le_add_one (le_refl (-n)))).app E))) := by sorry

end AlgebraicGeometry
