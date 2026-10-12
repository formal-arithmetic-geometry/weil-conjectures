/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage
import Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange

/-! # Perfect direct image and arbitrary base change

Source: Stacks Project, Tags 0B91 and 0A1H (blueprint: lem-pc-rf-perfect-base-change).
-/

@[expose] public section

set_option autoImplicit false
universe uPF wPF
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- For a proper morphism of finite presentation and a finitely presented module flat
relative to its base, the derived direct image is perfect and the canonical map to the
base-changed module's derived direct image is invertible for every base change: every
map with the characterising property of the canonical one is an isomorphism.
The localization instances choose models of the derived categories and impose no
geometric conditions. Additivity of each module tensor pullback (a left adjoint) is
assumed only to state the left-derived structure of the derived pullback.
Source: Stacks Project, Tag 0B91, clause (2) (blueprint: lem-pc-rf-perfect-base-change).

Proof:
1. Properness gives separatedness and quasi-compactness (def-weil-proper-morphism).
Finite presentation of G gives quasi-coherence. Apply lem-pc-rf-base-change-flat-module
with the given relative flatness to get invertibility of the canonical map for every g.
2. Apply lem-pc-proper-support-perfect-direct-image with E equal to the structure sheaf
in degree zero. It is strictly perfect of rank one (def-pc-perfect-complex). The support
of G is closed by lem-weil-pbc-finite-type-module-support-closed. X itself is proper
over S (def-weil-pbc-closed-subset-proper-over-base), so this closed subset is proper
by lem-weil-pbc-closed-subset-proper-over-base-properties, clause (2). The tensor unit
identification O_X ⊗ᴸ G ≅ G gives perfectness of Rf_*G, as in Tag 0B91(2). -/
theorem perfect_derivedDirectImage_baseChange
    [∀ Y : Scheme.{uPF},
      HasDerivedCategory.{wPF} (SheafOfModules.{uPF} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{uPF}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [∀ U : S.Opens, HasDerivedCategory.{wPF}
      (SheafOfModules.{uPF} ((moduleRings S.toRingedSpace).over U))]
    [∀ {Y Z : Scheme.{uPF}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    (G : X.Modules) [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G]
    (hG : G.IsFlatOver f) :
    Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{uPF} (moduleRings X.toRingedSpace)) 0).obj G)) ∧
      ∀ {T : Scheme.{uPF}} (g : T ⟶ S) φ, IsDerivedModuleBaseChangeMap f g G φ → IsIso φ := by
  sorry

end AlgebraicGeometry
