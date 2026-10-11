/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Sheaf.AlgebraicGeometry.SheafExt
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Paper.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Basic

/-! # The local-to-global spectral sequence for sheaf Ext

Source: literature/stacks-project/equiv.tex, Lemma 0FZ3 and Cohomology Tag 0BQP
(blueprint: lem-sc-ext-sheaf-to-global-spectral-sequence).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

/-- The local-to-global spectral sequence for sheaf Ext, with its first-quadrant
vanishing and the resulting Ext vanishing criterion.
Source: Stacks Project, equiv.tex, Lemma 0FZ3, proof of (1), and Cohomology,
Section 0BQP (blueprint: lem-sc-ext-sheaf-to-global-spectral-sequence).

Proof:
1. Work in module sheaves and abelian groups, with T = sheaf Hom(F,-) and U =
global sections. These are left exact additive (def-sp-left-exact-additive).
Module sheaves are Grothendieck abelian (prop-pur-kinjective-resolutions-exist)
and have enough injectives (lem-weil-pbc-scheme-modules-enough-injectives);
abelian groups are Grothendieck abelian (lem-weil-pbc-ring-modules-grothendieck-abelian).
By lem-sc-ext-coherent-hom-injective-acyclic, T sends injectives to U-acyclics.
Apply thm-sp-grothendieck to obtain the first-quadrant spectral sequence.
2. Resolve G by injectives. This is K-injective by
lem-weil-pbc-bounded-below-injectives-kinjective. The definitions
 def-weil-pbc-sheaf-ext and pqf-def-cohomology identify R^q T with sheaf Ext
and R^p U with module cohomology. Global sections of sheaf Hom are Hom
(def-pur-sheaf-hom), so lem-weil-pbc-ext-via-injective-resolution and
def-sc-ext-sheaf identify the derived composite with global Ext.
3. The first-quadrant sequence gives a finite exhaustive filtration on each Ext
abutment. If its page-two terms in total degree n > d vanish, all later terms
and all associated graded pieces vanish. The finite filtration forces Ext^n = 0. -/
theorem exists_sheafExt_global_spectralSequence
    (X : Scheme.{u}) [CompactSpace X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasExt.{u} X.Modules]
    (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    ∃ (E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{u}),
      (∀ (p q : ℕ), Nonempty (
        (E.page 2).X (p, q) ≅
          AddCommGrpCat.of (((RingedSpace.moduleCohomology X.toRingedSpace p).obj
            ((AlgebraicGeometry.moduleSheafExt X q F G))))) ) ∧
      E.AbutsTo (fun n ↦ AddCommGrpCat.of
        (AlgebraicGeometry.Scheme.Modules.Ext F G n)) ∧
      ∀ (d : ℕ),
        (∀ (p q : ℕ), d < p + q → IsZero
          (AddCommGrpCat.of (((RingedSpace.moduleCohomology X.toRingedSpace p).obj
            ((AlgebraicGeometry.moduleSheafExt X q F G))))) ) →
        ∀ (n : ℕ), d < n → IsZero (AddCommGrpCat.of
          (AlgebraicGeometry.Scheme.Modules.Ext F G n)) := by
  sorry

end AlgebraicGeometry
