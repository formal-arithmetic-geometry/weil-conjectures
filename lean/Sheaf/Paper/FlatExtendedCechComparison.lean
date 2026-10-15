/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ExtendedLocalizationCech
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.CategoryTheory.RingedSiteModules

/-! # Flat comparison of extended localization Čech complexes

Source: Stacks Project, Algebraization, Tag 099H
(blueprint: lem-weil-pbc-flat-extended-cech-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

/-- A flat coefficient extension unchanged modulo the generated ideal identifies
the extended alternating localization complexes by the canonical termwise map.
Source: Stacks Project, Tag 099H
(blueprint: lem-weil-pbc-flat-extended-cech-comparison).

Proof:
1. Localization commutes with scalar extension: a/g^k tensor b maps to
φ(a)b/φ(g)^k, with inverse b/φ(g)^k mapping to (1/g^k) tensor b. Sheafify
these formulas; they commute with localization maps and the degree-zero augmentation.
2. Use the explicit positive-power cochain Koszul complexes of Tag 0913:
in degree q the basis is the q-element subsets I, and insertion of j has
coefficient (-1)^a(j,I) f_j^(n+1). Paired insertions prove d squared is zero.
Multiplication by the subset product defines the transition to the next exponent.
3. The fraction cocone a e_I maps to a/(product_I f_i)^(n+1). Every fraction
occurs and equality of fractions is eventual equality in this sequential system.
Consequently its colimit is exactly the extended alternating localization complex;
these identifications commute with the coefficient comparison and augmentations.
4. Remove j from I with sign (-1)^a(j,I), or send the basis vector to zero
when j is absent. This homotopy satisfies d h_j + h_j d = f_j^(n+1) id.
Hence every cohomology sheaf is killed by each f_j^(n+1), and by the ideal
power r*n+1 for r positive. When r=0 the zero ideal itself suffices.
5. If the ideal kills a module sheaf, tensoring factors through the quotient
ring sheaf, so the quotient isomorphism identifies its canonical scalar-extension
map with the identity. Induct on a positive annihilating ideal power, using the
short exact sequence with submodule I^k F and quotient F/I^k F and exact tensoring.
The outer comparison maps are isomorphisms, hence so is the middle one.
6. Flatness and the exact-functor cohomology comparison identify the cohomology
of each scalar-extended Koszul complex with the scalar extension of its cohomology.
The comparison is the canonical map from step 5, hence an isomorphism in every degree.
7. The exact faithful forgetful functor to abelian sheaves preserves filtered
colimits, which are exact on any small site. Thus filtered colimits of module
sheaves are exact and commute with cohomology. Taking the colimit of the stage
quasi-isomorphisms gives the asserted quasi-isomorphism. For r=0 the quotient
hypothesis is precisely that φ is an isomorphism and the complexes are O[0] and B[0]. -/
theorem flat_extendedLocalizationCech_comparison_quasiIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (LocalizationCech.rings R)).sections)
    (hflat : IsFlat ((LocalizationCech.restriction φ).obj
      (unit (LocalizationCech.rings B))))
    (hquot : IsIso (LocalizationCech.quotientComparison φ r f)) :
    QuasiIso (LocalizationCech.comparison φ r f) := by
  sorry

end SheafOfModules
