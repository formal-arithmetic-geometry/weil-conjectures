/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.ModuleCohomologyBaseChange
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Surjectivity of degree-zero cohomology on a derived fibre

Source: Stacks Project, More on Algebra, Lemma 15.78.2, Tag 0A1U
(blueprint: def-sc-degree-zero-fibre-surjective).
-/

set_option autoImplicit false

universe uF wF

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map `H⁰(K) ⊗ κ(s) → H⁰(K ⊗ᴸ κ(s))` is surjective.
Choose a K-flat representative `P` of `K` and let `C = P_s` be its stalk complex of
`𝒪_{X,s}`-modules; `κ(s)` is `IsLocalRing.ResidueField 𝒪_{X,s}`, which is
`X.residueField s` by definition. The map is the recorded cohomology base-change map
`ModuleCat.cohomologyBaseChange` (def-pc-module-cohomology-base-change)
`κ(s) ⊗ H⁰(C) → H⁰(κ(s) ⊗ C)` in degree zero, and it is required to be epi.
Stalks are exact, so `H⁰(C) = H⁰(K)_s`, and K-flat stalks compute the derived
residue fibre (Tags 06YB, 06YS). The existential representative cannot make the
condition vacuous; changing the K-flat representative identifies these maps via their
canonical homology isomorphisms.
Source: Stacks Project, Tag 0A1U, hypothesis at i = 0; Tags 06YB and 06YS
(blueprint: def-sc-degree-zero-fibre-surjective). -/
def degreeZeroFibreSurjective (X : Scheme.{uF})
    [HasDerivedCategory.{wF} (SheafOfModules.{uF} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X) (s : X) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{uF} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsKFlat (R := X.sheaf) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
      Epi (ModuleCat.cohomologyBaseChange (B := IsLocalRing.ResidueField (X.presheaf.stalk s))
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace s).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) 0)

end AlgebraicGeometry
