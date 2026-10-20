/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatClosure
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
/-!
# Factorization through a K-flat complex

Source: Stacks Project, Cohomology on Sites, Tag 0G7D, lemma-factor-through-K-flat,
including the final flat-terms assertion (blueprint: lem-pur-kflat-map-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{r}}

/-- A chain map with K-flat source factors up to homotopy through a K-flat target.

Source: Stacks Project, Cohomology on Sites, Tag 0G7D, lemma-factor-through-K-flat
(blueprint: lem-pur-kflat-map-factorization).

The proof follows the source and uses the recorded generic K-flat resolution and cone
closure statements. First form the distinguished cone triangle of `t`, and resolve its
cone by a K-flat complex `M` with flat terms. Compose the connecting map with the
resolution map, then take the shifted cone of that composite; this gives a complex `N`
whose outer maps are `u : D ⟶ N` and `v : N ⟶ M`, with the required cone signs. K-flatness
of shifts follows from the signed reindexing of the total tensor complex, and cone closure
then gives K-flatness of `N`. Rotating the two cone triangles and applying the triangulated
morphism completion to the commuting square defined by the resolution map produces
`c : N ⟶ I` and a homotopy from `t` to `u ≫ c`. The exact localization at
quasi-isomorphisms, followed by the third-isomorphism property for a morphism of
triangles, shows that `c` is a quasi-isomorphism. The homotopy is Mathlib's
`Homotopy t (u ≫ c)`, whose components are the maps `h^i : D^i ⟶ I^(i-1)` and whose
component equation is `t^i - (u ≫ c)^i = d_I^(i-1) h^i + h^(i+1) d_D^i`. If all
terms of `D` are flat, the same shifted-cone model has terms that are finite direct sums
of flat terms, so the flat-term implication is retained in the displayed witness. -/
theorem exists_kFlat_map_factorization
    {D I : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (t : D ⟶ I) (hD : IsKFlatIndependentCoefficients (J := J) (R := R) D) :
    ∃ (N : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (u : D ⟶ N) (c : N ⟶ I),
      IsKFlatIndependentCoefficients (J := J) (R := R) N ∧
        QuasiIso c ∧ Nonempty (Homotopy t (u ≫ c)) ∧
        ((∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (D.X i)) →
          ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (N.X i)) := by
  sorry

end CochainComplex
