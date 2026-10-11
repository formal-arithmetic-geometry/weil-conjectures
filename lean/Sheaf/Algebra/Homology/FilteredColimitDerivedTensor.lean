/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Filtered colimits and cohomology of derived tensor products

Source: Stacks Project, Tags 06Y6, 06YR and 00DB
(blueprint: lem-pc-filtered-colimit-derived-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u wR wA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace DerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{u} A)]

/-- The canonical cohomology comparison for a filtered colimit is an `A`-module isomorphism,
natural in the fixed `A`-complex and in the diagram. Source: Stacks Project, Tags 06Y6,
06YR and 00DB (blueprint: lem-pc-filtered-colimit-derived-tensor).

`T` is the bifunctor supplied by `lem-pc-derived-tensor-second-factor-functor`, selected
from its existence theorem. `H M` is `Hⁿ(M ⊗ᴸ_R -)` on complexes of `R`-modules.
The comparison is `colimit.post`; its coprojection equation specifies the original maps,
and the last two equations give naturality in `M` and in the diagram, respectively.

Proof, following the four DAG steps:
1. Choose a K-flat `R`-resolution `E → M` after restriction of scalars
   (`lem-pc-kflat-resolution`). For a K-flat resolution `F → N`, the zigzag
   `Tot(F ⊗ M) ← Tot(F ⊗ E) → Tot(N ⊗ E)` consists of quasi-isomorphisms of
   underlying `R`-complexes. Use `lem-pur-quasi-iso-cone-acyclic`,
   `lem-pc-tensor-mapping-cone-iso`, signed symmetry and `def-pc-kflat-complex`.
   The derived-functor dependency identifies the first term with the derived tensor.
2. Hold `E` fixed. The zigzags are natural in `N`, independently of the chosen `F`,
   by `lem-pc-derived-tensor-second-factor-functor`. Termwise tensor totalization
   commutes with the colimit by `lem-pc-module-filtered-colimits-tensor` on the
   one-point site, with precisely the maps induced by the coprojections.
3. The exactness clause of `lem-pc-module-filtered-colimits-tensor` preserves kernels
   and images in degrees `n-1,n,n+1`. Thus cohomology commutes with this colimit,
   for every integer `n`, without a boundedness assumption (Tag 00DB).
4. The resulting map is the canonical comparison by step 2. Its components are
   `A`-linear by the derived-functor dependency, so its bijective underlying map
   has an `A`-linear inverse. Functoriality gives naturality in diagrams; clause (3)
   of that dependency gives naturality for maps of the fixed `A`-complex. -/
theorem filteredColimit_derivedTensor_cohomology (f : R →+* A)
    (I : Type u) [SmallCategory I] [IsFiltered I] (n : ℤ) :
    let QR := (Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤
      DerivedCategory (ModuleCat.{u} R))
    let T := Classical.choose (exists_derivedTensor_second_factor_functor f).2
    let H := fun M : CochainComplex (ModuleCat.{u} A) ℤ ↦
      QR ⋙ T.obj M ⋙ homologyFunctor (ModuleCat.{u} A) n
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ)
      (N : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ),
      IsIso (colimit.post N (H M))) ∧
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ)
      (N : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (j : I),
      colimit.ι (N ⋙ H M) j ≫ colimit.post N (H M) = (H M).map (colimit.ι N j)) ∧
    (∀ (M M' : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ M')
      (N : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ),
      let η := whiskerRight (whiskerLeft QR (T.map g))
        (homologyFunctor (ModuleCat.{u} A) n)
      colim.map (whiskerLeft N η) ≫ colimit.post N (H M') =
        colimit.post N (H M) ≫ η.app (colimit N)) ∧
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ)
      (N N' : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (a : N ⟶ N'),
      colim.map (whiskerRight a (H M)) ≫ colimit.post N' (H M) =
        colimit.post N (H M) ≫ (H M).map (colim.map a)) := by
  sorry

end DerivedCategory
