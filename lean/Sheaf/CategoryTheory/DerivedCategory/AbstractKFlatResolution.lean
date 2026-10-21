/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Abstract K-flat resolutions

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-def-sfb-derived-categories/def-sfb-left-derived-functor.proof.md`, first paragraph;
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`,
`CochainComplex.exists_quasiIso_flat_kFlat` (blueprint: lem-sfb-abstract-kflat-resolution).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Every unbounded complex has a K-flat resolution if there are functorial flat covers.
Source: blueprint main-20261015, `def-sfb-left-derived-functor.proof.md`, first paragraph;
upstream `CochainComplex.exists_quasiIso_flat_kFlat`
(blueprint: lem-sfb-abstract-kflat-resolution).

Proof: lift the flat-valued functor `B` to the full subcategory of flat objects.
The natural epimorphism `ε` then gives a functorial left resolution by flat objects.
Iterating this cover on kernels gives flat resolutions of individual objects.
Resolve the terms of each bounded above truncation of `L` and take the direct-sum
signed total complex. Its augmentation is a quasi-isomorphism, and bounded above
complexes of flat objects are K-flat. The compatible resolutions of the truncations
form a filtered diagram whose colimit resolves `L`. Exactness of filtered colimits
in a Grothendieck abelian category implies that this augmentation is a
quasi-isomorphism. Closedness and symmetry imply that tensoring on either side
preserves colimits; hence the colimit is still K-flat. These are precisely the
construction and argument of `CochainComplex.exists_quasiIso_flat_kFlat`; retain its
quasi-isomorphism and two-sided K-flatness and discard termwise flatness. The tensor
maps in the two-sided K-flatness test are the direct-sum total tensor maps used in
`IsKFlatForTotalTensor`. No upper or lower bound on `L` is needed. -/
theorem exists_quasiIso_isKFlatForTotalTensor
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    (B : C ⥤ C) (hB : ∀ X : C, ObjectProperty.flat (B.obj X))
    (ε : B ⟶ 𝟭 C) [∀ X : C, Epi (ε.app X)] (L : CochainComplex C ℤ) :
    ∃ (Q : CochainComplex C ℤ) (q : Q ⟶ L), QuasiIso q ∧ Q.IsKFlatForTotalTensor := by
  let : Abelian.HasFunctorialFlatResolution C :=
    ⟨{ F := ObjectProperty.lift _ B hB, π := ε }⟩
  obtain ⟨Q, q, hq, _, hQ⟩ := exists_quasiIso_flat_kFlat L
  refine ⟨Q, q, hq, ?_⟩
  constructor
  · intro Q' Q'' s hs
    exact hQ.whiskerLeft hs
  · intro Q' Q'' s hs
    exact hQ.whiskerRight hs

end CochainComplex
