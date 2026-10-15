/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.Additive
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Flat K-flat resolutions on the small étale site

Source: Stacks Project, Cohomology on Sites, Lemma 21.17.11, Tag 06YS;
Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`
(blueprint: lem-kun-flat-resolution-existence).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every complex of modules over the constant coefficient ring on the small étale site
admits a quasi-isomorphism from a K-flat complex with flat terms.
Source: Stacks Project, Tag 06YS (blueprint: lem-kun-flat-resolution-existence).

Proof:
1. Take the ringed site with category `T.Etale`, topology `T.smallEtaleTopology`
(def-weil-pbc-etale-site), and constant ring sheaf obtained by sheafifying the constant
presheaf with value `Λ` (def-kun-constant-sheaf). Its pointwise ring operations make it
 a sheaf of commutative rings, and `G` is a cochain complex of its module sheaves.
2. Apply `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`
(lem-pc-kflat-resolution). This gives a K-flat complex `K`, flat in each degree,
and a degreewise surjective quasi-isomorphism `K ⟶ G`. Retain the complex, map,
K-flatness, flatness and quasi-isomorphism, forgetting degreewise surjectivity. -/
theorem exists_etale_flat_isKFlat_resolution
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (G : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)))) ℤ) (f : K ⟶ G),
      CochainComplex.IsKFlat K ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := T.smallEtaleTopology)
        (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) (K.X i)) ∧ QuasiIso f := by
  sorry

end AlgebraicGeometry.Scheme
