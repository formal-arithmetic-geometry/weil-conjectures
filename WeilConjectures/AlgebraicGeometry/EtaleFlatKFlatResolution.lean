/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

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
      CochainComplex.IsKFlatIndependentCoefficients K ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := T.smallEtaleTopology)
        (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) (K.X i)) ∧ QuasiIso f := by
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of Λ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  obtain ⟨K, f, hK, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
  refine ⟨K, f, hK, ?_, hf⟩
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (K.X i)).symm (hflat i)

end AlgebraicGeometry.Scheme
