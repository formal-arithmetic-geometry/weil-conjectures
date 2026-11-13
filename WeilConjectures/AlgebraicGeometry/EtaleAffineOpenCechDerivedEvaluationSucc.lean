/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.SpectralSequenceNatRowZero
import WeilConjectures.AlgebraicGeometry.EtaleAffineOpenCechResolutionColumns
import WeilConjectures.AlgebraicGeometry.EtaleOpenCechResolutionTotal

/-! # The positive-degree affine-open Čech edge comparison for étale sheaves

## References

* Stacks Project, Tags 03AZ and 03P2
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- An étale sheaf acyclic on affine objects is computed on a separated scheme by
its sections on a finite affine open covering, in positive degree.
(Stacks, Tags 03AZ and 03P2) -/
theorem nonempty_rightDerived_etale_affineOpenCech_succ
    (X : Scheme.{u}) [X.IsSeparated]
    (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hc : CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i)
    [PreservesFiniteLimits i] (ht : IsTerminal (i.obj ⊤))
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hvan : ∀ (W : X.Etale), IsAffine W.left → ∀ (q : ℕ), 0 < q →
      IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op W)).rightDerived q).obj G))
    (n : ℕ) :
    Nonempty ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op (i.obj ⊤))).rightDerived (n + 1)).obj G)
        ≅ ((cechComplexFunctor U).obj (i.op ⋙ G.obj)).homology (n + 1)) := by
  let I := injectiveResolution G
  let D := etaleOpenCechResolutionDoubleComplex X i U I
  obtain ⟨E, hE₂, hE⟩ := D.exists_spectralSequence
  obtain ⟨hzero, hpositive⟩ := etale_affineOpenCech_resolution_columns
    X i hi U hU G hvan I
  have hrow (p q : ℕ) (hq : 0 < q) : IsZero ((E.page 2).X (p, q)) := by
    obtain ⟨e⟩ := hE₂ p q
    exact e.isZero_iff.mpr
      (((((HomologicalComplex.homologyFunctor _ (.up ℕ) q).mapHomologicalComplex
        (.up ℕ)).obj D).sc p).isZero_homology_of_isZero_X₂ (hpositive q hq p))
  obtain ⟨eA⟩ := E.nonempty_abutment_iso_row_zero _ hE hrow (n + 1)
  obtain ⟨eB⟩ := hE₂ (n + 1) 0
  obtain ⟨eC⟩ := hzero
  obtain ⟨eD⟩ := nonempty_etale_openCech_resolution_total_iso
    X i hc ht U hcover G I (n + 1)
  exact ⟨eD.symm ≪≫ eA ≪≫ eB ≪≫
    (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso eC⟩

end AlgebraicGeometry.Scheme
