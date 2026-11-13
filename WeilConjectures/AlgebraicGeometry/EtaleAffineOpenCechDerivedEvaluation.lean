/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleAffineOpenCechDerivedEvaluationSucc
import WeilConjectures.Topology.OpenCechZerothHomology

/-! # The affine-open Čech edge comparison for étale sheaves

Source: Stacks Project, Tag 03AZ, specialized to an acyclic affine-open covering,
and Tag 03P2, separated-case proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- An étale sheaf acyclic on affine objects is computed on a separated scheme by
its sections on a finite affine open covering.
(Stacks, Tags 03AZ and 03P2) -/
theorem nonempty_rightDerived_etale_affineOpenCech
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
    (q : ℕ) :
    Nonempty ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op (i.obj ⊤))).rightDerived q).obj G)
        ≅ ((cechComplexFunctor U).obj (i.op ⋙ G.obj)).homology q) := by
  cases q with
  | zero =>
    let : RepresentablyFlat i := flat_of_preservesFiniteLimits i
    let : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology :=
      (i.isContinuous_iff_coverPreserving).2 hc
    let F : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} :=
      ⟨i.op ⋙ G.obj, i.op_comp_isSheaf_of_isSheaf _ _ _ G.property⟩
    let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op (i.obj ⊤))
    obtain ⟨e⟩ := TopCat.Sheaf.nonempty_openCech_zerothHomology U hcover F
    exact ⟨E.rightDerivedZeroIsoSelf.app G ≪≫ e⟩
  | succ n =>
    exact nonempty_rightDerived_etale_affineOpenCech_succ X i hi hc ht U hU hcover G hvan n

end AlgebraicGeometry.Scheme
