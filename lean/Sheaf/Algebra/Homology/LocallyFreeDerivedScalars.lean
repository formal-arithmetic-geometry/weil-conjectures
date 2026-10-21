/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction

/-! # Derived scalar extension of locally finite free module sheaves

Source: Stacks Project, Modules on Sites, Tags 0GN1 and 08FC; Cohomology on Sites,
Tags 06YQ and 06YY (blueprint: lem-sfb-locally-free-derived-scalars).

The ordinary functor and its universal derived comparison are those of
`DerivedChangeOfRingsCochainModel`. Its object and map equations fix ordinary extension
as sheafification of sectionwise scalar extension, with the new ring acting on the left.
The degree-zero comparison below is its counit followed by the standard single-complex
isomorphism. In particular it is not an arbitrarily selected isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u v r wR wB

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Sheaf J CommRingCat.{r}}

/-- The canonical degree-zero scalar comparison, formed from the universal derived counit
and the natural isomorphism commuting an additive functor with a single complex.
Source: Stacks Project, Tag 06YY, identity K-flat resolution computation
(blueprint: lem-sfb-locally-free-derived-scalars). -/
noncomputable def locallyFreeScalarComparison
    {B : Sheaf J CommRingCat.{r}} {φ : R ⟶ B}
    [HasDerivedCategory.{wR}
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wB}
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J B))]
    (D : DerivedChangeOfRingsCochainModel φ)
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) :
    D.T.obj (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ⟶
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj (D.E.obj M)) :=
  D.ε.app ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex D.E (.up ℤ) 0).hom.app M)

/-- A module sheaf locally finite free on slice sites is flat, its single complex is
K-flat, and its canonical derived scalar comparison is invertible for every ring map.
Scalar extension preserves each local finite rank, and the comparisons commute with maps.
Source: Stacks Project, Modules on Sites, Tags 0GN1, 08FC and Section 03EK;
Cohomology on Sites, Tags 06YQ, 06YT and 06YY.

Proof, following the DAG:
1. Trivialize on a covering and express any finite relation in the local basis. Its
coordinates give the finite factorization in `lem-weil-pbc-site-flat-equational-criterion`,
including the empty basis. Thus tensoring by M is exact (`def-pc-flat-sheaf-modules`).
2. The degree-zero complex is bounded above with flat terms, since its other terms are
zero. Apply `lem-pc-bounded-above-flat-kflat-site` to obtain K-flatness.
3. Compute derived extension on the identity K-flat resolution, using the canonical
counit of `lem-pur-derived-change-of-rings`. The single-complex isomorphism identifies
its target with ordinary extension in degree zero. Naturality of the counit and that
isomorphism gives the displayed square; no flatness of the target ring is used.
4. In Mod(R), the relative coequalizer of `sk-def-sfb-change-of-scalars` is the same
balanced sheaf tensor: the unit and balancing identify its two arrows. Exact tensoring
on either side also carries quasi-isomorphisms to quasi-isomorphisms, by
`lem-weil-pbc-exact-functor-complex-cohomology`. Thus the K-flat computation agrees with
the total left derived convention of `sk-def-sfb-derived-categories`.
5. Apply `lem-sfb-localized-site-tensor-restriction` on each trivializing slice.
The maps b tensor (a_q) ↦ (b φ(a_q)) and (b_q) ↦ sum b_q tensor e_q are inverse
and B-linear. They preserve the very same covering and ranks, including zero rank.
(blueprint: lem-sfb-locally-free-derived-scalars). -/
theorem locallyFree_derived_scalars
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
    (hM : ∀ X : C, ∃ S : Sieve X, S ∈ J X ∧
      ∀ (U : C) (f : U ⟶ X), S f → ∃ n : ℕ,
        Nonempty (M.over U ≅ ∏ᶜ (fun _ : Fin n ↦
          unit ((derivedChangeRingIndependentCoefficients J R).over U)))) :
    IsFlatOnSite (R := R) M ∧
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ∧
    ∀ (B : Sheaf J CommRingCat.{r}) (φ : R ⟶ B)
      [HasDerivedCategory.{wR}
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
      [HasDerivedCategory.{wB}
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J B))]
      (D : DerivedChangeOfRingsCochainModel φ),
      IsIso (locallyFreeScalarComparison D M) ∧
      (∀ (U : C) (n : ℕ),
        Nonempty (M.over U ≅ ∏ᶜ (fun _ : Fin n ↦
          unit ((derivedChangeRingIndependentCoefficients J R).over U))) →
        Nonempty ((D.E.obj M).over U ≅ ∏ᶜ (fun _ : Fin n ↦
          unit ((derivedChangeRingIndependentCoefficients J B).over U)))) ∧
      (∀ (N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
        (a : M ⟶ N),
        D.T.map (DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map a)) ≫
            locallyFreeScalarComparison D N =
          locallyFreeScalarComparison D M ≫
            DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map (D.E.map a))) := by
  sorry

end SheafOfModules
