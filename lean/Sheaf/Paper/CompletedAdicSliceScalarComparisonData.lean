/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral

/-! # Universal data for the completed adic slice comparison

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E and 0D6D.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

set_option linter.defProp false in
/-- The universal ordinary and derived scalar-extension witness on the slice.
Its object and map equations determine ordinary tensor extension, while its
counit determines the derived functor.  Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
def completedAdicSliceChangeData (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (R.over U)))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (S.over U)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).map f)

/-- Ordinary scalar extension along the coefficient map restricted to the slice.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
def completedAdicSliceChange (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  (completedAdicSliceChangeData X U f).choose

/-- The chosen slice scalar-extension witness is additive.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
instance completedAdicSliceChange_additive (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    (completedAdicSliceChange X U f).Additive :=
  (completedAdicSliceChangeData X U f).choose_spec.choose_spec.choose_spec.choose

/-- The total left derived scalar-extension functor on the slice.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/
def completedAdicSliceDerivedChange (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  (completedAdicSliceChangeData X U f).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose

/-- Ordinary scalar extension commutes with restriction to the pro-etale slice.
The proof is the presheaf tensor comparison followed by the sheafification
universal property.  This is the ordinary (underived) step in the derived
comparison theorem.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison-underived).
-/
theorem completedAdic_slice_scalarComparison_underived (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    Nonempty
      ((SheafOfModules.overFunctor
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U ⋙
          completedAdicSliceChange X U f) ≅
        (completedAdicChange X f ⋙ SheafOfModules.overFunctor
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) U)) := by
  sorry


/-- Both derived composites are left derived functors of their ordinary composites.
The composite of exact slice restriction with derived slice extension, and the
composite of derived extension with exact slice restriction, each carry a counit to
the localized ordinary composite exhibiting it as a left derived functor along the
quasi-isomorphisms.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E and 0D6D.
Proof: every complex of R-modules has a flat-term K-flat resolution, and slice
restriction is exact and carries K-flat complexes to K-flat complexes (pullback by
the localization morphism of ringed topoi, Tag 0G7E). The universal counits of both
derived scalar extensions are invertible on K-flat complexes and their ordinary
extensions preserve quasi-isomorphisms between K-flat complexes. Hence both ordinary
composites send quasi-isomorphisms between K-flat complexes to isomorphisms, both
derived composites are computed on K-flat representatives, and the induced counits
are isomorphisms there; a functor with this property is a left derived functor, by
the universal property of the localization restricted to K-flat complexes.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison-derived-data).
-/
theorem completedAdic_slice_scalarComparison_derived_data (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    let O_R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
    let O_S := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
    let A := SheafOfModules O_R
    letI : (SheafOfModules.overFunctor O_R U).Additive := by
      exact (ringedOverFunctor_exactGeneral O_R U).1
    letI : (SheafOfModules.overFunctor O_S U).Additive := by
      exact (ringedOverFunctor_exactGeneral O_S U).1
    letI : (completedAdicChange X f).Additive := completedAdicChange_additive X f
    letI : (completedAdicSliceChange X U f).Additive :=
      completedAdicSliceChange_additive X U f
    letI : HasDerivedCategory A := HasDerivedCategory.standard _
    letI : HasDerivedCategory (SheafOfModules O_S) := HasDerivedCategory.standard _
    letI : HasDerivedCategory (SheafOfModules (O_R.over U)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory (SheafOfModules (O_S.over U)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory
        (SheafOfModules.{t + 1}
          (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
            ((ProEt.topology X).over U)
            (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).obj S))) :=
      HasDerivedCategory.standard _
    let Q_A := DerivedCategory.Qh (C := A)
    let F := completedAdicDerivedChange X f
    let F_U := completedAdicSliceDerivedChange X U f
    let L_U := ringedDerivedRestrictionGeneral O_R U ⋙ F_U
    let L := F ⋙ ringedDerivedRestrictionGeneral O_S U
    let G_U :=
      ((SheafOfModules.overFunctor O_R U ⋙ completedAdicSliceChange X U f).mapHomotopyCategory
        (.up ℤ)) ⋙ DerivedCategory.Qh
    let G :=
      ((completedAdicChange X f ⋙ SheafOfModules.overFunctor O_S U).mapHomotopyCategory
        (.up ℤ)) ⋙ DerivedCategory.Qh
    ∃ (α : Q_A ⋙ L_U ⟶ G_U) (α' : Q_A ⋙ L ⟶ G),
      L_U.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ)) ∧
      L.IsLeftDerivedFunctor α' (HomotopyCategory.quasiIso A (.up ℤ)) := by
  sorry


end AlgebraicGeometry.Scheme
