/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicSliceScalarComparisonData

/-! # Scalar extension on a pro-etale slice

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Inverse image to the pro-etale slice commutes with total derived extension of
pulled-back condensed coefficients, including nonflat coefficient maps.
Source: det-def-sfb-coefficient-change and sk-prop-sfb-cartesian-coefficients.
Proof: the ordinary scalar comparison identifies the two ordinary composites.
The two counits furnished by completedAdic_slice_scalarComparison_derived_data
exhibit the two derived composites as left derived functors of those ordinary
composites. Map the ordinary comparison to homotopy categories and then localize;
uniqueness of left derived functors gives the comparison on the entire unbounded
category. This is the same uniqueness argument as in the previous ringed-site
proof, now applied to the actual module objects over pulled-back condensed rings.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison). -/
theorem completedAdic_slice_scalarComparison (X : Scheme.{t}) (U : X.ProEt)
    {Λ Λ' : Sheaf (coherentTopology Profinite.{t}) Ab.{t + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] :
    Nonempty
      ((CondensedRing.upperStar Λ U.hom).mapDerivedCategory ⋙
          completedAdicSliceDerivedChange X U a ≅
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor ⋙
          (CondensedRing.upperStar Λ' U.hom).mapDerivedCategory) := by
  obtain ⟨e₀⟩ := completedAdic_slice_scalarComparison_underived X U a
  let e := Functor.isoWhiskerRight
    { hom := NatTrans.mapHomotopyCategory e₀.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory e₀.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] } DerivedCategory.Qh
  obtain ⟨α, α', hα, hα'⟩ := completedAdic_slice_scalarComparison_derived_data X U a
  let := hα
  let := hα'
  exact ⟨Functor.leftDerivedNatIso _ _ α α'
    (HomotopyCategory.quasiIso _ (.up ℤ)) e⟩

end AlgebraicGeometry.Scheme
