/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalarsStrictArrow

/-! # K-flatness of fixed scalar chart coordinates

Source: Stacks Project, Tags 03CY, 06YN and 03DH.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

/-- The fixed-scalar encoding followed by restriction to a weakly etale chart carries K-flat
complexes over the constant ring sheaf to K-flat complexes of sheaves of `B`-modules on the
chart. This is true but not yet formalized.
Source: Stacks Project, Tags 03CY, 06YN and 03DH.

Proof sketch: the fixed-scalar encoding is an exact monoidal equivalence: the sheafified tensor
product over the constant ring sheaf is the sheafified tensor product of sheaves of `B`-modules
(compare the private `restrictionTensor` in
`ProEtaleRestrictedTensorFiniteLocalConstancySupplement`, stated only for finite `B`).
Monoidal equivalences preserve K-flatness
(`Functor.kFlat_mapHomologicalComplex_obj_of_isEquivalence`), once `IsKFlatTensor` is
identified with `kFlat`. Restriction to the weakly etale chart preserves K-flatness: `j_!` is
exact and faithful on the chart, and the projection formula `j_!(K|_V ⊗ L) ≅ K ⊗ j_! L`
reduces acyclicity of `K|_V ⊗ L` to that of `K ⊗ j_! L`; the repository only has `j_!` for
monomorphisms (`ProEtale.localizationLowerShriek`) and no projection formula for it. -/
theorem finiteCoefficientSliceRestriction_kFlat_of_constant
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (V : X.Etale)
    (K : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ)
    (hK : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X B)
      ((Functor.mapHomologicalComplex (SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ))
          (.up ℤ)).obj K)) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((finiteCoefficientSliceRestriction X B R φ V).mapHomologicalComplex (.up ℤ)).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
