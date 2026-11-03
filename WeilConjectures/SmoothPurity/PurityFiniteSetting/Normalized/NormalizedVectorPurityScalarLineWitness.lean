/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects

/-! # Existence of the normalized scalar Tate line comparison.

The comparison is the scalar-adjunction transpose of the existing ordinary Tate map,
which is uniquely fixed on root generators. It uses no vector-purity assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- A coefficient map admits the normalized degree-one Tate line comparison needed for
scalar reduction.

Source: current blueprint `sec-smooth-purity/sk-prop-an`,
`cor-pur-vector-bundle-purity.proof.md`, paragraph 2, Kummer normalization.

Proof: use the ordinary Tate map uniquely fixed on root generators. Its transpose under
ordinary extension/restriction of scalars is invertible by composition of the scalar
adjunctions. Take its associated isomorphism. The scalar adjunction cancels its inverse
hom-equivalence, so the generator equation is exactly the defining equation of the
ordinary Tate map. Transport the annihilator through the coefficient homomorphism.
(blueprint: lem-pur-normalized-vector-purity-scalar-line-witness). -/
theorem exists_purityScalarLineNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B]
    (hB : IsUnit (N : Γ(B, ⊤)))
    (A' : Type (u + 1)) [CommRing A'] [Finite A'] (φ : A →+* A') :
    ∃ hA' : (N : A') = 0,
    ∃ c : (Etale.purityScalarSheaf φ B).obj
        (Scheme.finiteEtaleTateLine B N A hA) ≅
      Scheme.finiteEtaleTateLine B N A' hA',
    PurityScalarLineNormalization φ N hA hA' B c := by
  have hA' : (N : A') = 0 := by
    simpa only [map_natCast, map_zero] using congrArg φ hA
  let c : (Etale.purityScalarSheaf φ B).obj
      (Scheme.finiteEtaleTateLine B N A hA) ≅
      Scheme.finiteEtaleTateLine B N A' hA' :=
    @asIso _ _ _ _
      (((Etale.purityScalarSheafAdjunction φ B).homEquiv _ _).symm
        (ProEtale.reductionEtaleTateMap φ B N hA hA'))
      (ProEtale.reductionTateOrdinaryScalar_isIso φ B N hA hA')
  refine ⟨hA', c, ?_⟩
  intro U a z
  change (((Etale.purityScalarSheafAdjunction φ B).homEquiv _ _ c.hom).hom.app U)
    (Scheme.finiteEtaleTateOneGenerator A N B hA U a z) = _
  simpa only [c, asIso_hom, Equiv.apply_symm_apply,
    ProEtale.reductionEtaleTateMap] using
    (ProEtale.reductionEtaleTateMap_existsUnique φ B N hA hA').exists.choose_spec U a z

end WeilConjectures.PurityFiniteSetting
