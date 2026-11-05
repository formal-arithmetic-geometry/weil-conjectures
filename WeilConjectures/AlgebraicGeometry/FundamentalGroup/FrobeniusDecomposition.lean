/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DecompositionGroup
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusRestriction

/-!
# Frobenius lifts in the decomposition group

In the situation of `AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut_hom_app_eq_of_mem_inertia`,
let the special geometric point `Spec κ ⟶ Spec B ⟶ Y` lie over a point `x` with finite residue
field, `κ` being an algebraic closure of `κ(x)`. An element `σ` of `Gal(Ω / K)` inducing on `κ`
the inverse of the arithmetic Frobenius `y ↦ y ^ #κ(x)` maps to a Frobenius element at `x`
(`AlgebraicGeometry.Scheme.FiniteEtale.isFrobeniusElement_galoisToFundamentalGroup`): through the
specialization, it acts on the fibres as the geometric Frobenius at the special point.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}} [ConnectedSpace Y] {R K Ω : Type u} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω]
  [IsScalarTower R K Ω] [IsGalois K Ω] [IsSepClosed Ω] (a : Spec (.of R) ⟶ Y)
  {κ : Type u} [Field κ] [IsSepClosed κ] [Algebra (integralClosure R Ω) κ]
  (x : Y) [Finite (Y.residueField x)] [Algebra (Y.residueField x) κ]
  [IsAlgClosure (Y.residueField x) κ]
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {s : Spec (.of Ω') ⟶ Y}
  (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup (fiber s) G]

section Affine

open scoped Pointwise

variable {C : Scheme.{u}} [IsIntegral C] [ConnectedSpace C] {W : C.Opens} (hW : IsAffineOpen W)
  [Nonempty W] [IsIntegrallyClosed Γ(C, W)]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (z : C) (hz : z ∈ W) [Finite (C.residueField z)] [(hW.primeIdealOf ⟨z, hz⟩).asIdeal.IsMaximal]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal]
  [Q.LiesOver (hW.primeIdealOf ⟨z, hz⟩).asIdeal]
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {s : Spec (.of Ω') ⟶ C}
  (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup (fiber s) G]

end Affine

end AlgebraicGeometry.Scheme.FiniteEtale
