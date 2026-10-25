/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointExchangeOpen
public import WeilConjectures.TraceFormula.Specialization.SupportClosureProper

/-!

# The compact-support exchanges of the deformation to the normal cone

For a correspondence `c` contracting at `y`, the compact-support exchanges of blueprint
`det-nearby-exchange-maps` (3) for the support map
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.supportCompactSupportExchange`, through
the compactification `C ⊂ C̄ ⟶ X ⨯ X` deformed along `c̄⁻¹(x, x)`) and for the structure map of `X`
(`ProEtale.CondensedRing.pointCompactSupportExchangeOfSeparated`, through a compactification
`X ⊂ X̄` and the dense compactification of the deformation of `X̄`) give the trace specialization
`deformationTraceSpecialization`. This file states that these exchanges specialize the class of
the component `B ∋ y` of the fixed locus
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.specializesComponentClass_deformation`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence

namespace IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k'] (F : c.FixedLocus)

/-- **The compact-support exchanges of the deformation specialize the class of `B`** (blueprint
`det-tf-sp-theta-proper-constant`, `det-tf-sp-theta-open-constant`, with
`det-tf-fixed-deformation-points`; Varshavsky, *Lefschetz–Verdier trace formula and a
generalization of a theorem of Fujiwara*, §1.4–§2): for the exchanges `ν_c`
(`supportCompactSupportExchange`) and `ν_X` (`pointCompactSupportExchangeOfSeparated`), the
exchange `ν_F` of the fixed loci maps the specialization of the unit class of the special fixed
locus `F'` to the specialization of the class of the component `B ∋ y`. Near `y` the deformed fixed
locus is the constant family `B × S` up to nilpotents, on which `ν` is the inverse of the proper
exchange and is compatible with the specialization units. -/
theorem specializesComponentClass_deformation {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))}) :
    hc.SpecializesComponentClass k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F j :=
  sorry

end IsContractingAt

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
