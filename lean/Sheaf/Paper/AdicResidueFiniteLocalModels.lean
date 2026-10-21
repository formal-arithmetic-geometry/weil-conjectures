/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.AdicResidueLiftComparisons

/-! # Finite-level local models in the general adic lifting argument

Source: Stacks Project, proetale.tex, Tag 09C6, first half of the proof.
(blueprint: lem-sfb-adic-residue-finite-local-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

/-- A single local finite-projective model for all finite reductions, without compatible
markings or an isomorphism over completed coefficients.

Source: Stacks Project, proetale.tex, Tag 09C6, through the construction of the dual
complex; Tags 09C2, 09BI, 09AW and 099Q.
(blueprint: lem-sfb-adic-residue-finite-local-models).

Proof: restrict M to constant A-coefficients using the complete-object equivalence.
The given lisse cohomology is constructible on the one-stratum stratification, so 09C2
supplies all bounded constructible finite reductions with the same Tor interval and
normalized quotient maps. Cover X by connected clopen components of Noetherian affine
charts. Exact slice restriction preserves the quotient Roos tower and its unit, hence
completeness and the finite reductions. On each component, apply nilpotent-reduction
lissity to each A/J^(n+1)-complex and then 09BI. Take the geometric stalk of its normalized
quotient system at one point. These are perfect complexes E_n with derived reduction
E_(n+1) tensor A/J^(n+1) = E_n. Algebraic perfect inverse-limit reconstruction 09AW and
A's adic completeness give a bounded finite-projective A-complex P with these reductions.
Choose an affine weakly contractible pro-etale cover of that component. The weakly
contractible clause of 09BI identifies every finite reduction of M there with the same
constant P/J^(n+1), independently at each level. Localize the coefficient ring and all
projections on the actual slice; this is the site of the covering scheme by localization.
Restriction remains complete since it preserves products, kernels and the quotient Roos
unit. Each term of the completed realization of P is an idempotent summand of a finite
power of B, and is the limit of its corresponding J-power-torsion summands. Apply torsion
limit completeness to the bounded complex and the constant/completed equivalence to
obtain its local completeness. Assemble the covers by transitivity and generate a covering
sieve. A member U of that sieve factors through one of the original weakly contractible
covering objects V. Restriction along U -> V gives R; composition of exact slice
restrictions identifies R(L) with M|U and R(T) with the same completed constant P|U.
Weak contractibility is required only of V, never of arbitrary sieve refinements.
Empty charts use the
empty covering. No compatible local markings and no morphism between the complete
objects are asserted here, and no quotient is assumed perfect over A or finite as a set. -/
theorem adicResidue_finite_local_models
    (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A]
    (M : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J))
    (_hcomplete : CategoryTheory.ConstantCompletion.IsComplete
      (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X) A
        J 0) M)
    (C : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A J 0))
    (_hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (_hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (A ⧸ J ^ (0 + 1))
      ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (a b : ℤ) (_hab : a ≤ b)
    (_htor : ∀ P : CategoryTheory.ConstantCompletion.Cx
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := smallModelComparisonEtaleTopology.{u, v} X)
        (R := CategoryTheory.ConstantCompletion.finite
          (smallModelComparisonEtaleTopology.{u, v} X) A J 0) P →
      Nonempty ((CategoryTheory.ConstantCompletion.Q
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)).obj P ≅ C) →
      ∀ (N : CategoryTheory.ConstantCompletion.Mod
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0))
        (q : ℤ), q < a ∨ b < q →
        IsZero (adicResidueTensorCohomology.{max v (u + 1)}
          (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X)
            A J 0) P N q))
    (_hres : Nonempty
      ((CategoryTheory.ConstantCompletion.extend
        (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X)
          A J 0)).obj M ≅
        (adicResidueComparison.{u, v} X (A ⧸ J ^ (0 + 1))).obj C)) :
    ∃ S : Sieve ((AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj
        (⊤_ X.ProEt)),
      S ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
      ∀ (U : coefficientProEtaleSiteModel.{u, v} X)
        (f : U ⟶ (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj
          (⊤_ X.ProEt)), S f →
        ∃ (V : coefficientProEtaleSiteModel.{u, v} X)
          (R : AdicResidueLocalDerived.{u, v} X J V ⥤
            AdicResidueLocalDerived.{u, v} X J U)
          (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (c d : ℤ),
          P.IsStrictlyGE c ∧ P.IsStrictlyLE d ∧
          (∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) ∧
          IsAffine ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj V).left ∧
          AdicResidueSliceWeaklyContractible.{u, v} X V ∧
          let B := CategoryTheory.ConstantCompletion.completed
            (coefficientProEtaleModelTopology.{u, v} X) A J
          let T := (adicResidueRestriction B V).obj (adicResidueConstantPerfect X J P)
          let L := (adicResidueRestriction B V).obj M
          Nonempty (R.obj L ≅ (adicResidueRestriction B U).obj M) ∧
          Nonempty (R.obj T ≅ (adicResidueRestriction B U).obj
            (adicResidueConstantPerfect X J P)) ∧
          CategoryTheory.ConstantCompletion.IsComplete
            (adicResidueLocalProjection.{u, v} X J V 0) T ∧
          CategoryTheory.ConstantCompletion.IsComplete
            (adicResidueLocalProjection.{u, v} X J V 0) L ∧
          ∀ n : ℕ, Nonempty
            ((adicResidueLocalReduction.{u, v} X J V n).obj T ≅
              (adicResidueLocalReduction.{u, v} X J V n).obj L) := by
  sorry

end AlgebraicGeometry.Scheme
