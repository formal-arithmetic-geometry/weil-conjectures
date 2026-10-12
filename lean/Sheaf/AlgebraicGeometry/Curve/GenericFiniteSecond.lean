/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.RepresentationTheory.SylowModuleFiltration
import Sheaf.FieldTheory.OpenSubgroupFixedField
import Sheaf.AlgebraicGeometry.FiniteEtaleTrace
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree
import WeilConjectures.SixFunctors.Finite.GlobalSections
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.Curve.GenericComparison
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.NormalGenericConstant
import Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction

/-! # Finite generic sheaves and second cohomology

Source: blueprint `lem-sc-affine-generic-second`, proof paragraphs 1--3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsConnectedCurve

/-- The finite-stalk step of the generic second-cohomology argument.
Source: blueprint `lem-sc-affine-generic-second`, proof paragraphs 1--3.
(blueprint: lem-sc-affine-generic-finite-second)

Proof: identify the finite geometric stalk with a finite continuous Galois module and split
it into its primary summands. For a prime ell, the Sylow filtration lemma gives a finite
separable extension of degree prime to ell on which the module has a filtration by trivial
Z/ell modules. Restriction followed by finite etale trace is multiplication by the degree;
rescaling gives a retraction because the degree is invertible on the primary module.
Use `hmodel` for that extension. Its generic-point identification rewrites the induced
pushforward as the finite direct image of the generic pushforward on the smooth affine
normalization. Finite pushforward preserves cohomology, so vanishing upstairs implies
vanishing of the retract downstairs.
For each filtration step, generic direct image is left exact. Its cokernel defect has zero
generic restriction and is torsion, hence is acyclic in positive degrees. The two short
exact sequences and their long exact cohomology sequences therefore propagate second
cohomology vanishing along the filtration. Normality identifies the generic pushforward
of a finite constant sheaf with the constant sheaf. Apply `hconstant` on the normalization
for each trivial quotient. Induction, the retraction, and finite primary decomposition
finish the proof. The zero module is the empty-filtration case. -/
theorem subsingleton_sheafH_two_lowerStar_of_finite_stalk
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]
    (hmodel : ∀ (L : Type u) [Field L] [Algebra C.functionField L]
      [FiniteDimensional C.functionField L],
      IsFinite (C.fromNormalizationIn L) ∧ IsAffine (C.normalizationIn L) ∧
        IsConnectedCurve (C.fromNormalizationIn L ≫ f) ∧
        Smooth (C.fromNormalizationIn L ≫ f) ∧
        ∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField,
          e.hom ≫ (C.normalizationIn L).fromSpecFunctionField =
            (C.fromSpecOfAlgebraFunctionField L).toNormalization)
    (hconstant : ∀ {D : Scheme.{u}} (g : D ⟶ Spec (.of k)) [IsConnectedCurve g]
      [Smooth g] [IsAffine D] (ℓ : ℕ) [Fact ℓ.Prime],
      Subsingleton (Sheaf.H (D.constantZMod ℓ) 2))
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M)) :
    Subsingleton
      (Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M) 2) := by
  obtain ⟨N, j, hj, hN⟩ := finite_stalk_second_cohomology_retraction f hmodel hconstant M hM hfinite
  exact subsingleton_of_injective j hj hN

end AlgebraicGeometry.IsConnectedCurve
