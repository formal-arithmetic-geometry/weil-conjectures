/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
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

/-! Finite trace and filtration reduction for generic second cohomology.

Source: blueprint `lem-sc-affine-generic-finite-second`, proof paragraphs 1--3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsConnectedCurve

/-- A map into a second-cohomology object with subsingleton codomain is enough to
deduce subsingletonness of the source. -/
theorem subsingleton_of_injective {A B : Type*} (j : A → B)
    (hj : Function.Injective j) (hB : Subsingleton B) : Subsingleton A := by
  constructor
  intro x y
  apply hj
  exact Subsingleton.elim _ _

/-- The finite primary decomposition, trace retraction, normalization, and filtration
argument produce an injective map from the desired cohomology into that of a finite
normalization model, whose second cohomology is subsingleton.  The construction uses
the finite Galois-module equivalence, Sylow filtration, finite etale trace degree,
exact finite pushforward, unrestricted strict henselization stalk comparison, exact
inverse image, torsion acyclicity, the derived long exact sequence, and the normal
generic constant-sheaf comparison.  These are exactly paragraphs 1--3 of the
blueprint proof; the remaining target theorem is the formal retraction consequence.
(blueprint: lem-sc-affine-generic-finite-second-retraction) -/
theorem finite_stalk_second_cohomology_retraction
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
    ∃ (N : Type (u + 1))
      (j : Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M) 2 → N),
      Function.Injective j ∧ Subsingleton N := by
  sorry

end AlgebraicGeometry.IsConnectedCurve
