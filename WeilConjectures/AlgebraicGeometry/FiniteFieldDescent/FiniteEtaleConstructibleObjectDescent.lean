/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldDescent.FiniteEtaleConstructibleStages
import WeilConjectures.AlgebraicGeometry.FiniteFieldDescent.FiniteEtaleConstructibleStagesLimit
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexLimitDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.SurjectiveFlat
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatConstructibleModel
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatConstructibleComplex

/-! # Finite-stage constructible descent component

Source: Stacks Project, Lemma 09YU (3).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteFieldDescent

variable {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))

/-- Object descent for bounded constructible finite-Tor complexes.
Source: Stacks Lemma 09YU (3), essential-surjectivity paragraph
(blueprint: new-sfb-finite-etale-constructible-object-descent).

Proof: finite intermediate fields of L/K form a directed system; Y_L is their affine
inverse limit and each transition is finite etale. All stages and Y_L are Noetherian,
since Y is finite type over a field. Replace P by a bounded complex of flat constructible
modules using the finite-Tor model theorem. Descend its finitely many nonzero terms
by constructible-module limit descent, then descend the finitely many differential
maps at a common larger finite stage using full faithfulness. Enlarge the stage again
so that the finitely many equations d composed with d = 0 hold. Faithfully flat
surjectivity of Y_L to this stage detects flatness on stalks; constructibility already
holds for the descended terms. The resulting bounded flat constructible complex has
bounded constructible cohomology and finite Tor amplitude. Its derived pullback is
represented by the original flat complex, giving the required isomorphism to P.
The zero complex, empty scheme and identity extension satisfy the same construction. -/
theorem finiteEtaleConstructibleObjectDescent
    {L : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [Algebra.IsSeparable K L] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (P : DerivedCategoryModule Λ (scheme f L)) (hP : ctf f Λ P) :
    ∃ (E : IntermediateField K L), FiniteDimensional K E ∧
      ∃ (P_E : DerivedCategoryModule Λ (scheme f E)), ctf f Λ P_E ∧
        Nonempty ((pull f Λ (IntermediateField.val E)).obj P_E ≅ P) := by
  have : CompactSpace (scheme f L) := QuasiCompact.compactSpace_of_compactSpace (toSpec f L)
  obtain ⟨Pc, ⟨a, b, hab⟩, hPc, ⟨e⟩⟩ :=
    DerivedCategory.exists_flatConstructibleModel_of_locallyOfFiniteType (toSpec f L) P hP
  obtain ⟨_, _, hflat⟩ := isBoundedFlatComplex_iff.1 hab
  obtain ⟨E, PE, _, _, hPE, ⟨eE⟩⟩ :=
    Scheme.exists_boundedComplex_constructible_limit_descent (stageDiagram f L) (stageCone f L)
      (isLimitStageCone f L) (surjective_stageCone_π_app f L) Λ Pc a b hPc
  have hflatE (q : ℤ) : ObjectProperty.flat (PE.X q) :=
    flat_of_flat_upperStar_of_surjective _ (surjective_stageCone_π_app f L (.op E)) _
      (ObjectProperty.prop_of_iso _ ((HomologicalComplex.eval _ _ q).mapIso eE).symm (hflat q))
  refine ⟨E.1, E.2, _root_.DerivedCategory.Q.obj PE,
    DerivedCategory.constructibleFiniteTor_Q_obj PE a b hflatE hPE,
    ⟨(leftDerivedUpperStarIsoMapDerivedCategory _ _).app _ ≪≫
      (Functor.mapDerivedCategoryFactors _).app PE ≪≫
      _root_.DerivedCategory.Q.mapIso eE ≪≫ e.symm⟩⟩

end AlgebraicGeometry.Etale.FiniteFieldDescent
