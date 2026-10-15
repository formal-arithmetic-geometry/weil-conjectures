/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.Topology.NoetherianSpace

import Sheaf.AlgebraicGeometry.FpqcDetectsOpenness
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage
import Sheaf.Paper.CondensedPointBasisEvaluation
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Local triviality over continuous p-adic field coefficients

Source: Hemo--Richarz--Scholbach, Example 3.1, and the agent rank/descent argument
recorded in (blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Projection |X[S]| → S, using Spec LC(S,Z) = S × Spec Z and base change.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-weil-pbc-condensed-lfp-local-triviality). -/
noncomputable def profiniteTestProjection (X : Scheme.{u}) (S : Profinite.{u}) :
    C(((profiniteToProEtOf X).obj S).left, S) :=
  (ContinuousMap.fst.comp
    ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩).comp
      (Limits.pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)).base.hom

/-- The condensed coefficient ring is the ring sheaf of continuous functions on site objects.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
Proof: compatible continuous functions descend along fpqc covers, since fibre products
identify values over the same point and fpqc covers detect openness. On a weakly contractible
affine, point-basis evaluation gives continuous functions on the quotient of connected
components. Since E is totally disconnected these are exactly continuous functions on the
affine itself. The identifications respect restrictions and pointwise ring operations.
Weakly contractible affine covers and sheaf gluing extend this identification to the site.
The adjoint sends each f : C(S,E) to f composed with |X[S]| → S. These equations
determine the natural transformation on every S, hence uniquely determine the isomorphism. -/
theorem existsUnique_condensedFieldContinuousMapIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    ∃! e : Mon.mk (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) ≅
        Mon.mk ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousCoefficientRingSheaf X E)),
      ∀ (S : Profinite.{u}) (f : C(S, E)),
        (((pointUpperStarLowerStarAdjunction.comp
            (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv
              _ _ e.hom.hom).hom.app (Opposite.op S)) (ULift.up f) =
          ULift.up (f.comp (profiniteTestProjection X S)) := sorry

/-- Local finite presentations over continuous field coefficients are locally finite free.
Source: Hemo--Richarz--Scholbach, Example 3.1, with the agent rank/descent argument
(blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
Proof: use the preceding continuous-function realization. Pull a finite presentation to a
geometric point; inverse image and evaluation preserve cokernels, and covers of a geometric
point split. Its dimension is independent of the algebraically closed representative.
The presentation matrix consists of continuous functions, so the dimension is n minus its
pointwise rank. Flat going-down lifts generalizations through presentation covers.
Continuous functions to the Hausdorff field E agree at comparable points, hence the rank
descends and is constant on specializations. Noetherianity gives finitely many irreducible
components and sobriety gives their generic points. Rank levels are therefore clopen.
Restrict presentations to these levels. Nonvanishing loci of maximal-rank minors cover;
Gaussian elimination using the continuous inverse of each invertible minor reduces the
matrix to an identity block and a Schur complement. The latter vanishes pointwise, hence
is zero as a matrix of functions. Its cokernel is finite free. For rank zero use the zero
matrix directly. Composing the covers proves the assertion, including the empty scheme.
All cokernels are ordinary sheaf cokernels; no completeness hypothesis is used. -/
theorem exists_finiteFree_cover_of_condensedField_lfp
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Mod.IsFree
        ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
        (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P) := sorry

/-- The local triviality assertion applies on every noetherian locally closed stratum.
Source: the concluding application in the agent rank/descent argument accompanying
Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
Proof: restrict the module to a stratum of its finite locally closed stratification.
The coefficient composition comparison identifies the restricted ring with the condensed
coefficient ring of the stratum. Apply the local triviality theorem there, to the finite
presentations in the stratified constructibility hypothesis. Pullback preserves the
coefficient comparison, so its finite free modules give exactly the displayed ones.
This includes empty strata, rank zero, and presentations with zero rows or columns. -/
theorem exists_finiteFree_cover_on_condensedField_strata
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (S : Scheme.LocallyClosedStratification X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (hP : ∀ a : Fin S.n,
      IsLocallyFinitelyPresented
        ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
        (((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).mapMod
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P)) :
    ∀ (a : Fin S.n), TopologicalSpace.NoetherianSpace (S.domain a) →
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a), ∀ i : C.I₀,
        Mod.IsFree
          ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
            ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj
              (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)))
          (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod
            ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj
              (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))).obj
            (((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).mapMod
              (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P)) := sorry

end AlgebraicGeometry.ProEtale
