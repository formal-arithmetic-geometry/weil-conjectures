/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.FiniteEtaleEtaleLocalSplit
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.ContinuousCoefficientRealizations

/-! # Integral lattices descend along finite etale surjections

Source: Bhatt--Scholze, first paragraph of the proof of Lemma 6.8.13.
(blueprint: lem-weil-pbc-lisse-lattice-finite-etale-descent)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A lisse rational module with an integral lattice on a finite etale cover
has an integral lisse lattice on the base. No descent datum on the input lattice
is required. Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph.
(blueprint: lem-weil-pbc-lisse-lattice-finite-etale-descent)

Proof in words. Etale locally split the finite etale surjection into finitely many
sheets. Restriction to an etale slice is the inverse-image functor, and the coefficient
comparison identifies both coefficient rings with the same continuous-function rings
on that slice. Map the supplied lattice into the rational module using its
rationalization isomorphism. This is injective locally, since in free coordinates it
is the inclusion of integral-valued functions into field-valued functions. The
lattices on the different sheets are therefore submodule sheaves of the same rational
module. Define their sum by the local condition that a section can, on a covering, be
written as a finite sum of sections of those submodules. This is a sheaf submodule.

Refine a pro-etale cover to trivialize the rational module and all finitely many
sheet lattices. In free coordinates each embedded lattice is g_j A^n, where g_j and
its inverse are matrices of continuous E-valued functions. Around each point t,
shrink to the open set on which every entry of g_j(t)^{-1}g_j(s)-I belongs to the
maximal ideal, simultaneously for all j. These matrices are invertible over A:
their determinants are 1 modulo its maximal ideal, and the adjugate formula gives
continuous integral-valued inverses. Consequently every sheet lattice on this open
is the constant lattice g_j(t) A^n. Their finite sum is a finitely generated
torsion-free spanning A-submodule of E^n. The valuation ring is a DVR, so this sum is
finite free and rationalizes to E^n. This proves local finite freeness of the sum
as a sheaf, including its scalar-extension isomorphism.

On a double overlap the two splittings match after partitioning into opens according
to the permutation of their sheets. The embedded lattices match there since they
come from the same input lattice. Their sums agree, being independent of sheet order.
Equality is local, so the sum submodule sheaves agree on the whole overlap. These
identity maps inside the rational module satisfy the cocycle condition and glue to
an integral module on X. The rationalization maps and their local inverses glue as
well, giving the original rational module. The composite trivializing covers witness
local finite freeness. Rank zero and the empty base give the zero lattice. This
argument only descends from a given finite etale cover; it does not construct that
cover, stratify the base, or glue constructible strata. -/
theorem continuousLisse_finiteEtale_lattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj P))
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (hM : ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage U, ∀ s : D.I₀,
        Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (D.f s)).obj
          (condensedRingObj (integralCoeff ℓ E) U))
          (((ProEtale.upperStar Ab.{u + 1} (D.f s)).mapMod _).obj M))
    (e : Nonempty ((Mod.extendScalars
      (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P)) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X),
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (integralCoeff ℓ E) X))
          (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj N)) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj N ≅ P) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
