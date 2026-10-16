/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
import Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.ContinuousCoefficientRealizations

/-! # Etale local integral lattices

Source: Bhatt--Scholze, Proposition 6.8.4(6) and Lemma 6.8.13.
(blueprint: lem-weil-pbc-continuous-etale-local-lattice)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Integral lattices exist on a quasi-compact quasi-separated etale cover.
Source: Bhatt--Scholze, Proposition 6.8.4(6), and the first paragraph of Lemma 6.8.13.
(blueprint: lem-weil-pbc-continuous-etale-local-lattice)

Proof in words. Evaluate an internal tensor action after the sheafification unit
on the presheaf tensor to obtain the sectionwise bilinear scalar action. Conversely,
a sectionwise action factors through the presheaf tensor and then through its
sheafification, since the target is a sheaf. These inverse operations preserve the
module laws, linear maps and finite free modules. The tensor universal property
identifies ordinary scalar extension in both encodings, and the inverse-image
adjunction identifies their pullbacks. The continuous-function realization identifies
the coefficient rings: the given norm on the finite extension equals the spectral
norm, and its closed unit ball is the valuation ring used in Proposition 6.8.4(6).
Thus a locally finite free internal rational module gives the lisse rational sheaf
of that proposition. Apply it to obtain integral lisse lattices on an etale covering
family. No compatibility among these lattices is required.

Refine each etale neighborhood by affine open subschemes. Etale maps are open, so
their images form an open cover of X. The underlying space of X is noetherian and
hence compact; finitely many of these images cover it. Take the finite disjoint union
of the corresponding affine neighborhoods. This scheme is compact and
quasi-separated, and its map to X is etale and surjective. Restrict the local lattices
to those neighborhoods and assemble them on their disjoint union; the scalar-extension
isomorphisms assemble in the same way. Transfer back to internal modules through the
explicit sectionwise equivalence and coefficient identifications. In rank zero use
the zero lattice, and over the empty scheme take the empty cover. Only a cover and a
lattice on it are asserted here; descent and stratification are separate steps. -/
theorem continuousLisse_etale_lattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj P)) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X), Etale p ∧ Surjective p ∧
      CompactSpace U ∧ QuasiSeparatedSpace U ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) U),
      (∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage U, ∀ s : D.I₀,
        Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (D.f s)).obj
          (condensedRingObj (integralCoeff ℓ E) U))
          (((ProEtale.upperStar Ab.{u + 1} (D.f s)).mapMod _).obj M)) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
