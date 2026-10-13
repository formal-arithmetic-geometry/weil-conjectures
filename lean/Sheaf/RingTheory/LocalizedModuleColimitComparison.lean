/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
/-! # Localized additive comparison
Source: Stacks Project, Algebra, Tag 02JO first paragraph and Tag 037D.
(blueprint: lem-pc-localized-module-colimit-comparison) -/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace Algebra
/-- Additive comparison for localization of a semilinear filtered diagram.
Source: Stacks Project, Algebra, Tag 02JO first paragraph and Tag 037D.
(blueprint: lem-pc-localized-module-colimit-comparison)
Proof: Lift the numerator of a fraction in M through D and its denominator through B,
then pass to a common upper bound. The denominator remains outside the contracted prime,
so the fraction lifts to N. For equality, lift a multiplier outside q witnessing the zero
cross difference and pass to a common stage. Semilinearity ensures that the cross difference
there maps to zero in M. The original additive colimit detects this zero at a later stage.
The multiplier remains outside the prime, so the localized fractions agree at that stage.
The stipulated transition and fraction formulas therefore give a bijective comparison
from the colimit of N. Addition is respected at common stages; the comparison is an
additive equivalence with the stated coprojection formula. -/
theorem localizedModuleColimitComparison
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {T : Type u} [CommRing T] {M : Type v} [AddCommGroup M] [Module T M]
    (B : Λ ⥤ CommRingCat.{u}) (D : Λ ⥤ AddCommGrpCat.{v})
    (N : Λ ⥤ AddCommGrpCat.{max u v})
    (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of T))
    (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
    [∀ i, Module (B.obj i) (D.obj i)]
    (hB : Nonempty (IsColimit (Cocone.mk (CommRingCat.of T) κ)))
    (hD : Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)))
    (hs : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x)
    (hν : ∀ i (b : B.obj i) (x : D.obj i),
      (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (b • x) =
        (@CommRingCat.Hom.hom _ (CommRingCat.of T) (κ.app i)) b •
          (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
    (q : PrimeSpectrum T)
    (eᵢ : ∀ i, N.obj i ≃+
      LocalizedModule (q.asIdeal.comap (κ.app i).hom).primeCompl (D.obj i))
    (hm : ∀ (i j : Λ) (f : i ⟶ j) (x : D.obj i)
      (s : (q.asIdeal.comap (κ.app i).hom).primeCompl),
      ∃ t : (q.asIdeal.comap (κ.app j).hom).primeCompl,
        (t : B.obj j) = (B.map f).hom s ∧
        eᵢ j ((N.map f).hom ((eᵢ i).symm (LocalizedModule.mk x s))) =
          LocalizedModule.mk ((D.map f).hom x) t)
    (g : ∀ i, N.obj i →+ LocalizedModule q.asIdeal.primeCompl M)
    (hg : ∀ i (x : D.obj i) (s : (q.asIdeal.comap (κ.app i).hom).primeCompl),
      g i ((eᵢ i).symm (LocalizedModule.mk x s)) =
        LocalizedModule.mk
          ((@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
          ⟨(@CommRingCat.Hom.hom _ (CommRingCat.of T) (κ.app i)) s, s.property⟩) :
    ∃ e : (colimit N : AddCommGrpCat.{max u v}) ≃+
      LocalizedModule q.asIdeal.primeCompl M,
      ∀ i (z : N.obj i), e ((colimit.ι N i).hom z) = g i z := by sorry
end Algebra
