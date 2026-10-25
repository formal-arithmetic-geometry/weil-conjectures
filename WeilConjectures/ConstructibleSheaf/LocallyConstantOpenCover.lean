/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.EtaleDescent
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf

/-!
# Finite local constancy is local for open covers

A sheaf on the small étale site of a scheme `X` is finite locally constant as soon as its
restrictions to the members of a family of open subschemes covering `X` are.

## Main definitions

- `AlgebraicGeometry.Scheme.Cover.ofOpens`: the étale cover of `X` by a covering family of
  open subschemes.

## Main statements

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_opens`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The étale cover of `X` by a family of open subschemes covering `X`. -/
def Cover.ofOpens {ι : Type u} (O : ι → X.Opens) (hO : ∀ x : X, ∃ i, x ∈ O i) :
    Cover.{u} etalePrecoverage X where
  I₀ := ι
  X i := O i
  f i := (O i).ι
  mem₀ := by
    refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun _ ↦ inferInstance⟩
    obtain ⟨i, hi⟩ := hO x
    exact ⟨i, ⟨x, hi⟩, rfl⟩

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- **Finite local constancy is local for open covers**: a sheaf whose restrictions to a family
of open subschemes covering `X` are finite locally constant is finite locally constant. -/
theorem IsFiniteLocallyConstantSheaf.of_opens {ι : Type u} (O : ι → X.Opens)
    (hO : ∀ x : X, ∃ i, x ∈ O i) (G : Sheaf X.smallEtaleTopology A)
    (hG : ∀ i, IsFiniteLocallyConstantSheaf (FA := FA) (CA := CA)
      ((Etale.upperStar A (O i).ι).obj G)) :
    IsFiniteLocallyConstantSheaf (FA := FA) (CA := CA) G :=
  have : ∀ i, IsFiniteLocallyConstantSheaf (FA := FA) (CA := CA)
      ((Etale.upperStar A ((Cover.ofOpens O hO).f i)).obj G) := hG
  IsFiniteLocallyConstantSheaf.of_cover (Cover.ofOpens O hO) G

end AlgebraicGeometry.Scheme
