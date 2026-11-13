/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.AffineFinitePresentationFlatShorteningConstruction
import WeilConjectures.AlgebraicGeometry.AffineFinitePresentationFlatPseudoCoherent

/-! # Shortening a finite-presentation flat complex on an affine scheme -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Residue-field vanishing shortens a bounded finite-presentation flat complex on
an affine scheme without shrinking that scheme. This is an algebraic statement;
there is no proper morphism, coefficient sheaf, or competing cohomology model.
Source: Stacks Project, https://stacks.math.columbia.edu/tag/068V (residue criterion),
Tags 0653 and 064U (Tor-amplitude and finite-projective representatives), and 08EB. -/
theorem exists_affine_finitePresentation_flat_shortening (S : Scheme.{u})
    (hS : IsAffine S) (B : CochainComplex S.Modules ℤ) (b d : ℕ)
    (hBge : B.IsStrictlyGE 0) (hBle : B.IsStrictlyLE b)
    (hBflat : ∀ n : ℤ, (B.X n).IsFlatOver (𝟙 S))
    (hBqc : ∀ n : ℤ, (B.X n).IsQuasicoherent)
    (hBfp : ∀ n : ℤ, (B.X n).IsFinitePresentation)
    (hvan : ∀ (s : S) (q : ℕ), d < q →
      IsZero ((((Modules.pullback (S.fromSpecResidueField s)).mapHomologicalComplex _).obj
        B).homology q)) :
    ∃ D : CochainComplex S.Modules ℤ,
      D.IsStrictlyGE 0 ∧ D.IsStrictlyLE d ∧
      (∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S)) ∧
      (∀ n : ℤ, (D.X n).IsQuasicoherent) ∧
      (letI : CommRing (S.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(S, ⊤));
        letI := HasDerivedCategory.standard (ModuleCat.{u} (S.ringCatSheaf.obj.obj (.op ⊤)));
        DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
          (((SheafOfModules.evaluation.{u} S.ringCatSheaf (.op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D))) ∧
      ∀ {T' : Scheme.{u}} (g : T' ⟶ S) (q : ℕ),
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj D).homology q ≅
          (((Modules.pullback g).mapHomologicalComplex _).obj B).homology q) := by
  obtain ⟨D, hDge, hDle, hDflat, hDqc, hDfp, ⟨e⟩⟩ :=
    affine_finitePresentation_flat_shortening_construction S hS B b d hBge hBle
      hBflat hBqc hBfp hvan
  refine ⟨D, hDge, hDle, hDflat, hDqc,
    affine_finitePresentation_flat_pseudoCoherent S hS D d hDle hDflat hDqc hDfp, ?_⟩
  intro T' g q
  exact ⟨((Modules.pullback g).mapHomotopyEquiv e).toHomologyIso (q : ℤ)⟩

end AlgebraicGeometry.Scheme.Modules
