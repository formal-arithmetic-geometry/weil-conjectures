/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalReductionPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
import all WeilConjectures.AlgebraicGeometry.Strict.StrictKummerCohomologyConcentration

/-! # Simultaneous diagonal reduction and geometric inverse image

Source: blueprint diagonal coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] diagonalScalarExtension diagonalForget diagonalScalarAdjunction
  Functor.mapDerivedCategory DerivedCategory

/-- Scalar extension commutes with inverse image, by conjugating the strict
restriction/direct-image square.
Source: blueprint diagonal coefficient changes, paragraph (3)
(blueprint: lem-diagonal-class-reduction-pullback). -/
def diagonalClassScalarPullback (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    diagonalScalarExtension l S ⋙ upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f ≅
      upperStar Ab.{u + 1} f ⋙ diagonalScalarExtension l X :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction Ab.{u + 1} f).comp (diagonalScalarAdjunction l X))
    ((diagonalScalarAdjunction l S).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f))).symm
    (by
      unfold diagonalForget
      exact Iso.refl _)

private theorem regular_resolution (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (K : CochainComplex (DiagonalAb X) ℤ) :
    ∃ (P : CochainComplex (DiagonalAb X) ℤ) (p : P ⟶ K),
      (∀ (n : ℕ) (i : ℤ), Mono (l ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p := by
  obtain ⟨P, p, hp, hflat, _⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
  refine ⟨P, p, ?_, hp⟩
  intro n i
  exact flat_multiplication_mono _
    (integerUnit_mono X _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)) _ (hflat i)

private theorem reduction_computes_regular (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems l X)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l X))
    (P : CochainComplex (DiagonalAb X) ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (l ^ (n + 1) • 𝟙 (P.X i))) :
    IsIso (D.ε.app P) := by
  let L := diagonalScalarExtension l X
  let : L.Additive := scalarExtension_additive l X
  let : PreservesFiniteLimits L := scalarExtension_exact l X
  let : PreservesColimits L :=
    (diagonalScalarAdjunction l X).leftAdjoint_preservesColimits
  let good : CochainComplex (DiagonalAb X) ℤ → Prop := fun K ↦
    ∀ (n : ℕ) (i : ℤ), Mono (l ^ (n + 1) • 𝟙 (K.X i))
  apply reduction_counit_on_class l L D good (regular_resolution l X) ?_ P hP
  intro K K' f hf hK hK'
  let := hf
  apply reductionTower_quasiIso l L D.ordinary f
  · intro n i
    let := hK n i
    have h := L.map_mono (l ^ (n + 1) • 𝟙 (K.X i))
    simpa only [L.map_nsmul, L.map_id] using h
  · intro n i
    let := hK' n i
    have h := L.map_mono (l ^ (n + 1) • 𝟙 (K'.X i))
    simpa only [L.map_nsmul, L.map_id] using h

/-- Geometric inverse image compares the simultaneous reductions as whole
strict systems, naturally on every integral derived input.
Source: blueprint diagonal coefficient changes, paragraph (3)
(blueprint: lem-diagonal-class-reduction-pullback).
Proof: forgetting scalars commutes strictly with direct image. Conjugating that
square gives the scalar-extension/inverse-image comparison. Exact inverse image
preserves prime-power torsion-free complexes. Flat-term resolutions provide a
common resolving class, and both supplied universal reduction counits are
invertible on it. Apply the normalized whole-system comparison to descend the
ordinary cokernel square. This construction uses one common resolution for all
levels, hence retains the quotient transitions. -/
theorem diagonalClassReduction_pullback (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l S))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l X)) :
    let F := upperStar Ab.{u + 1} f
    let G := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
    let V := (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l S) (DiagonalMod l X)).obj G
    ∃ (e : D.ordinary.E ⋙ V ≅ F ⋙ D'.ordinary.E)
      (q : D.T ⋙ V.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ D'.T),
      (∀ (n : ℕ) (M : DiagonalAb S),
        G.map ((D.ordinary.π n).app M) ≫ (e.hom.app M).app (op n) =
          (diagonalClassScalarPullback l f).hom.app M ≫
            (D'.ordinary.π n).app (F.obj M)) ∧
      ∀ P : CochainComplex (DiagonalAb S) ℤ,
        (∀ (n : ℕ) (i : ℤ), Mono (l ^ (n + 1) • 𝟙 (P.X i))) →
          V.mapDerivedCategory.map (D.ε.app P) ≫
              V.mapDerivedCategoryFactors.hom.app
                ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
              DerivedCategory.Q.map
                ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
            q.hom.app (DerivedCategory.Q.obj P) ≫
              D'.T.map (F.mapDerivedCategoryFactors.hom.app P) ≫
              D'.ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  let F := upperStar Ab.{u + 1} f
  let G := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  let good : CochainComplex (DiagonalAb S) ℤ → Prop := fun P ↦
    ∀ (n : ℕ) (i : ℤ), Mono (l ^ (n + 1) • 𝟙 (P.X i))
  obtain ⟨e, q, he, hq⟩ := diagonalDerivedReduction_pullback l
    (diagonalScalarExtension l S) (diagonalScalarExtension l X) F G
    (diagonalClassScalarPullback l f) D D' good (regular_resolution l S)
    (fun P hP ↦ reduction_computes_regular l S D P hP) (by
      intro P hP
      apply reduction_computes_regular l X D'
      intro n i
      change Mono (l ^ (n + 1) • 𝟙 (F.obj (P.X i)))
      let := hP n i
      have h := F.map_mono (l ^ (n + 1) • 𝟙 (P.X i))
      simpa only [F.map_nsmul, F.map_id] using h)
  exact ⟨e, q, he, hq⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
