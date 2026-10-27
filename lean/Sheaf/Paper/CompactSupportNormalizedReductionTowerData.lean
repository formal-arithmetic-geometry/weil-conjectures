/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.NormalizedDVRTower

/-! # Finite compact-support normalized tower data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The finite compact-support terms admit a normalized tower and compatible level
isomorphisms.  This is the construction and transition part of the compact-support
normalization argument, before the independent constructibility and boundedness claim.
Source: current blueprint `lem-fix-operation-reduction.proof.md`, compact-support
paragraph; Bhatt--Scholze Lemmas 6.7.7 and 6.8.14; Stacks Tags 08J9 and 0FPT.
The proof chooses flat-term K-flat representatives, identifies finite quotient
reductions by the two-term free resolutions, and transports the scalar-adjunction
mates through extension by zero and proper direct image.  Coherence of these mates
assembles the normalized tower and gives the displayed adjacent transition square.
The construction works for identity and zero levels and never invokes an inverse
limit or a projection comparison.
(blueprint: lem-sf-compact-support-normalized-reduction-tower-data). -/
theorem compactSupport_normalizedReductionTower_data
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
    [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
    [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∃ (T : NormalizedDVRTower l E Y D hl)
      (a : ∀ n : ℕ, T.M n ≅
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
          ((scalarReductionDerivedExtension l E X n).obj K)),
      ∀ n : ℕ,
        (normalizedDVRTowerTransition l E Y D hl n.le_succ).app T.tower ≫
            (T.evaluationIso n ≪≫
              (scalarReductionDerivedRestriction l E Y n).mapIso (a n)).hom =
          (T.evaluationIso (n + 1) ≪≫
              (scalarReductionDerivedRestriction l E Y (n + 1)).mapIso (a (n + 1))).hom ≫
            sfCompactSupportTransition l E c K n := by
  sorry

end WeilConjectures
