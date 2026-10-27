module

public import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
public import Sheaf.Paper.SmoothPurityScalarExtension
public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
import Sheaf.SecSmoothPurity.ReductionDirectImage
import Sheaf.SecSmoothPurity.ReductionExceptional

/-! # Coefficient comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/_section.md, node sk-lem-sp-reduction, order 1820
(blueprint: sk-lem-sp-reduction).

The theorem records the canonical direct-image comparison and its exceptional
mate on the constructible finite-Tor subcategories.  The proof is postponed;
the dependencies provide the fixed compactification, the restricted
adjunctions, and the exceptional chart comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/- The comparison in the statement is `reductionDirectImageComparison φ j p`.
   Its inverse is used in the counit equation below. -/
/--
For a smooth morphism in the standing finite-type scheme setting and a map of
finite ell-primary coefficient rings, extension of coefficients commutes with
compact support.  The exceptional comparison is the unique natural mate whose
counit is the coefficient extension of the A-counit followed by the inverse of
the canonical compact-support comparison.  The exceptional comparison is an
isomorphism objectwise.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/_section.md, node sk-lem-sp-reduction, order 1820
(blueprint: sk-lem-sp-reduction).

Proof plan.  Use the scalar-extension functor and the preservation theorem to
restrict all ambient functors to bounded constructible finite-Tor complexes.
The direct-image comparison from `det-sp-reduction-direct-image` is invertible
on those complexes.  For each `K`, transpose
`(ε_A K)_B` after this inverse comparison through the B-adjunction; the
adjunction hom-equivalence gives existence and uniqueness and, by its
naturality, a natural transformation in `K`.  Finally use
`det-sp-reduction-exceptional` to identify this mate with the chart comparison
and obtain objectwise invertibility.
-/
theorem sp_reduction
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    ∃ (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
      (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
        spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj)),
      ∃ (hb : ∀ M : spFiniteConstructibleTorCategory X A,
          IsIso ((reductionDirectImageComparison φ j p).app M.obj)),
        ∃ (GA : spFiniteConstructibleTorCategory Y A ⥤
            spFiniteConstructibleTorCategory X A)
          (GB : spFiniteConstructibleTorCategory Y B ⥤
            spFiniteConstructibleTorCategory X B)
          (adjA : (spFiniteConstructibleTor Y A).lift
            ((spFiniteConstructibleTor X A).ι ⋙ reductionCompactSupport A j p) hFA ⊣ GA)
          (adjB : (spFiniteConstructibleTor Y B).lift
            ((spFiniteConstructibleTor X B).ι ⋙ reductionCompactSupport B j p) hFB ⊣ GB),
          ∃! c : GA ⋙ scalarExtensionCtfFunctor ℓ hA hB φ X ⟶
              scalarExtensionCtfFunctor ℓ hA hB φ Y ⋙ GB,
            (∀ K : spFiniteConstructibleTorCategory Y A,
              (reductionCompactSupport B j p).map (c.app K).hom ≫
                  (adjB.counit.app ((scalarExtensionCtfFunctor ℓ hA hB φ Y).obj K)).hom =
                @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app
                    (GA.obj K).obj) (hb (GA.obj K)) ≫
                  (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) ∧
            (∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c.app K)) := by
  sorry

end AlgebraicGeometry.ProEtale
