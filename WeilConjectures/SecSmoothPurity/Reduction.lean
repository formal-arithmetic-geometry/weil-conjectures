/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocalizingExceptionalPreservation
public import WeilConjectures.AlgebraicGeometry.SmoothPurityScalarExtension
public import WeilConjectures.SecSmoothPurity.ReductionDirectImageComparison
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
import WeilConjectures.SecSmoothPurity.ReductionDirectImage
import WeilConjectures.SecSmoothPurity.ReductionExceptional

/-! # Coefficient comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/_section.md, node sk-lem-sp-reduction, order 1820
(blueprint: sk-lem-sp-reduction).

The theorem records the canonical direct-image comparison and its exceptional
mate on the constructible finite-Tor subcategories.  The proof takes the
restricted adjunctions and the invertible exceptional comparison from
`det-sp-reduction-exceptional`, invertibility of the direct-image comparison
on all of `Dctf` from `det-sp-reduction-direct-image`, and proves uniqueness
by injectivity of the B-adjunction Hom equivalence.
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

Proof.  `det-sp-reduction-exceptional` supplies the compact-support
preservation witnesses, the restricted adjunctions `F_A ⊣ G_A`, `F_B ⊣ G_B`,
and a natural comparison `c` satisfying the counit identity, invertible at
every `K`.  For an arbitrary `M` in `Dctf(X,A)`, its bounded homology lies in
a finite interval, so `det-sp-reduction-direct-image` makes the direct-image
comparison invertible at `M`.  For uniqueness, any `c'` with the same counit
identity has the same inverse transpose `ε_B ∘ F_B(c'_K)` as `c` under the
B-adjunction (the full-subcategory inclusion is faithful), so `c' = c`.
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
  obtain ⟨hFA, hFB, hSX, hSY, GA, GB, adjA, adjB, RA, RB, hb', c, hc, _⟩ :=
    reductionExceptional_isIso ℓ pchar hp hℓ k f d j p hf hA hB φ
  have hb (M : spFiniteConstructibleTorCategory X A) :
      IsIso ((reductionDirectImageComparison φ j p).app M.obj) := by
    obtain ⟨⟨a, b, hab, hz⟩, hconstructible, hTor⟩ := M.property
    have hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M.obj)} := by
      apply Set.Finite.subset (Set.finite_Icc a b)
      intro i hi
      constructor <;> by_contra! hn
      · exact hi (hz i (.inl hn))
      · exact hi (hz i (.inr hn))
    exact (reductionDirectImage_isIso ℓ pchar hp hℓ k f j p hf hA hB φ M.obj
      hbounded hconstructible hTor).1
  refine ⟨hFA, hFB, hb, GA, GB, adjA, adjB, c, ⟨hc.1, hc.2.1⟩, ?_⟩
  intro c' hc'
  apply NatTrans.ext
  funext K
  apply (adjB.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  apply (spFiniteConstructibleTor Y B).hom_ext
  exact (hc'.1 K).trans (hc.1 K).symm

end AlgebraicGeometry.ProEtale
