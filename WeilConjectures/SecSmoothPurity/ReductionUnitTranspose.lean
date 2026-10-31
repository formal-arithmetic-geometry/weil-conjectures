/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.ReductionExceptional
public import WeilConjectures.SecSmoothPurity.ReductionDirectImage
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations

/-! # Transpose of the coefficient-extension unit composite

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, Proof (1), the displayed transpose
calculation before applying the triangle identity
(blueprint: lem-sp-reduction-unit-transpose).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Transposing the proposed coefficient-extension unit gives the conjugate of the
scalar-extended A-triangle composite. The comparison `b` is an arbitrary natural
isomorphism of the stated functors; `c` is constrained by precisely its counit equation.
Source: latest blueprint, sk-lem-sp-reduction-compatibilities.proof.md, Proof (1)
(blueprint: lem-sp-reduction-unit-transpose).

Proof: Expand the inverse Hom equivalence of `adjB` as the B-compact-support
functor applied to the three factors, followed by its counit. Naturality of that
counit moves `GB.map (b.hom.app M)` to the last factor `b.hom.app M`.
Use `hc` at `P_A M` to replace the B-image of `c` followed by the B-counit with
`b.inv.app (G_A (P_A M))` followed by the scalar-extended A-counit. Naturality of
`b.inv` at the A-unit moves its inverse comparison past the B-image of the
scalar-extended A-unit. Functoriality of scalar extension then combines the
A-unit and A-counit into the displayed conjugate. These are the two proof steps
of the node, using det-sp-reduction-exceptional for the adjunctions and
 det-sp-scalar-extension-functor for the coefficient functor. The triangle identity
and the comparison with the B-unit are left to the parent theorem. -/
theorem reductionUnitTranspose
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (_hp : 0 < pchar) (_hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (_hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (hSX : ∀ K : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj K.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (b : reductionCtfCompactSupport A j p hFA ⋙ reductionCtfScalar φ Y hSY ≅
      reductionCtfScalar φ X hSX ⋙ reductionCtfCompactSupport B j p hFB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (_hc : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionCtfCompactSupport B j p hFB).map (c.app K) ≫
          adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K) =
        b.inv.app (GA.obj K) ≫ (reductionCtfScalar φ Y hSY).map (adjA.counit.app K))
    (M : spFiniteConstructibleTorCategory X A) :
    (adjB.homEquiv ((reductionCtfScalar φ X hSX).obj M)
      ((reductionCtfCompactSupport B j p hFB).obj
        ((reductionCtfScalar φ X hSX).obj M))).symm
      ((reductionCtfScalar φ X hSX).map (adjA.unit.app M) ≫
        c.app ((reductionCtfCompactSupport A j p hFA).obj M) ≫ GB.map (b.hom.app M)) =
      b.inv.app M ≫
        (reductionCtfScalar φ Y hSY).map
          ((reductionCtfCompactSupport A j p hFA).map (adjA.unit.app M) ≫
            adjA.counit.app ((reductionCtfCompactSupport A j p hFA).obj M)) ≫
        b.hom.app M := by
  sorry

end AlgebraicGeometry.ProEtale
