/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.SecSmoothPurity.ReductionDirectImage
public import WeilConjectures.SecSmoothPurity.ReductionExceptional
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor

/-! # Transpose of two successive exceptional coefficient comparisons

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, Proof (2)
(blueprint: lem-sp-reduction-composition-transpose).

The direct-image comparisons are arbitrary natural isomorphisms. No cocycle for them,
and no naturality or invertibility of the exceptional comparisons, is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The recorded canonical scalar associator, on the full bounded constructible finite-Tor
subcategory. The three membership witnesses only package the existing derived objects.
Source: blueprint Proof (2), its scalar-associator convention, and
`det-sp-scalar-extension-functor`, clause (4)
(blueprint: lem-sp-reduction-composition-transpose). -/
def reductionCtfScalarCompositionIso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u})
    (hAB : ∀ K : spFiniteConstructibleTorCategory T A,
      spFiniteConstructibleTor T B ((scalarExtensionFunctor φ T).obj K.obj))
    (hBC : ∀ K : spFiniteConstructibleTorCategory T B,
      spFiniteConstructibleTor T C ((scalarExtensionFunctor ψ T).obj K.obj))
    (hAC : ∀ K : spFiniteConstructibleTorCategory T A,
      spFiniteConstructibleTor T C ((scalarExtensionFunctor (ψ.comp φ) T).obj K.obj))
    (K : spFiniteConstructibleTorCategory T A) :
    (reductionCtfScalar ψ T hBC).obj ((reductionCtfScalar φ T hAB).obj K) ≅
      (reductionCtfScalar (ψ.comp φ) T hAC).obj K :=
  ObjectProperty.isoMk (spFiniteConstructibleTor T C)
    ((scalarExtensionFunctor_composition φ ψ T).app K.obj)

/-- The transpose before the direct-image cocycle, with the scalar associators inserted
at both endpoints. The maps `cAB` and `cBC` are just component families; their two counit
identities suffice. The inverse on the right is that of the consecutive `b` maps
conjugated by the canonical scalar associators, rather than a comparison for `ψ.comp φ`.
Source: blueprint Proof (2), before invoking the direct-image cocycle
(blueprint: lem-sp-reduction-composition-transpose).

Proof plan:
1. In iterated scalar coordinates put a = cAB(K) and h = cBC(K_B). The inverse Hom
bijection is P_C(h composed with U'(a)) followed by the C-counit. Apply the assumed
B-to-C counit identity to h, giving V'(epsilon_B) composed with bBC inverse and P_C(U'a).
2. Naturality of bBC at a moves P_C(U'a) past bBC inverse. Functoriality combines
V'(P_B(a)) and V'(epsilon_B) into V'(P_B(a) followed by epsilon_B).
3. Apply the A-to-B counit identity. Functoriality and the inverse-of-composite identity
produce the inverse of the two consecutive b maps, followed by V'V(epsilon_A).
Finally insert the canonical associators from det-sp-scalar-extension-functor (4).
Naturality of the C-counit moves the target associator through P_C G_C; naturality
of the scalar associator at epsilon_A then gives exactly the displayed conjugated
comparison inverse followed by the direct scalar extension of epsilon_A. These are
the three elementary proof steps of the node; det-sp-reduction-exceptional supplies
the adjunction and its transpose formula. No b cocycle is used.
-/
theorem reductionComposition_transpose
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (_hp : 0 < pchar) (_hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (_hf : j ≫ p = f)
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (_hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0)
    (φ : A →+* B) (ψ : B →+* C)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (hFC : ∀ M : spFiniteConstructibleTorCategory X C,
      spFiniteConstructibleTor Y C ((reductionCompactSupport C j p).obj M.obj))
    (hABX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hABY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hBCX : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor X C ((scalarExtensionFunctor ψ X).obj M.obj))
    (hBCY : ∀ K : spFiniteConstructibleTorCategory Y B,
      spFiniteConstructibleTor Y C ((scalarExtensionFunctor ψ Y).obj K.obj))
    (hACX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X C ((scalarExtensionFunctor (ψ.comp φ) X).obj M.obj))
    (hACY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y C ((scalarExtensionFunctor (ψ.comp φ) Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (GC : spFiniteConstructibleTorCategory Y C ⥤ spFiniteConstructibleTorCategory X C)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (adjC : reductionCtfCompactSupport C j p hFC ⊣ GC)
    (bAB : reductionCtfCompactSupport A j p hFA ⋙ reductionCtfScalar φ Y hABY ≅
      reductionCtfScalar φ X hABX ⋙ reductionCtfCompactSupport B j p hFB)
    (bBC : reductionCtfCompactSupport B j p hFB ⋙ reductionCtfScalar ψ Y hBCY ≅
      reductionCtfScalar ψ X hBCX ⋙ reductionCtfCompactSupport C j p hFC)
    (cAB : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionCtfScalar φ X hABX).obj (GA.obj K) ⟶
        GB.obj ((reductionCtfScalar φ Y hABY).obj K))
    (cBC : ∀ K : spFiniteConstructibleTorCategory Y B,
      (reductionCtfScalar ψ X hBCX).obj (GB.obj K) ⟶
        GC.obj ((reductionCtfScalar ψ Y hBCY).obj K))
    (hcAB : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionCtfCompactSupport B j p hFB).map (cAB K) ≫
          adjB.counit.app ((reductionCtfScalar φ Y hABY).obj K) =
        bAB.inv.app (GA.obj K) ≫ (reductionCtfScalar φ Y hABY).map (adjA.counit.app K))
    (hcBC : ∀ K : spFiniteConstructibleTorCategory Y B,
      (reductionCtfCompactSupport C j p hFC).map (cBC K) ≫
          adjC.counit.app ((reductionCtfScalar ψ Y hBCY).obj K) =
        bBC.inv.app (GB.obj K) ≫ (reductionCtfScalar ψ Y hBCY).map (adjB.counit.app K))
    (K : spFiniteConstructibleTorCategory Y A) :
    (adjC.homEquiv _ _).symm
        ((reductionCtfScalarCompositionIso φ ψ X hABX hBCX hACX (GA.obj K)).inv ≫
          (reductionCtfScalar ψ X hBCX).map (cAB K) ≫
          cBC ((reductionCtfScalar φ Y hABY).obj K) ≫
          GC.map (reductionCtfScalarCompositionIso φ ψ Y hABY hBCY hACY K).hom) =
      ((reductionCtfScalarCompositionIso φ ψ Y hABY hBCY hACY
          ((reductionCtfCompactSupport A j p hFA).obj (GA.obj K))).symm ≪≫
        (reductionCtfScalar ψ Y hBCY).mapIso (bAB.app (GA.obj K)) ≪≫
        bBC.app ((reductionCtfScalar φ X hABX).obj (GA.obj K)) ≪≫
        (reductionCtfCompactSupport C j p hFC).mapIso
          (reductionCtfScalarCompositionIso φ ψ X hABX hBCX hACX (GA.obj K))).inv ≫
        (reductionCtfScalar (ψ.comp φ) Y hACY).map (adjA.counit.app K) := by
  sorry

end AlgebraicGeometry.ProEtale
