/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Extension.ExtendScalars
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Residue-field differential injectivity in positive characteristic

Source: Stacks Project, More on Algebra, Proposition Tag 07E5, proof of (3) ⇔ (4)
(blueprint: lem-weil-pbc-h1-injective-differentials-injective-char-p).
-/

universe u v

open scoped TensorProduct

namespace Algebra

/-- For a Noetherian local `k`-algebra in positive characteristic, injectivity of the
canonical map from first cotangent homology to the maximal ideal's conormal module
implies injectivity of the residue-field base change of the map on prime-field differentials.
Tensor factors are reversed from the source by the canonical tensor commutativity isomorphisms.

Source: Stacks Project, More on Algebra, Proposition Tag 07E5, proof of (3) ⇔ (4).
Proof:
1. The Jacobi–Zariski sequence for `𝔽_p → k → K` is exact at `K ⊗[k] Ω[k⁄𝔽_p]`:
   the kernel of its map to `Ω[K⁄𝔽_p]` is the image of the connecting map from
   `H1Cotangent k K` (lem-weil-pbc-jacobi-zariski-homology-sequence).
2. The sequence for `𝔽_p → A → K` has injective connecting map from `H1Cotangent A K`,
   because `H1Cotangent 𝔽_p K` vanishes (lem-weil-pbc-field-char-p-h1-cotangent-vanishing).
   Under the surjection isomorphism (lem-weil-pbc-jacobi-zariski-surjection-h1), this is
   the injective map `δ : m/m² → K ⊗[A] Ω[A⁄𝔽_p]`; the identification follows from
   lem-weil-pbc-jacobi-zariski-connecting-map-naturality.
3. Connecting-map naturality and presentation functoriality
   (lem-weil-pbc-nl-presentation-h1-functoriality) give `δ ∘ γ = λ ∘ ∂`.
4. The maps to `Ω[K⁄𝔽_p]` commute with `λ`, as checked on `x ⊗ da` using
   the universal derivation (def-weil-pbc-kahler-differentials).
5. If `λ(x) = 0`, step 4 and step 1 give `x = ∂(h)`. Step 3 gives `δ(γ(h)) = 0`.
   Injectivity of `δ`, then the assumed injectivity of `γ`, gives `h = 0`, hence `x = 0`.

(blueprint: lem-weil-pbc-h1-injective-differentials-injective-char-p) -/
theorem differentials_injective_of_h1Cotangent_injective_charP
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP k p] :
    letI := ZMod.algebra k p
    letI := ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
    let K := IsLocalRing.ResidueField A
    let P := Extension.ofSurjective (Algebra.ofId A K) IsLocalRing.residue_surjective
    let γ := P.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k A K K)
    let lambdaMap := (TensorProduct.isBaseChange k Ω[k⁄ZMod p] K).lift
      (((TensorProduct.mk A K Ω[A⁄ZMod p] 1).restrictScalars k).comp
        (KaehlerDifferential.map (ZMod p) (ZMod p) k A))
    Function.Injective γ → Function.Injective lambdaMap := by
  sorry

end Algebra
