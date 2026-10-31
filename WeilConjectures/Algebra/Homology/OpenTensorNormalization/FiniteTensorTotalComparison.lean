/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorOrdinaryComparison
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorTotalOfOrdinary

/-! # Pinned tensor transport for finite realizations

Source: Stacks 03EK, 0A5J and 012Z.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- The section-normalized realization comparison on signed total tensor complexes.

Source: Stacks, Modules on Sites, Tag 03EK, and Homology, Tags 0A5J and 012Z.
(blueprint: lem-sf-finite-tensor-total-comparison).

Proof: for fixed-coefficient sheaves M,N and an R-module sheaf H, the underlying
comparison identifies pairings into H with A-bilinear pairings into its underlying
sheaf. An A-bilinear pairing compatible with restriction is R-bilinear: for a
section r of R, cover by the image sieve of i at r. On each member r lifts to a
constant a, so the scalar equations for e and its inverse give the required
R-linearity. Separatedness gives it before restriction. Apply this in both variables.
The universal properties of the sheafified fixed-coefficient tensor and the ringed
tensor consequently give a natural isomorphism e(M tensor N) to e(M) tensor e(N),
carrying each pure tensor to the pure tensor of the two underlying inverse images.
Both composites are identities because they agree on all pure pairs after the
sheafification units. This argument applies to the prescribed e, without choosing a
new realization or replacing the literal coefficient ring R by a constant ring.

Apply the ordinary comparison in every bidegree. The realization equivalence
preserves the coproducts indexed by p+q=n, so the coproduct universal property gives
the comparison in degree n. Naturality of the ordinary tensor comparison makes it
commute with the first differential and the second differential. Additivity of e
preserves multiplication by (-1)^p in the second differential. These degree maps
therefore form a chain isomorphism, natural in both input complexes. On every
coproduct injection it equals the ordinary comparison followed by the target
injection. Apply the naturality of e.underlying.inv to that injection and then the
ordinary pure-pair equation to obtain exactly finiteTensorPure. -/
theorem finite_tensor_total_comparison_exists
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallySurjective (ProEt.topology X) i]
    (e : FiniteRealization A X R i) :
    ∃ s : Functor.uncurry.obj
        ((curriedTensor (FiniteModules A X)).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ finiteComplexRealization e ≅
      ((finiteComplexRealization e).prod (finiteComplexRealization e)) ⋙ total R,
      finiteTensorPure e (fun P Q ↦ s.app (P, Q)) := by
  obtain ⟨c, ⟨hc, hp⟩⟩ := finite_tensor_ordinary_comparison_exists A X R i e
  exact finite_tensor_total_of_ordinary A X R i e c hc hp

end SheafOfModules.OpenTensorNormalization
