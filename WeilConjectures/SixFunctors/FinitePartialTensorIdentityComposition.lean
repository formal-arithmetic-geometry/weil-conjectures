/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePartialPullbackTensor
import WeilConjectures.SixFunctors.FinitePartialTensorIdentityNaturality
import WeilConjectures.SixFunctors.FinitePartialTensorIdentityComponent

/-! # Composition of the finite partial tensor comparison at identity

Source: composition clause of lem-pur-derived-pullback-tensor-iso and the specified
finite pullback realization of def-fix-six-functor-datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Naturality and the twice-identity composition square for the explicit finite
partial tensor comparison. No identity unit is assumed or asserted.

Source: Stacks Project, sites-cohomology.tex, Tag 07A4,
lemma-pullback-tensor-product; composition clause of
lem-pur-derived-pullback-tensor-iso and the finite normalization clause of
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-finite-partial-tensor-identity-composition).

Proof: the prime-to-characteristic coefficient convention makes the coefficient
prime invertible on X. Write n = m + 1 using hn to match the canonical finite
comparison's indexing. Apply the full bounded-constructible inclusion, which is
faithful. Under
its coefficient equivalence, pullbackTensorComparison is the canonical fixed-scalar
pullback/tensor comparison conjugated by pullRealization and the two inverse
fixedPullRealization maps. Naturality of all these isomorphisms gives a natural
isomorphism in the two inputs; restriction of the second input is through the
full finite-Tor inclusion. For composition, substitute this conjugation into both
routes. Naturality moves the coefficient-equivalence units past the tensor and
pullback maps, and inverse identities cancel the adjacent units. The remaining
square is the finite composition equation of derivedPullbackTensorIso.
finitePullCompositionNormalization identifies its pullback compositors with c,
and the same equality under the full finite-Tor inclusion identifies d. Finally
transport identity composed with identity to identity using the equality maps
shown below. This proves the displayed composition square and the prescribed
component equation. The first input is never assumed to have finite Tor
amplitude; its tensor with the second input is bounded by domains. The argument
also applies to zero objects, empty schemes and n = 1. -/
theorem finitePartialTensor_identityComposition
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D) :
    let U := S.finite.pull (𝟙 X)
    let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
    let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
      eqToIso (congrArg (fun f ↦ (S.finite.pull f).obj M)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        (S.finite.pullComposition (𝟙 X) (𝟙 X)).app M
    let d : ∀ L, V.obj L ≅ V.obj (V.obj L) := fun L ↦
      eqToIso (congrArg (fun f ↦ (CompactSupportFiniteProjection.torPull S f).obj L)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        CompactSupportFiniteProjection.torPullComposition S (𝟙 X) (𝟙 X) L
    ∃ μ : T ⋙ U ≅ U.prod V ⋙ T,
      (∀ M L, μ.app (M, L) =
        CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L) ∧
      (∀ M L, μ.hom.app (M, L) ≫
          T.map (Prod.mkHom (c M).hom (d L).hom) =
        (c (T.obj (M, L))).hom ≫ U.map (μ.hom.app (M, L)) ≫
          μ.hom.app (U.obj M, V.obj L)) := by
  dsimp only
  let U := S.finite.pull (𝟙 X)
  let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
  let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
  let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
    eqToIso (congrArg (fun f ↦ (S.finite.pull f).obj M)
      (Category.id_comp (𝟙 X)).symm) ≪≫
      (S.finite.pullComposition (𝟙 X) (𝟙 X)).app M
  let d : ∀ L, V.obj L ≅ V.obj (V.obj L) := fun L ↦
    eqToIso (congrArg (fun f ↦ (CompactSupportFiniteProjection.torPull S f).obj L)
      (Category.id_comp (𝟙 X)).symm) ≪≫
      CompactSupportFiniteProjection.torPullComposition S (𝟙 X) (𝟙 X) L
  change ∃ μ : T ⋙ U ≅ U.prod V ⋙ T, _
  let μ : T ⋙ U ≅ U.prod V ⋙ T :=
    NatIso.ofComponents
      (fun ML ↦ (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X)
        ML.1 ML.2))
      (by
        intro ML ML' f
        exact finitePartialTensor_identityNaturality S X ML.1 ML'.1 ML.2 ML'.2 f.1 f.2)
  refine ⟨μ, ?_, ?_⟩
  · intro M L
    rfl
  · intro M L
    exact finitePartialTensor_identityComponent S X M L

end WeilConjectures
