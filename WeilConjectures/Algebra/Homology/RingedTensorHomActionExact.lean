/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorHomActionDefinitions
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactUniverses
public import WeilConjectures.Algebra.Homology.DerivedTensorShiftDescent
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Algebra.Homology.RingedTensorHomActionShiftWitness
import WeilConjectures.Algebra.Homology.RingedTensorHomActionLaws
import WeilConjectures.Algebra.Homology.RingedTensorHomActionCoefficientNaturality
import WeilConjectures.Algebra.Homology.RingedTensorHomActionUnit
import WeilConjectures.Algebra.Homology.RingedTensorHomActionHomNaturality

/-! # Exactness of the canonical derived tensor-Hom action

Source: Stacks 0BYU, with the coefficient exactness enhancement.
(blueprint: lem-sf-tensor-hom-action-exact).
The triangle morphism is constructed from naturality and the coefficient-shift square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe a b c v u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite WeilConjectures

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- The action laws induce the specified morphism of distinguished triangles.
Source: Stacks 0BYU (blueprint: lem-sf-tensor-hom-action-exact). -/
theorem ringed_tensor_hom_action_spec_of_shift
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (s : ∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
      (tensorHomActionSource S V).CommShift ℤ)
    (hs : tensorHomActionShiftNormalization J R S T β hc s) :
    tensorHomActionExactSpec J R S β s := by
  let (V : DerivedCategory (RingedTensorModules.{c, v, u} J R)) := s V
  obtain ⟨hF, hG, hshift⟩ : tensorHomActionExactCore J R S β s :=
    ringed_tensor_hom_action_laws_of_shift J R S T β hc s hs
  have hnatFixed := tensorHomAction_hom_naturality S β
  have hnat (K K' L L' A A' : DerivedCategory (RingedTensorModules.{c, v, u} J R))
      (k : K' ⟶ K) (l : L ⟶ L') (f : A ⟶ A') :
      S.tensor.map ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map (k.op, l), f) ≫
          tensorHomAction S β K' L' A' =
        tensorHomAction S β K L A ≫
          (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
            (k.op, S.tensor.map (l, f)) := by
    let H := derivedInternalHomOfUniverses.{c, v, u, w} J R
    have ht : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom k.op l)) f) =
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom k.op l)) (𝟙 A)) ≫
          S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K', L'))) f) := by
      rw [← S.tensor.map_comp]
      congr 1
      ext <;> simp
    rw [ht, Category.assoc, tensorHomAction_coefficient_naturality,
      ← Category.assoc, hnatFixed, Category.assoc, ← H.map_comp]
    congr 1
    apply H.congr_map
    ext
    · simp
    · dsimp
      rw [← S.tensor.map_comp]
      congr 1
      ext <;> simp
  refine ⟨hF, hG, hnat, hshift, ?_, tensorHomAction_unit S β⟩
  intro K L Δ hΔ
  let F := tensorHomActionSource S
    ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L))
  let G := tensorHomActionTarget S K L
  let : F.IsTriangulated := hF _
  let : G.IsTriangulated := hG K L
  have hn (A A' : DerivedCategory (RingedTensorModules.{c, v, u} J R)) (f : A ⟶ A') :
      F.map f ≫ tensorHomAction S β K L A' = tensorHomAction S β K L A ≫ G.map f := by
    have h := hnat K K L L A A' (𝟙 K) (𝟙 L) f
    have hi : (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
        (Prod.mkHom (𝟙 K).op (𝟙 L)) =
        𝟙 ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L)) :=
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).map_id (op K, L)
    rw [hi] at h
    exact h
  refine ⟨F.map_distinguished Δ hΔ, G.map_distinguished Δ hΔ, ?_⟩
  refine ⟨{ hom₁ := tensorHomAction S β K L Δ.obj₁
            hom₂ := tensorHomAction S β K L Δ.obj₂
            hom₃ := tensorHomAction S β K L Δ.obj₃
            comm₁ := hn _ _ Δ.mor₁
            comm₂ := hn _ _ Δ.mor₂
            comm₃ := ?_ }, rfl, rfl, rfl⟩
  change (F.map Δ.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app Δ.obj₁) ≫
      (tensorHomAction S β K L Δ.obj₁)⟦(1 : ℤ)⟧' =
    tensorHomAction S β K L Δ.obj₃ ≫
      (G.map Δ.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app Δ.obj₁)
  rw [Category.assoc, ← hshift K L Δ.obj₁ (1 : ℤ), ← Category.assoc,
    hn _ _ Δ.mor₃, Category.assoc]

/-- The canonical derived tensor-Hom action is exact in its coefficient argument.
Source: Stacks Project, sites-cohomology.tex, Tag 0BYU, and the agent-formulated exactness
and unit enhancement (blueprint: lem-sf-tensor-hom-action-exact).

Proof plan:
1. Resolve every fixed tensor factor by flat-term K-flats (lem-pc-kflat-resolution).
   Apply lem-weil-pbc-kflat-fixed-tensor-triangulated, identify its canonical shifts by
   lem-weil-pbc-derived-tensor-shift-descent, and compose with the normalized exact Hom
   functor of lem-weil-pbc-ringed-internal-hom-exact-universes.
2. Uncurry the naturality squares in K, L and A. Naturality of evaluation, associativity
   and symmetry in lem-sf-ringed-derived-closed-symmetric-monoidal gives all three.
3. On total K-flat representatives the exchange has sign (-1)^(q*r); extracting the
   coefficient shift gives exponent n*(p+r). Extracting it first and then exchanging
   gives n*p+(q+n)*r, the same exponent. Use lem-pur-total-tensor-signed-coherence,
   lem-sf-ringed-derived-native-tensor and lem-weil-pbc-derived-tensor-shift-descent.
   Naturality in evaluation and lem-weil-pbc-site-derived-tensor-descent extend this
   tensor-constraint equality to all derived maps.
4. Apply the adjunction to the shift square. The normalized target-Hom evaluation
   equation of lem-sf-ringed-hom-target-shift-evaluation identifies its two uncurries
   with the equality in step 3; injectivity of transposition proves the square.
5. Naturality for each triangle arrow gives the first two squares. For its last arrow,
   compose naturality with the target shift and substitute step 4. These are exactly
   the connecting arrows of the two image triangles, giving the specified morphism.
6. At the tensor unit, unit and symmetry coherence reduce the uncurried action to
   evaluation. The identity has the same uncurry, so transposition identifies them.
No action map is asserted invertible; no boundedness or finiteness is required. -/
theorem ringed_tensor_hom_action_exact
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β) :
    ∃ s : ∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
      (tensorHomActionSource S V).CommShift ℤ,
      tensorHomActionShiftNormalization J R S T β hc s ∧ tensorHomActionExactSpec J R S β s := by
  obtain ⟨s, hs⟩ := ringed_tensor_hom_action_shift_witness J R S T β hc
  exact ⟨s, hs, ringed_tensor_hom_action_spec_of_shift J R S T β hc s hs⟩

end CategoryTheory
