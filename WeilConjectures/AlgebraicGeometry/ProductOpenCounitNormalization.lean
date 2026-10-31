/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProductOpenTensorProjectionData

/-! # The supported open counit and its tensor normalization

Source: the first step of lem-pur-product-open-tensor-projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization WeilConjectures.FiniteOpenProduct
open WeilConjectures.ProductOpenTensorProjection

namespace WeilConjectures.ProductOpenTensorProjection

/-- Tensoring the open counit with an extended object is invertible, and the two
signed symmetries in rho give the same normalized open tensor map. The three
restriction comparisons use the actual open units, not chosen identifications.

Source: blueprint latest, sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md, symmetry paragraph; parent proof Step 1.
(blueprint: lem-pur-product-open-counit-normalization).

Proof: apply open tensor normalization to k. Gamma identifies the tensor with
first factor k_!P_kQ with k_!(P_kQ tensor P_k k_!N); the open unit identifies
P_k k_!N with N. The signed symmetry, gamma for N,Q, and extended symmetry
identify Q tensor k_!N with that same extension. The restriction of gamma is
its specified tensor-pullback comparison followed by the open unit. Naturality
of tensor pullback and the adjunction triangle identify the restriction of the
counit with the inverse unit at P_kQ. Restricting rho cancels the two signed
symmetries, including odd cochain degrees. Thus the two maps from the first
supported tensor to k_!(P_kQ tensor N) agree after restriction. Full faithfulness
of extension, transported along these isomorphisms, proves their equality.
Both maps are isomorphisms, so their quotient, the tensored counit, is too.
The argument applies also to the empty open and zero objects: the supported
objects are zero and every displayed identity is the identity on zero. -/
theorem productOpenCounitNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U Y : Scheme.{u}} (k : U ⟶ Y) [IsOpenImmersion k]
    (Q : FiniteD A Y) (N : FiniteD A U) :
    let J := (finiteShriek A k).obj N
    let T := tensor A U ((pull A k).obj Q) N
    let η := tensorMap A Y ((adj A k).counit.app Q) (𝟙 J)
    let δ := gamma A k ((pull A k).obj Q) J ≫
      (finiteShriek A k).map (tensorMap A U (𝟙 _) (openUnit A k N).inv)
    let rν := tensorPullIso A k Q J ≪≫
      tensorIsoMap A U (Iso.refl _) (openUnit A k N).symm
    let rη := tensorPullIso A k ((finiteShriek A k).obj ((pull A k).obj Q)) J ≪≫
      tensorIsoMap A U (openUnit A k ((pull A k).obj Q)).symm (openUnit A k N).symm
    IsIso η ∧ η ≫ rho A k Q N = δ ∧
      (pull A k).map η ≫ rν.hom = rη.hom ∧
      (pull A k).map (rho A k Q N) ≫ (openUnit A k T).inv = rν.hom ∧
      Nonempty (tensor A Y ((finiteShriek A k).obj ((pull A k).obj Q)) J ≅
        (finiteShriek A k).obj T) ∧
      Nonempty (tensor A Y Q J ≅ (finiteShriek A k).obj T) := by sorry

end WeilConjectures.ProductOpenTensorProjection
