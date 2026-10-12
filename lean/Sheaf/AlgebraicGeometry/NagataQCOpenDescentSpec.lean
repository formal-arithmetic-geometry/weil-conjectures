/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.NagataQCOpenDescent
import Sheaf.Order.DirectedFiniteUpperBound

/-!
# Properties of the descended quasi-compact open

Source: blueprint, sec-nagata-compactification, sk-prop-nagata-sketch-approximation,
node order 348 (blueprint: lemma-nagata-qc-open-descends).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The selected finite-stage open is quasi-compact and pulls back to the original open.
Source: blueprint node order 348 (blueprint: lemma-nagata-qc-open-descends).

Proof: By `def-nagata-qc-open-descent`, the selected open is a finite union of basic opens
inside the inverse images of the affine charts. These inverse images are affine because
the transition to the base stage is affine, by base change (Stacks Tag 01SD). Each basic
open of an affine chart is quasi-compact (Tag 00E8), as is their finite union.
By `lemma-nagata-directed-finite-upper-bound`, every chosen chart stage is below the
selected common stage. Transporting its lifted sections to this stage and pulling them
back to the limit recovers the original sections: the colimit maps of
`lem-weil-pbc-limit-global-sections-colimit` are exactly the projection pullbacks.
By `lem-weil-pbc-basic-open-pullback`, the inverse image of each transported basic open
is its original basic open. Inverse image commutes with unions, and the chosen
presentations therefore recover the union of `W` intersected with the limit charts.
The charts cover the limit, since they are inverse images of a cover of the base stage,
so this last union is exactly `W`. -/
theorem nagataQCOpenDescent_spec
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) {Y₀ : Scheme.{u}} (p : Y₀ ⟶ D.obj (op i₀))
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (W : (baseChangeCone D c p).pt.Opens)
    (hW : IsCompact (W : Set (baseChangeCone D c p).pt))
    (m : ℕ) (U : Fin m → Y₀.Opens) (hU : ∀ a, IsAffineOpen (U a))
    (hcover : iSup U = ⊤) (r : Fin m → ℕ)
    (f : ∀ a, Fin (r a) → Γ((baseChangeCone D c p).pt,
      pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ U a))
    (hpresentation : ∀ a, W ⊓ (pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ U a) =
      ⨆ k, (baseChangeCone D c p).pt.basicOpen (f a k))
    (stage : Fin m → I) (ha : ∀ a, i₀ ≤ stage a)
    (lift : ∀ a, Fin (r a) →
      Γ((baseChangeDiagram D p).obj (Over.mk (homOfLE (ha a)).op),
        pullback.fst p (D.map (homOfLE (ha a)).op) ⁻¹ᵁ U a))
    (hlift : ∀ a k,
      ((baseChangeCone D c p).π.app (Over.mk (homOfLE (ha a)).op)).appLE
        (pullback.fst p (D.map (homOfLE (ha a)).op) ⁻¹ᵁ U a)
        (pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ U a)
        (nagataQCOpenDescent_limit_chart_le D c p
          (Over.mk (homOfLE (ha a)).op) (U a)) (lift a k) = f a k)
    (d : I → I → I) (hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j)
    (order : LinearOrder I) :
    IsCompact ((nagataQCOpenDescent D c hc i₀ p W hW m U hU hcover r f hpresentation
        stage ha lift hlift d hd order).2.2.carrier) ∧
      (baseChangeCone D c p).π.app
          (Over.mk (homOfLE
            (nagataQCOpenDescent D c hc i₀ p W hW m U hU hcover r f hpresentation
              stage ha lift hlift d hd order).2.1).op) ⁻¹ᵁ
        (nagataQCOpenDescent D c hc i₀ p W hW m U hU hcover r f hpresentation
        stage ha lift hlift d hd order).2.2 = W := by
  sorry

end AlgebraicGeometry
