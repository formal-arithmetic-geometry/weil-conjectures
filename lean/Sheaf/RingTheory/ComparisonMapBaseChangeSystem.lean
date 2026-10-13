/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.Paper.DirectedColimitBaseChangeElementwise

/-! # Extending a tensor comparison by base change

Source: Stacks Project, Algebra, Tags 02JO (3) and 00DD.
(blueprint: lem-weil-pbc-comparison-map-base-change-system)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- Extend a single comparison map by base change to a pushout system with its colimits.

Source: Stacks Project, Algebra, Tag 02JO (3), the displayed maps Ψ and their
colimit; tensor universal properties and Tag 00DD.
(blueprint: lem-weil-pbc-comparison-map-base-change-system)

Proof: for j ≥ i, transport the P-structure of Bᵢ to Bⱼ by the tensor transition
map. Define Dⱼ as the common-universe ULift of Bⱼ tensor_P Q and Eⱼ as the ULift
of Cⱼ. Define their transitions by tensor maps. Tensor cancellation identifies
Bⱼ with F(j) tensor_{F(i)} Bᵢ and Cⱼ with F(j) tensor_{F(i)} Cᵢ.
Base change ψ along F(i) → F(j), and use these cancellation equivalences to
obtain αⱼ. The identity hψ makes ψ F(i)-linear, and also proves left-inclusion
compatibility after base change. Checking the B and Q inclusions proves
naturality. Explicitly, if qᵢ(q) = ψ(1 tensor q), the component on pure
tensors is b tensor q ↦ φⱼ(b) · τⱼᵢ(qᵢ(q)), where τ is the C transition.
The transported P-structure makes this balanced. For j → k, both source
and target at k are obtained from their
values at j by tensoring with Bₖ over Bⱼ; tensor associativity therefore proves
the transition square is a pushout. These identifications also define the
canonical d and c after the ULift conjugations.
The B and C tensor diagrams have their limit tensor rings as colimits, by the
elementwise representative and eventual-equality lemma. A compatible family
of maps from Dⱼ is exactly a compatible family of maps from Bⱼ and a map from
Q agreeing on P. Thus its colimit is B tensor_P Q. Construct cD and cE using
these universal properties and lift their points to the common universe.
Their comparison is the conjugate of e: hμB and hlim identify the stage maps,
and tensor extensionality proves this identity at the limit. Consequently f
is bijective. This construction uses no finite-presentation assumptions and
works for arbitrary Q and φ₀, including zero rings.
-/
theorem exists_comparison_map_base_change_system
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (e : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (i : I) (hi : i₀ ≤ i)
    (aPi : letI := (F.map (homOfLE hi)).hom.toAlgebra
      Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀))
    (μB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      μB.toRingHom =
        (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom)
    (ψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ((↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q) →+* (↥(F.obj i) ⊗[F.obj i₀] C₀))
    (hψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ψ.comp (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom)
    (hlim : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp ψ =
        e.toRingHom.comp (Algebra.TensorProduct.map μB (AlgHom.id P Q)).toRingHom) :
      let J := {j : I // i ≤ j}
      ∃ (aPs : ∀ j : J,
          letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
        ∃ (D E : J ⥤ CommRingCat.{max v w x y}) (α : D ⟶ E),
          ∃ (d : ∀ j : J,
              letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
              letI := aPs j
              ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q),
            ∃ (c : ∀ j : J,
                letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀)),
              ∃ (cD : Cocone D) (cE : Cocone E) (f : cD.pt ⟶ cE.pt),
                ∃ (_hD : IsColimit cD) (_hE : IsColimit cE),
                (∀ j, α.app j ≫ cE.ι.app j = cD.ι.app j ≫ f) ∧
                Function.Bijective f ∧
                (∀ {j k} (r : j ⟶ k), IsPushout (α.app j) (D.map r)
                  (E.map r) (α.app k)) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                  letI := aPs j
                  ((c j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)).comp
                    (Algebra.TensorProduct.includeLeftRingHom (R := P)
                      (A := ↥(F.obj j.val) ⊗[F.obj i₀] B₀) (B := Q)) =
                    (Algebra.TensorProduct.map (Algebra.ofId (F.obj j.val) (F.obj j.val))
                      φ₀).toRingHom) := by sorry

end RingHom
