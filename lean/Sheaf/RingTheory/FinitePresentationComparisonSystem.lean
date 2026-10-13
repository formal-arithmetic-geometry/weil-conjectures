/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Descending a comparison map and its filtered pushout system -/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- The comparison descends as a finitely presented ring map, in a filtered system
of pushout squares. No stage map is asserted to be bijective.

Source: Stacks Project, Algebra, Tag 02JO (3), construction of the comparison map;
Tags 00QO and 05N9 (2); tensor base change and cancellation.
(blueprint: lem-weil-pbc-finite-presentation-comparison-system)

Proof: work in the cofinal upper set of i₀. The systems Aⱼ tensor B₀ and Aⱼ tensor
C₀ have the indicated tensor colimits: representatives and eventual equality are
provided by the elementwise base-change lemma. Define the universal ring map
on representatives; eventual equality makes it well defined, and ring operations
are checked at common upper bounds. Finite presentation of P over Z
factors P into one B stage. After restricting to the upper set of that stage,
transport this structure by transition maps. Composing e with the inclusion of Q
makes Q a P-algebra map into the limit C ring. Finite presentation of Q over P
factors this map into a later C stage as a P-algebra map, so compatibility with P
holds already at that stage. Restrict again
and denote the starting index by i. For j above i, give Cⱼ its P-structure through
Bⱼ and the base change of φ₀, and extend the Q map by transition maps.
The tensor universal property gives ψⱼ : Bⱼ tensor_P Q → Cⱼ, sending b tensor q
to φⱼ(b) times the chosen image of q. This proves its left-inclusion compatibility.
These maps commute with transitions by checking pure tensors. Tensor cancellation
shows each transition square of ψ is a pushout: both sides at a later index are
base changes along Bⱼ → Bₖ. The target Cⱼ is finitely presented over Bⱼ by base
change of φ₀; the source is finitely presented over Bⱼ by base change of P → Q.
The finite-type cancellation theorem therefore makes ψⱼ finitely presented.
Tensor products commute with the filtered colimit, so the source has colimit
B tensor_P Q and the target has colimit C. Their colimit comparison is e,
hence bijective. Lift rings to the common universe if necessary and record the
canonical ring equivalences dⱼ and cⱼ; these change none of the identities.
Only the comparison maps, not their inverses, have been descended in this step.
The construction works for zero rings and empty presentations.
-/
theorem exists_finitePresentation_comparison_system
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hfp : φ₀.toRingHom.FinitePresentation)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (e : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (he : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      e.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom) :
    ∃ (i : I) (hi : i₀ ≤ i),
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
                ∃ (_hD : IsColimit cD) (_hE : IsColimit cE), IsFiltered J ∧
                (∀ j, α.app j ≫ cE.ι.app j = cD.ι.app j ≫ f) ∧
                Function.Bijective f ∧
                (∀ j, (α.app j).hom.FinitePresentation) ∧
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
