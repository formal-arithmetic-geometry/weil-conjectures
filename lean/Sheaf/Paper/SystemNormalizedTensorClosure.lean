/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Paper.SystemTensorReductionFormula

/-!
# Tensor and inverse image preserve normalized semilinear systems

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 06YS, applied to the
strict-system consequence in the proof of `prop-pur-adic-reconstruction-trace-coherence`
(blueprint: lem-pur-system-normalized-tensor-closure).

All reductions below are the adjoints of the actual horizontal system transitions.
The comparison maps are the representative-normalized comparisons of the simultaneous
semilinear-section calculus. No boundedness or flatness hypothesis is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- Tensor closure, its actual reduction formula, and the quotient cocycle.
Source: Stacks 07A4 and 06YS; strict-system consequence in the normalized-system operations
of `prop-pur-adic-reconstruction-trace-coherence`
(blueprint: lem-pur-system-normalized-tensor-closure).
Proof: apply the actual tensor-reduction identity `tensor_reduction_formula`, proved
by the ordinary pure-section adjunction calculation, the total cochain tensor
summands, and the representative-normalized derived comparison squares. The two
original reductions are invertible by normalization. The scalar tensor and evaluation
comparisons are isomorphisms, so cancellation proves that the tensor reduction is
invertible. Retain the actual tensor-reduction identity as the second conjunct.
The quotient cocycle is the simultaneous calculus's reduction_cocycle field applied
to the tensor system. K-flat resolutions with flat terms and the total tensor model
apply to unbounded complexes without flat coefficient transitions. -/
theorem normalized_tensor_closure (A : Data.{c, v, r} J B τ)
    (P Q : DS.{c, v, max c v r} J B τ)
    (hP : Normalized.{c, v, max c v r} J B τ A.scalar P)
    (hQ : Normalized.{c, v, max c v r} J B τ A.scalar Q) :
    Normalized.{c, v, max c v r} J B τ A.scalar (A.closed.tensor.obj (P, Q)) ∧
    (∀ {m n : ℕ} (h : n ≤ m),
      reduction.{c, v, max c v r} J B τ h (A.scalar h) (A.closed.tensor.obj (P, Q)) ≫
          (A.tensorEvaluation n).hom.app (P, Q) =
        (A.scalar h).T.map ((A.tensorEvaluation m).hom.app (P, Q)) ≫
          (A.scalarTensor h).hom.app
            ((e.{c, v, max c v r} J B τ m).obj P, (e.{c, v, max c v r} J B τ m).obj Q) ≫
          (A.levelClosed n).tensor.map
            (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (A.scalar h) P)
              (reduction.{c, v, max c v r} J B τ h (A.scalar h) Q))) ∧
    (∀ {l m n : ℕ} (h : n ≤ m) (k : m ≤ l),
      (A.scalar h).T.map
          (reduction.{c, v, max c v r} J B τ k (A.scalar k)
            (A.closed.tensor.obj (P, Q))) ≫
          reduction.{c, v, max c v r} J B τ h (A.scalar h) (A.closed.tensor.obj (P, Q)) =
        (A.scalarComposition h k).hom.app
            ((e.{c, v, max c v r} J B τ l).obj (A.closed.tensor.obj (P, Q))) ≫
          reduction.{c, v, max c v r} J B τ (h.trans k) (A.scalar (h.trans k))
            (A.closed.tensor.obj (P, Q))) := by
  refine ⟨?_, (fun h ↦ tensor_reduction_formula J B τ A P Q h), ?_⟩
  · intro m n h
    have := hP h
    have := hQ h
    have : IsIso (Prod.mkHom
        (reduction J B τ h (A.scalar h) P) (reduction J B τ h (A.scalar h) Q)) :=
      (isIso_prod_iff _ _).mpr ⟨hP h, hQ h⟩
    exact IsIso.of_isIso_fac_right (tensor_reduction_formula J B τ A P Q h)
  · intro l m n h k
    exact A.reduction_cocycle h k (A.closed.tensor.obj (P, Q))

section InverseImage

variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv]

/-- An accessor for the inverse-image model already supplied by the simultaneous calculus.
Its coefficients and transitions are the inverse images of B and tau; no new choice is made.
Source: lem-coef-semilinear-derived-sections; Stacks 07A4
(blueprint: lem-pur-system-normalized-tensor-closure). -/
abbrev SemilinearDerivedSectionsData.inverseImageGeometry
    (A : SemilinearDerivedSectionsData.{c, v, r} J B τ) :
    Geometry.{c, v, r} J B τ A.systems J' uInv uPush adjSet :=
  (A.geometric J' uInv uPush adjSet).val

end InverseImage

section InverseImageClosure

variable (A : SemilinearDerivedSectionsData.{c, v, r} J B τ)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv]

/-- Inverse-image closure together with the actual transition formula and quotient cocycle.
Source: Stacks 07A4 and 06YS; normalized-system operations of
`prop-pur-adic-reconstruction-trace-coherence`
(blueprint: lem-pur-system-normalized-tensor-closure).
Proof: take the inverse-image section model of lem-coef-semilinear-derived-sections.
Its PullTransitionFormula identifies the actual reduction, under pull evaluation,
with inverse image of the original reduction after the inverse coefficient-pullback
comparison. The comparison is canonical: its scalar-adjunction transpose is the
identity-on-underlying-sheaves restriction comparison, as fixed in that model.
Tag 07A4 gives the same comparison on K-flat representatives. Inverse image preserves
isomorphisms, so normalization of P makes each such composite invertible. Cancel the
pull evaluation isomorphism to obtain normalization of the inverse-image system.
Naturality of coefficient pullback and the original reduction cocycle give the target
quotient cocycle, also recorded by target.reduction_cocycle. K-flat resolutions exist
for arbitrary unbounded complexes by 06YS; lem-pur-derived-change-of-rings imposes no
flatness hypothesis on coefficient maps. -/
theorem normalized_inverseImage_closure
    (P : DS.{c, v, max c v r} J B τ)
    (hP : Normalized.{c, v, max c v r} J B τ A.systems.scalar P) :
    Normalized.{c, v, max c v r} J'
      (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficients
      (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficientTransition
      (A.inverseImageGeometry J B τ J' uInv uPush adjSet).target.scalar
      ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).pull.mapDerivedCategory.obj P) ∧
    (∀ {m n : ℕ} (h : n ≤ m),
      reduction.{c, v, max c v r} J'
          (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficients
          (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficientTransition h
          ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).target.scalar h)
          ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).pull.mapDerivedCategory.obj P) ≫
          ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).pullEvaluation n).hom.app P =
        ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).target.scalar h).T.map
            (((A.inverseImageGeometry J B τ J' uInv uPush adjSet).pullEvaluation m).hom.app P) ≫
          ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficientPullback h).inv.app
            ((e.{c, v, max c v r} J B τ m).obj P) ≫
          (derivedExact.{c, v, max c v r, c, v} J J' (B n)
            ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficients n)
            ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).inverseImage n).modules).map
              (reduction.{c, v, max c v r} J B τ h (A.systems.scalar h) P)) ∧
    (∀ {l m n : ℕ} (h : n ≤ m) (k : m ≤ l),
      ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).target.scalar h).T.map
          (reduction.{c, v, max c v r} J'
            (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficients
            (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficientTransition k
            ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).target.scalar k)
            ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).pull.mapDerivedCategory.obj P)) ≫
          reduction.{c, v, max c v r} J'
            (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficients
            (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficientTransition h
            ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).target.scalar h)
            ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).pull.mapDerivedCategory.obj P) =
        ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).target.scalarComposition h k).hom.app
            ((e.{c, v, max c v r} J'
              (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficients
              (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficientTransition l).obj
              ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).pull.mapDerivedCategory.obj P)) ≫
          reduction.{c, v, max c v r} J'
            (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficients
            (A.inverseImageGeometry J B τ J' uInv uPush adjSet).coefficientTransition (h.trans k)
            ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).target.scalar (h.trans k))
            ((A.inverseImageGeometry J B τ J' uInv uPush adjSet).pull.mapDerivedCategory.obj P))
    := by
  let G := A.inverseImageGeometry J B τ J' uInv uPush adjSet
  have hpull : G.PullTransitionFormula J B τ A.systems J' uInv uPush adjSet :=
    (A.geometric J' uInv uPush adjSet).property.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro m n h
    have := hP h
    exact IsIso.of_isIso_fac_right (hpull h P)
  · intro m n h
    exact hpull h P
  · intro l m n h k
    exact G.target.reduction_cocycle h k (G.pull.mapDerivedCategory.obj P)

end InverseImageClosure
end WeilConjectures.SemilinearSections
