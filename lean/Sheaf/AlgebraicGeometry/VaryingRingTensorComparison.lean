/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingOperations

/-! # Normalized tensor comparison for varying-ring inverse image

Source: Stacks Project, Tags 03EL, 0B56, 06YS, 06YU and 07A4.
(blueprint: lem-pur-varying-ring-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

/-- Exact inverse image has the tensor comparison determined by the ordinary
adjunction and the section-normalized lax tensor of its specified right adjoint.
This statement supplies only the tensor comparison for one map; it constructs
neither a family of geometric operations nor any extension-by-zero functor.

Source: Stacks Project, Tags 03EL, 0B56, 06YS, 06YU and 07A4; Zheng,
Construction 4.1 and Lemma 4.10.
(blueprint: lem-pur-varying-ring-tensor-comparison).

Proof: inverse image of the constant coefficient ring at each index identifies
with the same coefficient ring on the source. The usual inverse-image tensor
isomorphism is therefore available on module systems, with no condition on
horizontal ring transitions. Its adjunction transpose sends each local pure
tensor to the two unit sections followed by their tensor in direct image;
the section formula for t identifies this map with the displayed word.
Apply the inverse ordinary comparison on every bidegree tensor summand and
use coproduct preservation of the left adjoint to form the chain comparison.
Naturality verifies the two signed differentials and gives the summand
identity. Apply ringed-topos inverse-image preservation of K-flat complexes
with flat terms (Tag 0G7E) on this vertical site. Descend the chain
isomorphism on flat-term
K-flat representatives. The representative isomorphisms of TA and TB give
mu and the derived square in TensorComparisonModel. Uniqueness of adjoints
transports this construction to the supplied F and adj, with its actual unit,
so it applies to every universal presentation of the inverse-image functor. -/
theorem tensorComparison_exists
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Modules R φ X ⥤ Modules R φ Y) (hG : G = push R φ f)
    (F : Modules R φ Y ⥤ Modules R φ X) (adj : F ⊣ G)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (A : SemilinearSections.Closed.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (systemRing (Scheme.ProEt.topology Y) (coefficients R Y) (coefficientTransition R φ Y)))
    (B : SemilinearSections.Closed.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)))
    (TA : Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (systemRing (Scheme.ProEt.topology Y) (coefficients R Y) (coefficientTransition R φ Y)) A)
    (TB : Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)) B)
    (t : ∀ M N : Modules R φ X,
      ordinaryTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (systemRing (Scheme.ProEt.topology Y) (coefficients R Y) (coefficientTransition R φ Y))
        (G.obj M) (G.obj N) ⟶
      G.obj (ordinaryTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X))
        M N))
    (ht : ∀ (M N : Modules R φ X) (V : (ℕ × Y.ProEt)ᵒᵖ)
      (x : (G.obj M).val.obj V) (y : (G.obj N).val.obj V),
      cast (congrArg
        (fun H : Modules R φ X ⥤ Modules R φ Y ↦
          ((H.obj (ordinaryTensor.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology X))
            (systemRing (Scheme.ProEt.topology X) (coefficients R X)
              (coefficientTransition R φ X)) M N)).val.obj V : Type (u + 1))) hG)
      ((t M N).val.app V
        (tensorSection.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (systemRing (Scheme.ProEt.topology Y) (coefficients R Y)
            (coefficientTransition R φ Y))
          (G.obj M) (G.obj N) V x y)) =
      tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X))
        M N (((𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)).op.obj V)
        (cast (congrArg (fun H : Modules R φ X ⥤ Modules R φ Y ↦
          ((H.obj M).val.obj V : Type (u + 1))) hG) x)
        (cast (congrArg (fun H : Modules R φ X ⥤ Modules R φ Y ↦
          ((H.obj N).val.obj V : Type (u + 1))) hG) y)) :
    ∃ mu : A.tensor ⋙ F.mapDerivedCategory ≅
        (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor,
      ∃ model : TensorComparisonModel.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (systemRing (Scheme.ProEt.topology Y) (coefficients R Y) (coefficientTransition R φ Y))
        (systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X))
        F A B TA TB mu,
        ∀ M N : Modules R φ Y,
          adj.homEquiv _ _ (model.ordinary M N).hom =
            ordinaryTensorHom.{u + 1, u, u + 1}
              (coefficientSequenceTopology (Scheme.ProEt.topology Y))
              (systemRing (Scheme.ProEt.topology Y) (coefficients R Y)
                (coefficientTransition R φ Y))
              (adj.unit.app M) (adj.unit.app N) ≫ t (F.obj M) (F.obj N) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
