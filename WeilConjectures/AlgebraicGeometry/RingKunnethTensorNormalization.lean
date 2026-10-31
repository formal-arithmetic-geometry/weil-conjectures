/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingKunnethNormalizationData
public import WeilConjectures.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-! # Tensor normalization of constant pullback from a separably closed point
Source: Stacks Tags 07A4 and 0F1E.
(blueprint: lem-sf-ring-kunneth-tensor-normalization).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
  {k : Type u} [Field k] [IsSepClosed k]

/-- Constant pullback intertwines the specified point, inverse-image, and constant tensors.
Source: Stacks Tags 07A4 and 0F1E.
(blueprint: lem-sf-ring-kunneth-tensor-normalization).

Proof: Before localization, the constant-presheaf tensor constraint has identity
components. Its sheafification followed by inverse image sends a local constant tensor
to the tensor of its two constant germs. The other route, inverse image of the tensor
followed by the two constant-pullback comparisons, has the same effect. The sheafification
universal property therefore gives equality of these natural transformations. This also
identifies the normalized constant-presheaf monoidal structure with the one used in the
point comparison, since both have identity unit and tensor components. On complexes the
equality holds on every pair of degrees and every coproduct summand of total tensor.
Choose flat-term K-flat representatives of P and Q. Exact constant sheaves preserve flat
objects, and constant-ring inverse image preserves K-flat complexes; hence all displayed
derived tensors are computed by these representatives. The equivalence comparison used
by ringKunnethPointTensorComparison is the localization of the same complex tensor map:
its chosen flat representative agrees with any such representative by naturality of the
localization comparison and cancellation of the resolution isomorphisms. Descend the
underived equality and transport left-derived constants to exact constants. The resulting
constant-pullback comparison is ringKunnethConstantComparison, and the two derived tensor
comparisons are precisely the displayed ones. This applies to arbitrary unbounded P,Q;
the zero and empty-scheme cases obey the same component identities. -/
theorem ringKunnethTensorNormalization
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (P Q : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    (ringKunnethConstantComparison Λ a).hom.app (P ⊗ Q) ≫
        (upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.map
          (ringKunnethPointTensorComparison Λ P Q) ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) a).app
          ((constantFunctor Λ (Spec (.of k))).obj P)).app
          ((constantFunctor Λ (Spec (.of k))).obj Q) =
      ((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).cachedDerivedTensorComparison.app P).app Q ≫
        ((ringKunnethConstantComparison Λ a).hom.app P ⊗ₘ
          (ringKunnethConstantComparison Λ a).hom.app Q) := by sorry

end AlgebraicGeometry.Etale
