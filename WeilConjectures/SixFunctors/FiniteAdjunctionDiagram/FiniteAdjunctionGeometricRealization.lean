/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagram.FiniteAdjunctionDiagramData

/-! The geometric part of the finite exceptional system construction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
variable {l E D hl f c}

variable (l E D hl f c)

variable (SX : CoefficientDerivedSystemCalculus l E X)
  (SZ : CoefficientDerivedSystemCalculus l E c.Z)
  (SY : CoefficientDerivedSystemCalculus l E Y)
  (SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k)))
/-- Construct the geometric system operations and their absolute dualizing objects.
This step asserts neither the dual-formula isomorphism nor enriched adjunction.
Source: realization node steps 1--9; Zheng Construction 5.15 and Lemmas 5.16, 5.22;
Stacks 079P, 06YS and 0941
(blueprint: lem-sf-finite-adjunction-geometric-realization).
Proof: form exact open extension and proper derived image on strict etale
coefficient systems. The finite proper image preserves coproducts, so Brown
representability gives its system right adjoint. Evaluation left extensions and
the proper/open projection comparisons identify its evaluated adjoints and
counits with the prescribed finite adjunctions. Their quotient mates identify
the transitions. Transport through the etale/pro-etale equivalence on systems
with etale-origin levels. Finite preservation and invertible quotient mates
restrict both functors to the normalized levelwise finite-Tor categories.
The system adjunction restricts with its unit and counit. The ordinary section
identity and its derived comparison give SectionsPush for the geometric image.
Apply the same construction to the two structure maps, using Nagata
compactifications and the actual normalized regular unit. The finite dualizing
comparisons and the normalized tower Roos triangle give DualizingSpec with
its original finite projections. Finally reduction, support, and total limit
identify the existing integral compact-support functor, and the scalar units
identify all its projections. Resolution-normalized uniqueness transports
these constructions to the supplied coherent calculus models. -/
theorem finiteAdjunctionGeometricRealization
    (hX : CoefficientDerivedSystemCoherence l E X SX)
    (hZ : CoefficientDerivedSystemCoherence l E c.Z SZ)
    (hY : CoefficientDerivedSystemCoherence l E Y SY)
    (hS : CoefficientDerivedSystemCoherence l E (Spec (.of D.k)) SS)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (tX : RingedDerivedTensorCoherence.{u + 1, u, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X) SX.systemClosed SX.systemTensorModel βX)
    (tY : RingedDerivedTensorCoherence.{u + 1, u, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) SY.systemClosed SY.systemTensorModel βY) :
    ∃ (r : Realization l E D hl f c SX SZ SY)
      (g : Geometry l E f SX SY) (s : SectionsPush g)
      (aX : DualizingOperation (D := D) (hl := hl) X SX SS)
      (aY : DualizingOperation (D := D) (hl := hl) Y SY SS),
      Nonempty (IntegralSupport r) := by
  sorry

end WeilConjectures.FiniteAdjunctionDiagram
