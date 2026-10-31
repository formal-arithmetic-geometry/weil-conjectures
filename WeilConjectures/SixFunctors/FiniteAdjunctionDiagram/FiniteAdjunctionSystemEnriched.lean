/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagram.FiniteAdjunctionDiagramData

/-! Enriched adjunction on derived coefficient systems before total limits. -/

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
/-- The specified internal transpose induces coherent enriched adjunction.
Source: realization node steps 14--18; blueprint finite exceptional proof;
Stacks 08J9 and 0941
(blueprint: lem-sf-finite-adjunction-system-enriched).
Proof: for normalized M and N form H = internalHom(M,G N) and Q = Rf_* H.
The unbounded proper/open projection comparison applies to this Q without
assuming finite Tor amplitude. Compose it with the ordinary image counit,
internal evaluation, and the exceptional counit. Tensor-Hom transposition is
exactly r.enrichedMap. Its evaluated maps are the canonical finite internal
adjunction maps, by the projection/evaluation/counit equation. They are
invertible, so the system transpose is invertible by conservativity. Its
inverse is natural in M and N; apply termwise derived sections and the
specified SectionsPush comparison to obtain the natural global isomorphism.
These are exactly r.globalMap components. At each finite level use the
canonical finite enriched adjunction, whose H-zero action is the already
fixed finite adjunction. Resolution normalization and the unit/counit
identities give the finite evaluation square. All maps and inverse identities
exist before taking total inverse limits. -/
theorem finiteAdjunctionSystemEnriched
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
      (coefficientSequenceCommRingSheaf l E Y) SY.systemClosed SY.systemTensorModel βY)
    (r : Realization l E D hl f c SX SZ SY)
    (g : Geometry l E f SX SY)
    (s : SectionsPush g) :
    Nonempty (Enriched r g s βX βY) := by
  sorry

end WeilConjectures.FiniteAdjunctionDiagram
