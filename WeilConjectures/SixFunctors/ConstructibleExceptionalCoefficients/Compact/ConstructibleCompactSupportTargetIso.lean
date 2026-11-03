/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Compact.ConstructibleCompactSupportTargetIsoStage
import WeilConjectures.SixFunctors.Constructible.ConstructibleCompactSupportTargetIsoDescent

/-! # Compact support under an isomorphism of the target

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
structural specialization and ordinary compact-support composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- Compact support is covariant under an isomorphism of its target: if
f followed by e.hom is g, the compact-support functor of f is the
compact-support functor of g followed by inverse image under e.hom.
This assertion involves only the left functors.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
structural specialization; lem-sf-native-exceptional-structural-transport, Step 2.
(blueprint: lem-sf-constructible-compact-support-target-iso).

Proof: use the equation h to identify the composite f followed by e.hom with g.
At a finite coefficient stage, factor each compact-support candidate as open extension followed by
proper derived direct image. Composition with the target isomorphism is exact
transport, inverse to inverse image under e.hom. Proper
composition gives the comparison when the compactifications correspond.
Pass to a common refinement to compare arbitrary c and c', using the canonical
proper/open refinement comparisons and their cocycle. The comparison commutes
with scalar extension: at each quotient this is naturality of the proper mate
and the open unit. Apply the integral reduction--limit comparison on the full
normalized tower, retaining its augmentation and transitions, to obtain the
integral comparison; no faithfulness of individual reductions is used.
Localize this comparison at the uniformizer. S.ring.rationalLeft and
S'.ring.rationalLeft identify the given rational left functors with these
compact-support candidates. Their scalar-normalization equations identify
the transition comparisons. Descend the natural comparison and its inverse
on common-field representatives, using S.common.commonComparison and the
corresponding comparison of S'. Scalar compatibility makes it independent
of enlargement; naturality follows on a representative of every morphism.
This proves the displayed functor isomorphism for the specified systems,
without choosing a new exceptional functor or invoking any native adjoint.
For empty X the same maps compare zero functors; identity target transports
use the unit comparisons. -/
theorem constructible_compact_support_target_iso
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y Z : Scheme.{max u v}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : X ⟶ Y) (g : X ⟶ Z) (e : Y ≅ Z) (h : f ≫ e.hom = g)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (S : System.{u, v} l Ω D hl (f := f)) (c : Compactification f)
    (S' : System.{u, v} l Ω D hl (f := g)) (c' : Compactification g) :
    Nonempty ((S.ring.operation c .closed).F ≅
      (S'.ring.operation c' .closed).F ⋙ commonStageDerivedPullback l Ω e.hom) := by
  obtain ⟨q, hq⟩ := constructible_compact_support_target_stage_comparison
    l Ω D hl f g e h S c S' c'
  exact ⟨stageSystem_iso_of_restrictions
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
    (S.ring.operation c .closed).F
    ((S'.ring.operation c' .closed).F ⋙ commonStageDerivedPullback l Ω e.hom)
    q (fun hij K ↦ hq hij K)⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
