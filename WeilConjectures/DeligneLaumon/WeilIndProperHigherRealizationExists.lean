/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilGeometricFiberProperties
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.DeligneLaumon.ConstructibleTruncations
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Existence of the normalized proper higher realization

This is the existence part of the comparison used by
`WeilConjectures.zlIndWeilProperHigher_realization`; the latter transports the
comparison to any supplied representative by full faithfulness.
(blueprint: lem-zl-ind-proper-higher-realization-exists).

Proof: apply the ordinary-heart realization and proper-image comparison on finite
coefficient stages, transport it through the normalized compact-support action,
and lift the resulting Frobenius-compatible carrier to the common-stage Weil
heart. The representability and carrier comparison are packaged together for
use by the parent transport theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/--
The normalized proper higher image has a represented carrier realizing the
coefficient-action cohomology.  This is the proper-image comparison itself;
the parent theorem only handles transport from this chosen representative to
an arbitrary supplied representative.
Source: SGA 4, XVII, proper image; Bhatt--Scholze 6.8.14--6.8.15; Barrett,
arXiv:2005.10859, Theorem 1.1; Kashiwara--Schapira, §15.3
(blueprint: lem-zl-ind-proper-higher-realization-exists).

Proof: apply the ordinary-heart realization and proper-image comparison on finite
coefficient stages, transport it through the normalized compact-support action,
and lift the resulting Frobenius-compatible carrier to the common-stage Weil
heart. The representability and carrier comparison are packaged together for
use by the parent transport theorem.
-/
theorem zlIndWeilProperHigher_realization_exists
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left]
    (S : SfCompactSupportCoefficientAction l D.k (zlRealizationPrimeUnit D l hl) Ω
      (.ofIsProper (zlFiberMap D p₀)))
    (n : ℕ) (G : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    ∃ H : sfCommonStageWeilSheaf D l hl Y₀ Ω,
      Nonempty ((zlWeilIndEmbedding D l hl Ω Y₀).obj H ≅
        ((zlIndWeilPush D l hl Ω p₀).rightDerived n).obj
          ((zlWeilIndEmbedding D l hl Ω X₀).obj G)) ∧
      Nonempty (H.obj.carrier ≅
        (constructibleTruncationCohomology
          (sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl) (n : ℤ)).obj
            (S.system.functor.obj G.obj.carrier)) := by
  sorry

end WeilConjectures
