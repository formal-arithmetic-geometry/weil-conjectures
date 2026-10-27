/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Paper.WeilGeometricFiberProperties
public import Sheaf.Paper.CompactSupportCoefficientAction

/-! # Realization of open extension on represented Weil ind-sheaves

Source: SGA 4, XVII, §5.1; Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7.
(blueprint: lem-zl-ind-open-realization).
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

/-- A represented open ind-extension realizes the normalized open compact-support
operation on its underlying common-stage object. No proper image is involved.
Source: SGA 4, XVII, 5.1; Bhatt--Scholze, 6.7.6--6.7.7
(blueprint: lem-zl-ind-open-realization).

Proof: integral extension by zero is exact and left adjoint to restriction. The
identity-proper compactification computes this exact extension at every positive
coefficient quotient. The normalized completed realization consequently identifies
its Roos-limit value with integral extension by zero. Rationalization and finite
coefficient extension preserve this adjunction, its units, and the standard heart.
It descends to an exact left adjoint on common-stage hearts, with the prescribed
Frobenius comparison given by the inverse open-adjunction mate. Transport through
AsSmall and extend by filtered colimits; the Yoneda Kan unit identifies this
extension on represented objects with the original heart functor. The fixed-pair
adjunction has the same unit normalization as zlIndWeilOpenShriek, so uniqueness
of left adjoints identifies the two. Full faithfulness of the Weil embedding then
identifies the arbitrary representative G with this heart extension. Applying the
heart inclusion gives the displayed comparison. Finite-type schemes over a field
are noetherian, so their open immersions are quasi-compact; no separated structure
map is required. Empty opens, the identity open and zero objects are included. -/
theorem zlIndWeilOpenShriek_realization
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    (S : SfCompactSupportCoefficientAction l D.k (zlRealizationPrimeUnit D l hl) Ω
      (.ofIsOpenImmersion (zlFiberMap D j₀)))
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (G : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (e : (zlWeilIndEmbedding D l hl Ω Y₀).obj G ≅
      (zlIndWeilOpenShriek D l hl Ω j₀).obj
        ((zlWeilIndEmbedding D l hl Ω X₀).obj F)) :
    Nonempty (G.obj.carrier ≅ S.system.functor.obj F.obj.carrier) := by
  sorry

end WeilConjectures
