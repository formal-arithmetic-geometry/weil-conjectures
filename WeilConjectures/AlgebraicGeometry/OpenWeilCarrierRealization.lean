/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OpenWeilCoefficientFibres

/-! # Open Weil extension comparison

Source: blueprint lem-zl-quasi-finite, proof (1) and (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
  {U₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [hUsep : IsSeparated U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hXsep : IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]

include hUsep hXsep

variable (J : sfCommonStageWeilSheaf D l hl U₀ Qbar ⥤
  sfCommonStageWeilSheaf D l hl X₀ Qbar)
  (a : J ⊣ zlWeilPull D l hl Qbar j₀)

include a

/-- The underlying carrier of any left adjoint to open Weil restriction is the
specified compact-support value on every integral finite-stage presentation.

Source: latest blueprint lem-zl-quasi-finite.proof.md, proof (1), coefficient passage.
(blueprint: lem-zl-open-weil-carrier-realization).

Proof: for the compactification (j,id), identify completed integral compact support
with ordinary extension by zero using the normalized Roos comparison. Exactness
and constructibility make it preserve both standard classes. Rationalize and
apply the scalar-compatible common-stage descent of openExtension_tExact. Lift
the resulting heart functor through its invertible Frobenius exchange, whose mate
is fixed by openWeilUnitAndEmptyFibre. Its restriction is exactly zlWeilPull by
the normalized Frobenius square. Uniqueness of left adjoints identifies it with J.
The integral/rational comparison and the coefficient-action object formula give
the displayed iso on the included localization of K. Apply the functor to the
specified carrier presentation of F and compose with that comparison. The
comparison depends only on the carrier; no Weil structure on K is required.
For the empty open every value is zero; for the identity open the comparisons
are the identity normalizations. No stable integral Weil lattice is assumed. -/
theorem openWeilCarrierRealization :
    (∀ (F : sfCommonStageWeilSheaf D l hl U₀ Qbar)
      (L : Padic.FiniteCoefficientFields l Qbar)
      (K : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) (D.geometricFiber U₀).left),
      Nonempty (F.obj.carrier ≅ (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
        ((sfRationalConstructibleLocalization l _ (D.geometricFiber U₀).left).obj K)) →
      Nonempty ((J.obj F).obj.carrier ≅
        sfQbarCompactSupportValue l (X := (D.geometricFiber U₀).left)
          (Y := (D.geometricFiber X₀).left) (f := zlFiberMap D j₀)
          D.k (zlClosurePrimeUnit D l hl) Qbar
          (Compactification.ofIsOpenImmersion (zlFiberMap D j₀)) L K)) := by sorry

end WeilConjectures
