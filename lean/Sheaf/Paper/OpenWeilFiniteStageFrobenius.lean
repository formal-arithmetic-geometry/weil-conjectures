/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Sheaf.Paper.OpenWeilCoefficientFibres

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

/-- Finite-stage open Weil extension and its natural local Frobenius comparison.

Source: latest blueprint lem-zl-quasi-finite.proof.md, proof (1) coefficient passage
and proof (2) local Frobenius on the open.
(blueprint: lem-zl-open-weil-finite-stage-frobenius).

Proof: at each finite coefficient field restrict the actual rational compact
support functor for (j,id) to its heart using openExtension_tExact. Lift its
normalized invertible Frobenius exchange to fixed pairs; this is the functor J_L.
Its carrier is exactly the recorded rational compact-support functor. The
finite/common scalar square of openWeilUnitAndEmptyFibre identifies its inclusion
with the common-stage lift. Uniqueness of adjoints identifies the latter with J,
yielding the second natural iso. The normalized open unit restricts the output
to the original input as a Weil isomorphism. Apply the inverse-compositor point
comparison at the compatible closed geometric points in the statement. The
residue-compatible pullback theorem and naturality of point transport identify
the three factors defining local Frobenius. Induct on the residue degree to
identify the iterated Weil structure maps. Take degree-zero cohomology to get e;
the same natural equations give the displayed intertwining identity on every K.
Open immersions identify residue fields, so the return exponents agree. All
comparisons commute with finite scalar extension. The zero object, empty open
and identity open are included by the same normalized adjunction equations. -/
theorem openWeilFiniteStageFrobenius :
    (∀ L : Padic.FiniteCoefficientFields l Qbar,
      ∃ Jₑ : sfWeilSheaf D l hl U₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⥤
          sfWeilSheaf D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L),
      Nonempty (Jₑ ⋙ zlFiniteWeilHeartCarrier D l hl _ X₀ ≅
        zlFiniteWeilHeartCarrier D l hl _ U₀ ⋙
          sfCompactSupportFiniteFunctor l (X := (D.geometricFiber U₀).left)
            (Y := (D.geometricFiber X₀).left) (f := zlFiberMap D j₀)
            D.k (zlClosurePrimeUnit D l hl)
            (Compactification.ofIsOpenImmersion (zlFiberMap D j₀))
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)) ∧
      Nonempty (zlWeilHeartStage D l hl Qbar U₀ L ⋙ J ≅
        Jₑ ⋙ zlWeilHeartStage D l hl Qbar X₀ L) ∧
      ∀ (u : {u : U₀.left // u ∈ closedPoints U₀.left})
        (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (ιU : U₀.left.residueField u.val →+* D.k)
        (hU : ιU.comp (U₀.hom.residueFieldAlgebraMap u.val) = algebraMap D.k₀ D.k)
        (ιX : X₀.left.residueField x.val →+* D.k)
        (hX : ιX.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
        j₀.left.base u.val = x.val →
        localClosedPoint D U₀ u ιU hU ≫ zlFiberMap D j₀ =
          localClosedPoint D X₀ x ιX hX →
        ∃ e : Jₑ ⋙ zlClosedCoefficientFiber D l hl _ X₀ x ιX hX ≅
            zlClosedCoefficientFiber D l hl _ U₀ u ιU hU,
          ∀ K : sfWeilSheaf D l hl U₀
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L),
            localClosedFrobeniusCohomology l _ D hl X₀ (Jₑ.obj K).obj x ιX hX 0 ≫
                e.hom.app K =
              e.hom.app K ≫ localClosedFrobeniusCohomology l _ D hl U₀ K.obj u ιU hU 0) := by sorry

end WeilConjectures
