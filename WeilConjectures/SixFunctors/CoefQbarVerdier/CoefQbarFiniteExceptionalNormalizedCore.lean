/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarFiniteExceptionalCore
public import WeilConjectures.SixFunctors.RationalOperations.RationalDualFormulaAdjunction
import WeilConjectures.SixFunctors.RationalOperations.RationalExceptionalIdentifications

/-! Trace-normalized finite exceptional comparison data.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-normalized-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

private theorem transport_rightAdjointUniq
    {C B : Type*} [Category C] [Category B] {F : C ⥤ B} {G H : B ⥤ C}
    (a : F ⊣ G) (b : F ⊣ H) :
    a.ofNatIsoRight (a.rightAdjointUniq b) = b := by
  apply Adjunction.ext_counit
  ext M
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← a.rightAdjointUniq_hom_app_counit b M]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Finite comparison data can be chosen with trace-normalized dual-formula adjunctions.
This asserts no scalar compatibility and uses only the one-field adjunction construction.
Source: thm-coef-qbar-verdier, retained proof step 9; rational exceptional construction,
steps 10--11. (blueprint: lem-coef-qbar-finite-exceptional-normalized-core)

Proof: first take any finite core. For each E take the trace-normalized adjunction on
its prescribed dual formula. Compare it with the coefficient system's adjunction,
transported along rationalLeft, using right-adjoint uniqueness. The resulting comparison
has precisely the chosen normalized adjunction, because transporting by rightAdjointUniq
recovers its target adjunction. Replace the old finite comparison by this new one.
Conjugate the old common-stage comparison by the inclusion of the new comparison followed
by the inverse old comparison. This is a natural isomorphism. The two old finite
comparisons cancel in its component formula, giving the required normalization. The
construction is pointwise in E, so it includes repeated fields, identity extensions and
zero objects without any scalar compatibility assumption. -/
theorem finite_exceptional_normalized_core
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)) :
    ∃ t : FiniteExceptionalFormulaCore D l hl Ω X f BX BY c S,
      ∀ E : Index l Ω,
        RationalOperations.DualFormulaAdjunctionNormalized D l hl X c (fieldStage l Ω E)
          (BX.finite.omega E) (BY.finite.omega E) (BX.finite.datum E) (BY.finite.datum E)
          (t.finite E).adjunction := by
  classical
  obtain ⟨t⟩ := finite_exceptional_formula_core D l hl Ω X f BX BY c S
  have adjExists (E : Index l Ω) :=
    RationalOperations.rationalDualFormulaAdjunction_exists D l hl X c (fieldStage l Ω E)
      (BX.finite.omega E) (BY.finite.omega E) (BX.finite.datum E) (BY.finite.datum E)
      (AuxiliaryClosure.{u} l) S
  choose a ha using adjExists
  let finite (E : Index l Ω) :=
    RationalOperations.exceptionalIdentificationOfIso D l hl X (AuxiliaryClosure.{u} l)
      c S (fieldStage l Ω E) (BX.finite.omega E) (BY.finite.omega E)
      (BX.finite.datum E) (BY.finite.datum E)
      (((S.ring.operation c (.rational (fieldStage l Ω E))).adjunction.ofNatIsoLeft
        (S.ring.rationalLeft c (fieldStage l Ω E))).rightAdjointUniq (a E))
  let comparison (E : Index l Ω) :=
    Functor.isoWhiskerRight
      ((finite E).comparison ≪≫ (t.finite E).comparison.symm) (inclusion (Y := X) E) ≪≫
        t.comparison E
  have normalized (E : Index l Ω) (M : Stage l Ω Y E) :
      (inclusion E).map ((finite E).comparison.hom.app M) ≫
        (BX.comparison E).hom.app
          (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
            (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
              ((BY.finite.datum E).dual.obj (op M)))) ≫
        BX.duality.dual.map
          ((CoefQbarPullback D l hl Ω f).map ((BY.comparison E).inv.app (op M)) ≫
            (pullbackInclusion D l hl Ω X f E
              ((BY.finite.datum E).dual.obj (op M))).inv).op =
      (comparison E).hom.app M := by
    dsimp only [comparison]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Iso.symm_hom, Functor.map_comp]
    rw [← t.normalized E M]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      Category.comp_id]
  refine ⟨{ finite := finite, comparison := comparison, normalized := normalized }, ?_⟩
  intro E
  change RationalOperations.DualFormulaAdjunctionNormalized D l hl X c (fieldStage l Ω E)
    (BX.finite.omega E) (BY.finite.omega E) (BX.finite.datum E) (BY.finite.datum E)
    (((S.ring.operation c (.rational (fieldStage l Ω E))).adjunction.ofNatIsoLeft
      (S.ring.rationalLeft c (fieldStage l Ω E))).ofNatIsoRight
      (((S.ring.operation c (.rational (fieldStage l Ω E))).adjunction.ofNatIsoLeft
        (S.ring.rationalLeft c (fieldStage l Ω E))).rightAdjointUniq (a E)))
  rw [transport_rightAdjointUniq]
  exact ha E

end WeilConjectures.CoefQbarVerdier
