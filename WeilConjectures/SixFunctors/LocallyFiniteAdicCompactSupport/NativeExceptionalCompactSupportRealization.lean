/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeExceptionalCompactSupportIntegralTransition
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportGeometry
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientChange
import WeilConjectures.CategoryTheory.StageSystem.StageComparisonNaturality

/-! # Coefficient realization of ordinary native compact support

Source: the scalar-realization step of
cor-coef-verdier-weil-equivariance.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local instance 2000] Shrink.instField Shrink.instAlgebra
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.LocallyFiniteAdicRealization

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
/-- Assemble an ordinary natural isomorphism from its stage comparisons. -/
private theorem assembleStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {B : Type*} [Category B] (T : StageSystem C) (F H : T.PairCategory ⥤ B)
    (e : ∀ i, T.ι i ⋙ F ≅ T.ι i ⋙ H)
    (he : ∀ (A : T.PairCategory) (i : I) (h : A.stage ≤ i),
      F.map (T.isoToStage A h).hom ≫ (e i).hom.app (A.toStage h) =
        (e A.stage).hom.app A.obj ≫ H.map (T.isoToStage A h).hom) :
    Nonempty (F ≅ H) :=
  ⟨NatIso.ofComponents (fun A ↦ (e A.stage).app A.obj)
    (fun g ↦ StageSystem.stageComparison_naturality T F H e he g)⟩

variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]

/-- Choose the uniquely prescribed finite comparisons and descend them. -/
private theorem comparisonWithChanges [G : NativeGeometry.{u} l]
    [∀ x : X, Invertible (l : X.residueField x)] (f : X ⟶ Y)
    [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (source : Realization l X) (target : Realization l Y)
    (S : ConstructibleExceptionalCoefficients.System.{u, 0} l (PadicAlgCl l) D hl (f := f))
    (c : Compactification f)
    (change : ∀ E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E))
          (nativeCoefficients l))
    (ha : ∀ (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) (T : Scheme.{u})
      (C : CoefficientPresentation l T
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      (change E).map T = C.integralMap l T) :
    Nonempty ((S.ring.operation c .closed).F ⋙ target.J ≅ source.J ⋙ actual l c) := by
  classical
  have finite (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :=
    systemFiniteComparison l D hl source target S c E (change E) (ha E)
  let alpha (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :=
    (finite E).exists.choose
  have halpha (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :=
    (finite E).exists.choose_spec
  exact assembleStage
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
    ((S.ring.operation c .closed).F ⋙ target.J) (source.J ⋙ actual l c) alpha
    (fun A E h ↦ systemFiniteTransition l D hl source target S c change ha alpha halpha A E h)

/-- The specified common-stage compact-support operation is realized by the ordinary
native open/proper functor. This involves no Weil category or forgetful model.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence and coefficient-comparisons paragraph;
Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-exceptional-compact-support-realization).

Proof: at every finite coefficient subfield use S.ring.rationalLeft to identify
the specified left operation with the prescribed rational compact-support functor.
For an integral representative, apply the inverse target integral realization,
the inverse integral compact-support realization and the proper/open scalar mate,
then compact support of the inverse source integral realization. The scalar mate
is invertible on constructible inputs by bounded-below proper scalar comparison
and exact open extension. The section equivalence reflects these isomorphisms.
Extend over inverse uniformizer powers to rational arrows. The normalized integral
scalar squares and the common_field equations of the specified source and target realizations make
these finite-stage maps compatible with every finite field inclusion. Compose
with S.common.commonComparison, and descend the maps and their inverses on common
finite-stage representatives. Every arrow is represented over a common field;
the compatibility square makes the construction independent of enlargement and
proves naturality. This yields the displayed natural isomorphism for the specified source, target
and S, without choosing alternative realizations. Empty schemes and identity
coefficient extensions use the same unit-normalized maps. -/
theorem system_compact_support_realization (f : X ⟶ Y)
    [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (source : Realization l X) (target : Realization l Y)
    (S : ConstructibleExceptionalCoefficients.System.{u, 0} l (PadicAlgCl l) D hl (f := f))
    (c : Compactification f) :
    Nonempty ((S.ring.operation c .closed).F ⋙ target.J ≅ source.J ⋙ actual l c) := by
  classical
  obtain ⟨G⟩ := native_compact_support_geometry.{u} l
  let := G
  let change (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :=
    (native_completed_coefficient_change l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
      (embedding l E)).choose
  have ha (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (T : Scheme.{u})
      (C : CoefficientPresentation l T
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
        (embedding l E)) : (change E).map T = C.integralMap l T :=
    (native_completed_coefficient_change l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
      (embedding l E)).choose_spec T C
  have primeUnit : IsUnit (l : Γ(X, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using
      (PurCompactSupport.coefficientPrimeUnit l D hl).map ρ.hom
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        ((primeUnit.map (X.presheaf.germ ⊤ x trivial).hom).map (X.residue x).hom)).invertible
  exact comparisonWithChanges l D hl f source target S c change ha

end WeilConjectures.LocallyFiniteAdicCompactSupport
