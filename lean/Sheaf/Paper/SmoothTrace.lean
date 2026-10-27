/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek

/-!
# Smooth traces at finite coefficients

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-def-sp-trace/def-pur-smooth-trace.md (blueprint: def-pur-smooth-trace).
The compact-support image of the specified smooth purity map is followed by the
canonical relative exceptional counit. The latter is transported from the published
site-comparison construction, using the same compactification as the purity map.
The unit case uses the purity map's explicit ordinary-etale presentation; its
identifying isomorphism is the unit of the intrinsic realization equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The compact-support candidate at the finite-type-over-a-field compactification.
Source: blueprint smooth trace, Rf_! (blueprint: def-pur-smooth-trace). -/
noncomputable def smoothCompactSupport (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Scheme.proEtaleDerivedCategory X P.Ring ⥤ Scheme.proEtaleDerivedCategory Y P.Ring := by
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  exact Scheme.sfIntrinsicCompactSupport (HasCompactification.compactification f) P.Ring

/-- The recorded degree-zero coefficient unit, in intrinsic constant-ring coordinates.
Source: blueprint smooth trace, Lambda_Y (blueprint: def-pur-smooth-trace). -/
noncomputable def coefficientUnit (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory Y P.Ring :=
  (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit P.Coefficient Y))

/-- The canonical relative exceptional counit in intrinsic coefficient coordinates.
It is the support realization comparison, followed by the published exceptional
counit, then the counit of the intrinsic equivalence. The published counit itself is
compact-support site comparison followed by the ordinary etale and comparison counits.
The zero branch merely totalizes the definition outside bounded-below inputs; it is
never used on D^b_ctf or on the coefficient unit. Finite cohomological support gives
boundedness below, and the inverse realization is exact and preserves that property.
Source: blueprint smooth trace, Tr_{f,K}; sk-prop-sf-existence (c), the normalized
relative adjunction (blueprint: def-pur-smooth-trace). -/
noncomputable def smoothExceptionalCounit
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (smoothCompactSupport P f).obj
        ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
          ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).obj
            ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))) ⟶ K := by
  classical
  letI := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  let L := (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K
  exact if hL : DerivedCategory.TStructure.t.plus L then
    (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
      (HasCompactification.compactification f)).hom.app
        ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).obj L) ≫
      (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.map
        (ProEtale.rightDerivedUpperShriekCounit f L hL) ≫
      (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).counitIso.hom.app K
  else 0

/-- For a bounded constructible finite-Tor coefficient complex, the smooth trace is obtained
by applying compact-support pushforward to the canonical smooth purity map and then composing
with the intrinsic constructible exceptional counit.
Source: blueprint smooth trace, second composite (blueprint: def-pur-smooth-trace). -/
noncomputable def coefficientValuedSmoothTrace
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (smoothCompactSupport P f).obj
        ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
          ((shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
              (ModuleCat.{u + 1} P.Coefficient))) (2 * (d : ℤ))).obj
            (((smoothPurityTensor P.Coefficient X).obj
                ((P.smoothPurityPullback f).obj
                  ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).obj
              ((shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
                  (ModuleCat.{u + 1} P.Coefficient))) (-(2 * (d : ℤ)))).obj
                (P.diagonalTwist X d))))) ⟶ K :=
  (smoothCompactSupport P f).map
      (P.smoothPurityMap f d K hK) ≫
    smoothExceptionalCounit P f K

/-- The smooth trace on the coefficient unit, using the purity map's explicit formula
in the canonical ordinary-etale unit presentation. The realization unit supplies the
representing isomorphism. The existing uniqueness characterization of the tensor purity
map identifies this with its coefficient-valued specialization at Lambda_Y; thus no
separate finite-Tor proof is needed merely to construct this particular arrow.
Source: blueprint smooth trace, first composite (blueprint: def-pur-smooth-trace). -/
noncomputable def smoothTrace
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    (smoothCompactSupport P f).obj
        ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
          ((shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
              (ModuleCat.{u + 1} P.Coefficient))) (2 * (d : ℤ))).obj
            (((smoothPurityTensor P.Coefficient X).obj
                ((P.smoothPurityPullback f).obj
                  ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
                    (coefficientUnit P Y)))).obj
              ((shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
                  (ModuleCat.{u + 1} P.Coefficient))) (-(2 * (d : ℤ)))).obj
                (P.diagonalTwist X d))))) ⟶ coefficientUnit P Y := by
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let C := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory
  let U := Etale.ordinaryFiniteUnit P.Coefficient Y
  let L := E.inverse.obj (coefficientUnit P Y)
  let γ := (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
    (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj L)).hom ≫
      (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
        (P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k)) L U
          (E.unitIso.app (C.obj U)))
  exact (smoothCompactSupport P f).map γ ≫
    smoothExceptionalCounit P f (coefficientUnit P Y)

end WeilConjectures.PurityFiniteSetting
