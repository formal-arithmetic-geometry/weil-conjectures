/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralNormalizedRefinementData
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization

/-! # Data and normalization for integral refinement pasting -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
section Data
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- Data and compatibility premises for integral refinement pasting.
(blueprint: def-sf-integral-refinement-pasting-data). -/
structure IntegralRefinementPastingData (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Over (Spec (CommRingCat.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left] where
  F : ∀ _c : Compactification f.left,
    finiteTorConstructibleIntegralCategory l E X.left ⥤
      finiteTorConstructibleIntegralCategory l E Y.left
  r : ∀ c : Compactification f.left,
    F c ⋙ (finiteTorConstructibleIntegral l E Y.left).ι ≅
      (finiteTorConstructibleIntegral l E X.left).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E) c
  ρ : ∀ {c d : Compactification f.left}, c.Refinement d → (F c ≅ F d)
  e : ∀ {_c d : Compactification f.left} (v : _c.Refinement d),
    (finiteTorConstructibleIntegral l E X.left).ι ⋙ ringedOpen l E d.i ≅
      (finiteTorConstructibleIntegral l E X.left).ι ⋙
        ringedOpen l E _c.i ⋙ ringedPush l E v.hom
  compatible : ∀ c : Compactification f.left,
      ∃ η : F c ⋙ PurCompactSupport.finiteTorIntegralInclusion l E Y.left ≅
          PurCompactSupport.finiteTorIntegralInclusion l E X.left ⋙
            sfCompactSupportFiniteIntegralFunctor l D.k
              (PurCompactSupport.coefficientPrimeUnit l D hl) c E,
        ∀ K : finiteTorConstructibleIntegralCategory l E X.left,
          (r c).hom.app K = (sfIntegralConstructible l E Y.left).ι.map (η.hom.app K) ≫
            (sfQcqsCompactSupportRealization l E D.k
              (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
                ((PurCompactSupport.finiteTorIntegralInclusion l E X.left).obj K)
  transpose : ∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left),
      (ringedOpenAdj l E d.i).homEquiv _ _ ((e v).hom.app K) ≫
          PurCompactSupport.refinementRestriction (PurCompactSupport.completed l E) v
            (PurCompactSupport.completedPull_comp l E c.i v.hom) K.obj =
        (ringedOpenAdj l E c.i).unit.app K.obj

/-- The single-refinement normalization premise of integral pasting.
(blueprint: def-sf-integral-refinement-pasting-normalized). -/
structure IntegralRefinementPastingData.Normalized
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Over (Spec (CommRingCat.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
  (P : IntegralRefinementPastingData l E D hl f) : Prop where
  equation : ∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left),
      (finiteTorConstructibleIntegral l E Y.left).ι.map ((P.ρ v).hom.app K) ≫
          (P.r d).hom.app K =
        (P.r c).hom.app K ≫
          ((ringedPushComp l E v.hom d.g ≪≫
            eqToIso (congrArg (ringedPush l E) v.hom_g)).inv.app
              ((ringedOpen l E c.i).obj K.obj)) ≫
          (ringedPush l E d.g).map ((P.e v).inv.app K)

end Data
end WeilConjectures.IntegralSystemRealization
