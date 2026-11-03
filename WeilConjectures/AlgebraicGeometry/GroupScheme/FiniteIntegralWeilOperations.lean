/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFrobeniusTransport.CondensedFrobeniusCohomologyTransportIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntrinsicFiniteTorMixedSupportCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupMixed.CondensedMixedSupportCup
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.CategoryTheory.WeilEquivariance

/-! The finite and integral coefficient companion of the operation-equivariance statement.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md, Steps 1--3
(blueprint: lem-fix-weil-operations-finite).
Proof steps: use the canonical direct and compact Frobenius-square mates; transport the
strict-pair datum through pullback, tensor, internal Hom, adjunction and projection maps;
then apply exact point sections to the ordinary and compact-support exchanges and the
mixed-support cup.  The postponed theorem records these clauses without proving them.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

universe u v

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

/-! The following declarations are the current condensed strict-pair interface used by the
finite and integral coefficient stages.  Each is a named construction from the blueprint. -/

/-- The current strict-pair carrier for a condensed coefficient ring.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, strict-pair paragraphs (blueprint: sk-def-sf-weil-complexes). -/
abbrev condensedStrictPair
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g] : Type (u + 2) :=
  StrictWeilCondensed.Complex Λ.X (asIso g)

/-- The ordinary derived module category used by all operation clauses.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, ordinary derived module convention
(blueprint: det-def-sf-operations). -/
abbrev condensedDerivedModule (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.D Λ.X X

/-- The structure morphism of a strict pair, exposed as a Weil datum.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, displayed `φ_M` (blueprint: sk-def-sf-weil-complexes). -/
noncomputable def strictWeilDatum
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    (M : condensedStrictPair Λ g) :
    (StrictWeilCondensed.action Λ.X (asIso g)).obj M.obj.a.obj ⟶ M.obj.a.obj :=
  M.obj.str.hom

/-- Pullback of a strict datum through the canonical Frobenius square comparison.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, pullback datum paragraph
(blueprint: lem-fix-condensed-pullback-coherence). -/
noncomputable def pullbackWeilDatum
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (sq : CommSq gX f f gY)
    (M : condensedStrictPair Λ gY) :
    (CondensedRing.upperStar Λ.X gX).mapDerivedCategory.obj
        ((moduleObjectDerivedPullback Λ.X f).obj M.obj.a.obj) ⟶
      (moduleObjectDerivedPullback Λ.X f).obj M.obj.a.obj :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ.X gX).inv.app _ ≫
    CategoryTheory.transportWeilDatum (moduleObjectDerivedPullback Λ.X f)
      (AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.square
    Λ.X gX f f gY sq.w)
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X gY).hom.app _ ≫
        strictWeilDatum Λ gY M)

/-- Pullback of an arbitrary Weil datum through the same canonical square.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, pullback datum paragraph
(blueprint: lem-fix-condensed-pullback-coherence). -/
noncomputable def pullbackDatum
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (sq : CommSq gX f f gY)
    (L : condensedDerivedModule Λ Y)
    (φ : (moduleObjectDerivedPullback Λ.X gY).obj L ⟶ L) :
    (moduleObjectDerivedPullback Λ.X gX).obj
        ((moduleObjectDerivedPullback Λ.X f).obj L) ⟶
      (moduleObjectDerivedPullback Λ.X f).obj L :=
  (AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.square
    Λ.X gX f f gY sq.w).inv.app L ≫
    (moduleObjectDerivedPullback Λ.X f).map φ

/- The Tate datum is supplied by `StrictWeilCondensed.tateDatum` below.  In particular, no
free object or free scalar is introduced at this interface. -/

/-! Canonical induced data for operation maps. -/

/-- The canonical direct-image datum induced by a Frobenius exchange and a source datum.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, `α_{*,M}` (blueprint: lem-fix-weil-operations). -/
noncomputable def directWeilDatum
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (sq : CommSq gX f f gY)
    (M : condensedDerivedModule Λ X)
    (φ : (moduleObjectDerivedPullback Λ.X gX).obj M ⟶ M) :
    (moduleObjectDerivedPullback Λ.X gY).obj
        ((moduleObjectDerivedPushforward Λ.X f).obj M) ⟶
      (moduleObjectDerivedPushforward Λ.X f).obj M :=
  (FrobeniusSquareExchange.direct Λ f sq).app M ≫
    (moduleObjectDerivedPushforward Λ.X f).map
      φ

/-- Convert a module-side datum to the equivalent strict-action datum.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, exact inverse-image comparison
(blueprint: sk-def-sf-weil-complexes). -/
noncomputable def actionWeilDatum
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    (M : condensedDerivedModule Λ X)
    (φ : (moduleObjectDerivedPullback Λ.X g).obj M ⟶ M) :
    (StrictWeilCondensed.action Λ.X (asIso g)).obj M ⟶ M :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ.X g).inv.app M ≫ φ

/-- Tensor datum transported back to the native module pullback category.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, strong monoidal pullback comparison
(blueprint: lem-sfb-derived-pullback-strong-monoidal). -/
noncomputable def tensorPullbackDatum
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    (M N : condensedDerivedModule Λ X)
    (φM : (moduleObjectDerivedPullback Λ.X g).obj M ⟶ M)
    (φN : (moduleObjectDerivedPullback Λ.X g).obj N ⟶ N) :
    (moduleObjectDerivedPullback Λ.X g).obj (M ⊗ N) ⟶ M ⊗ N :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ.X g).hom.app (M ⊗ N) ≫
    CategoryTheory.MonoidalClosed.tensorWeilDatum
      (StrictWeilCondensed.action Λ.X (asIso g))
      (actionWeilDatum Λ g M φM) (actionWeilDatum Λ g N φN)

/-- Point-section realization of the canonical unit datum.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, `id_R` on `Λ_s`
(blueprint: lem-fix-weil-operations-finite). -/
noncomputable def unitGlobalOperator
    (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (cpt : Compactification Y₀.hom) :
    (condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom).obj
        (𝟙_ _) ⟶
      (condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom).obj
        (𝟙_ _) :=
  (CondensedFrobeniusTransport.ordinaryTransport D Y₀ Λ cpt).app (𝟙_ _) ≫
    (condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X
        (D.geometricFrobenius Y₀).hom).hom.app (𝟙_ _) ≫
        (Functor.Monoidal.εIso
          (StrictWeilCondensed.action Λ.X
            (asIso (D.geometricFrobenius Y₀).hom))).inv)

/-- The ordinary global operator `F_M`, with the canonical exchange and strict datum.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, point-section operator
(blueprint: lem-fix-weil-operations-finite). -/
noncomputable def ordinaryGlobalOperator
    (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (cpt : Compactification Y₀.hom)
    (M : condensedStrictPair Λ (D.geometricFrobenius Y₀).hom) :
    (condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom).obj M.obj.a.obj ⟶
      (condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom).obj M.obj.a.obj :=
  (CondensedFrobeniusTransport.ordinaryTransport D Y₀ Λ cpt).app M.obj.a.obj ≫
    (condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X
        (D.geometricFrobenius Y₀).hom).hom.app M.obj.a.obj ≫
        strictWeilDatum Λ (D.geometricFrobenius Y₀).hom M)

/-- The compact-support global operator `F_{c,M}`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, point-section operator
(blueprint: lem-fix-weil-operations-finite). -/
noncomputable def compactGlobalOperator
    (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (cpt : Compactification Y₀.hom)
    (M : condensedStrictPair Λ (D.geometricFrobenius Y₀).hom) :
    (condensedRingCompactCoefficientComplex Λ.X
        (CondensedFrobeniusTransport.compactification D Y₀ cpt)).obj M.obj.a.obj ⟶
      (condensedRingCompactCoefficientComplex Λ.X
        (CondensedFrobeniusTransport.compactification D Y₀ cpt)).obj M.obj.a.obj :=
  (CondensedFrobeniusTransport.compactTransport D Y₀ Λ cpt).app M.obj.a.obj ≫
    (condensedRingCompactCoefficientComplex Λ.X
      (CondensedFrobeniusTransport.compactification D Y₀ cpt)).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X
        (D.geometricFrobenius Y₀).hom).hom.app M.obj.a.obj ≫
        strictWeilDatum Λ (D.geometricFrobenius Y₀).hom M)

/-- The compact global operator on a tensor pair.  Its datum is the canonical
tensor datum `δ_T ≫ (φ_M ▷ 1) ≫ (1 ◁ φ_N)`, so the target of the cup is the
specified `F_{c,M⊗N}` operator rather than an existential map.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, tensor point-section operator
(blueprint: lem-fix-weil-operations-finite). -/
noncomputable def compactGlobalOperatorTensor
    (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (cpt : Compactification Y₀.hom)
    (M N : condensedStrictPair Λ (D.geometricFrobenius Y₀).hom) :
    (condensedRingCompactCoefficientComplex Λ.X
        (CondensedFrobeniusTransport.compactification D Y₀ cpt)).obj
        (M.obj.a.obj ⊗ N.obj.a.obj) ⟶
      (condensedRingCompactCoefficientComplex Λ.X
        (CondensedFrobeniusTransport.compactification D Y₀ cpt)).obj
        (M.obj.a.obj ⊗ N.obj.a.obj) :=
  (CondensedFrobeniusTransport.compactTransport D Y₀ Λ cpt).app
      (M.obj.a.obj ⊗ N.obj.a.obj) ≫
    (condensedRingCompactCoefficientComplex Λ.X
      (CondensedFrobeniusTransport.compactification D Y₀ cpt)).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X
        (D.geometricFrobenius Y₀).hom).hom.app (M.obj.a.obj ⊗ N.obj.a.obj) ≫
        CategoryTheory.MonoidalClosed.tensorWeilDatum
          (StrictWeilCondensed.action Λ.X
            (asIso (D.geometricFrobenius Y₀).hom))
          (strictWeilDatum Λ (D.geometricFrobenius Y₀).hom M)
          (strictWeilDatum Λ (D.geometricFrobenius Y₀).hom N))

/-- Point-section realization of the intrinsic mixed-support cup.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, mixed-support cup realization
(blueprint: lem-fix-weil-operations-finite). -/
noncomputable def globalMixedSupportCup
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsLocalizingAdmissibleCoefficient C.l Λ.X)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k))
    (hA : LocallyOfFiniteType a) (hQ : QuasiCompact a) (hS : IsSeparated a)
    (c : Compactification a)
    (K : condensedDerivedModule Λ X)
    (hK : condensedConstructibleFiniteTor Λ.X X K)
    (L : condensedDerivedModule Λ X)
    (hL : condensedConstructibleFiniteTor Λ.X X L) :
    (condensedRingCompactCoefficientComplex Λ.X c).obj K ⊗
        (condensedRingOrdinaryCoefficientComplex Λ.X a).obj L ⟶
      (condensedRingCompactCoefficientComplex Λ.X c).obj (K ⊗ L) :=
  by
    letI := hA
    letI := hQ
    letI := hS
    let K' : CondensedConstructibleFiniteTor Λ.X X := ⟨K, hK⟩
    let L' : CondensedConstructibleFiniteTor Λ.X X := ⟨L, hL⟩
    exact TraceCupPoint.tensor Λ.X D.k
        ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K)
        ((moduleObjectDerivedPushforward Λ.X a).obj L) ≫
      (TraceCupPoint.fiber Λ.X D.k).map
        (intrinsicFiniteTorMixedSupportCupProduct Λ.X D C hΛ a c K' L')

/-- Point-section operators and the mixed-support cup at one coefficient stage.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
Source: latest blueprint, global operator Step 3
(blueprint: lem-fix-weil-operations-finite). -/
structure GlobalOperatorClauses
    (D : FiniteFieldDatum.{u}) (c₀ : D.CoefficientDatum)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (cpt : Compactification Y₀.hom) : Prop where
  F_M_isIso : ∀ (M : condensedStrictPair Λ (D.geometricFrobenius Y₀).hom),
    IsIso (ordinaryGlobalOperator D Y₀ Λ cpt M)
  F_c_M_isIso : ∀ (M : condensedStrictPair Λ (D.geometricFrobenius Y₀).hom),
    IsIso (compactGlobalOperator D Y₀ Λ cpt M)
  mixed_support_cup : ∀
      (hA : LocallyOfFiniteType (D.geometricFiber Y₀).hom)
      (hQ : QuasiCompact (D.geometricFiber Y₀).hom)
      (hS : IsSeparated (D.geometricFiber Y₀).hom)
      (hΛ : IsLocalizingAdmissibleCoefficient c₀.l Λ.X)
      (M N : condensedStrictPair Λ (D.geometricFrobenius Y₀).hom)
      (hM : condensedConstructibleFiniteTor Λ.X (D.geometricFiber Y₀).left
        M.obj.a.obj)
      (hN : condensedConstructibleFiniteTor Λ.X (D.geometricFiber Y₀).left
        N.obj.a.obj),
      (MonoidalCategoryStruct.tensorHom
        (compactGlobalOperator D Y₀ Λ cpt M)
        (ordinaryGlobalOperator D Y₀ Λ cpt N)) ≫
          globalMixedSupportCup D c₀ Λ hΛ
            (D.geometricFiber Y₀).hom
            hA hQ hS
            (CondensedFrobeniusTransport.compactification D Y₀ cpt)
            M.obj.a.obj hM N.obj.a.obj hN =
        globalMixedSupportCup D c₀ Λ hΛ
            (D.geometricFiber Y₀).hom
            hA hQ hS
            (CondensedFrobeniusTransport.compactification D Y₀ cpt)
            M.obj.a.obj hM N.obj.a.obj hN ≫
          compactGlobalOperatorTensor D Y₀ Λ cpt M N
  /-- On `s = Spec k` the canonical unit datum has scalar operator `id_R`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/lem-fix-weil-operations-finite.proof.md
  Source: latest blueprint, unit operator paragraph
  (blueprint: lem-fix-weil-operations-finite). -/
  id_R_on_unit :
    let Yunit : Over (Spec (.of D.k₀)) := Over.mk (𝟙 (Spec (.of D.k₀)))
    letI : LocallyOfFiniteType Yunit.hom := by
      dsimp [Yunit]
      infer_instance
    letI : QuasiCompact Yunit.hom := by
      dsimp [Yunit]
      infer_instance
    letI : IsSeparated Yunit.hom := by
      dsimp [Yunit]
      infer_instance
    ∀ (cunit : Compactification Yunit.hom),
      unitGlobalOperator D Yunit Λ cunit = 𝟙 _

end WeilConjectures
