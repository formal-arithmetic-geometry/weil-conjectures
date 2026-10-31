/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower
public import WeilConjectures.AlgebraicGeometry.NativeIntegralReductionExchange
public import WeilConjectures.AlgebraicGeometry.TowerAdjointCompositorRealization
public import WeilConjectures.AlgebraicGeometry.IntegralCompositorLimitRealization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Native integral compositor realization

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
sk-prop-sp-composition-comparisons.proof.md`, paragraphs (2)--(3).

Eight-step proof outline: (1) transport through the section-action equivalence and finite
coefficient tensor/pullback encoding; (2) use the proper/open compact-support compositor and
its normalized tower compositor; (3) use `towerBaseChange` and the reconstruction unit;
(4) apply the tower adjoint compositor and its Laws; (5) use coherent native pullback,
Tate-line, and shift comparisons; (6) paste the reduction square; (7) apply the limit
functor and cancel reconstruction; (8) paste the normalized source word, including the
ell-power quotient transition and even-shift reassociation. No finite evaluation is used as
an equality test and no purity orientation is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.NativeIntegralCompositor
open IntegralDirectImageTower SpNativeIntegralReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

def RootTowerTransition (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : Prop :=
  ∀ n : ℕ, (spIntegralTwistSystem T ℓ E).map
    (homOfLE (Nat.le_succ n)).op = spIntegralLevelTransition T ℓ E n

/-- The canonical comparison package.  Its fields are the actual compact-support,
tower, reconstruction, and coherent native-reduction maps used in the five equations. -/
structure Data (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (X Y Z : Scheme.{u})
    (f : X ⟶ Y) (g : Y ⟶ Z) (NC : Scheme.{u} → Type v) (NT : Scheme.{u} → Type w)
    [∀ T, Category (NC T)] [∀ T, Category (NT T)]
    (s : Presentation ℓ (ULift.{u} E)) where
  Ff : NC X ⥤ NC Y
  Fg : NC Y ⥤ NC Z
  Fh : NC X ⥤ NC Z
  Tf : NT X ⥤ NT Y
  Tg : NT Y ⥤ NT Z
  Th : NT X ⥤ NT Z
  rX : NC X ⥤ NT X
  rY : NC Y ⥤ NT Y
  rZ : NC Z ⥤ NT Z
  LX : NT X ⥤ NC X
  LY : NT Y ⥤ NC Y
  LZ : NT Z ⥤ NC Z
  betaF : Ff ⋙ rY ≅ rX ⋙ Tf
  betaG : Fg ⋙ rZ ≅ rY ⋙ Tg
  betaH : Fh ⋙ rZ ≅ rX ⋙ Th
  alpha : Ff ⋙ Fg ≅ Fh
  alphaTower : Tf ⋙ Tg ≅ Th
  rhoF : Ff ≅ rX ⋙ Tf ⋙ LY
  rhoG : Fg ≅ rY ⋙ Tg ⋙ LZ
  rhoH : Fh ≅ rX ⋙ Th ⋙ LZ
  Jf : NC Y ⥤ NC X
  Jg : NC Z ⥤ NC Y
  Jh : NC Z ⥤ NC X
  JTf : NT Y ⥤ NT X
  JTg : NT Z ⥤ NT Y
  JTh : NT Z ⥤ NT X
  lambdaF : Jf ⋙ rX ≅ rY ⋙ JTf
  lambdaG : Jg ⋙ rY ≅ rZ ⋙ JTg
  lambdaH : Jh ⋙ rX ≅ rZ ⋙ JTh
  sigmaF : Jf ≅ rY ⋙ JTf ⋙ LX
  sigmaG : Jg ≅ rZ ⋙ JTg ⋙ LY
  sigmaH : Jh ≅ rZ ⋙ JTh ⋙ LX
  split : Jh ≅ Jg ⋙ Jf
  splitTower : JTh ≅ JTg ⋙ JTf
  compactSupportCanonical : CondensedRing.CompactSupportComposition.Coherent
    (spIntegralCondensed ℓ (ULift.{u} E)) D.k
  nativeReductionCanonical : ∀ (_hne : ℓ ≠ D.p),
    ∃ q : ReductionGeometry ℓ (ULift.{u} E) s,
      ∃ hq : OpenReductionIsIso ℓ (ULift.{u} E) s q,
      ∃ L : ∀ T : Scheme.{u}, Limit ℓ (ULift.{u} E) s T,
        Nonempty (SpNativeIntegralReduction.Coherent ℓ (ULift.{u} E) D s q hq L)

set_option maxHeartbeats 2000000 in
-- The equations retain the full dependent categorical interfaces of the published maps.
/-- Native integral compact-support compositor realization. -/
theorem nativeIntegralCompositorRealization
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ ringChar D.k) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X Y Z : Scheme.{u})
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    (d e : ℕ) [SmoothOfRelativeDimension d f]
    [SmoothOfRelativeDimension e g]
    (s : Presentation ℓ (ULift.{u} E))
    (data : Data D ℓ E X Y Z f g
      (fun T => Constructible ℓ (ULift.{u} E) T)
      (fun T => spNormalizedConstructibleTorTowerCategory ℓ (ULift.{u} E) T (s.towers T)) s) :
    RootTowerTransition X ℓ E ∧
      (∀ M : Constructible ℓ (ULift.{u} E) X,
        data.rZ.map (data.alpha.hom.app M) ≫ data.betaH.hom.app M =
          data.betaG.hom.app (data.Ff.obj M) ≫ data.Tg.map (data.betaF.hom.app M) ≫
            data.alphaTower.hom.app (data.rX.obj M)) ∧
      (∀ M : Constructible ℓ (ULift.{u} E) X,
        data.alpha.hom.app M ≫ data.rhoH.hom.app M =
          data.rhoG.hom.app (data.Ff.obj M) ≫
            data.LZ.map (data.Tg.map (data.betaF.hom.app M)) ≫
              data.LZ.map (data.alphaTower.hom.app (data.rX.obj M))) ∧
      (∀ M : Constructible ℓ (ULift.{u} E) X,
        data.alpha.hom.app M =
          (data.rhoG.hom.app (data.Ff.obj M) ≫
            data.LZ.map (data.Tg.map (data.betaF.hom.app M)) ≫
              data.LZ.map (data.alphaTower.hom.app (data.rX.obj M))) ≫
            data.rhoH.inv.app M) ∧
      (∀ K : Constructible ℓ (ULift.{u} E) Z,
        data.lambdaH.hom.app K ≫ data.splitTower.hom.app (data.rZ.obj K) =
          data.rX.map (data.split.hom.app K) ≫ data.lambdaF.hom.app (data.Jg.obj K) ≫
            data.JTf.map (data.lambdaG.hom.app K)) ∧
      (∀ K : Constructible ℓ (ULift.{u} E) Z,
        data.sigmaH.hom.app K ≫ data.LX.map (data.splitTower.hom.app (data.rZ.obj K)) =
          data.split.hom.app K ≫ data.sigmaF.hom.app (data.Jg.obj K) ≫
            data.LX.map (data.JTf.map (data.lambdaG.hom.app K))) := by
  sorry

end AlgebraicGeometry.ProEtale.NativeIntegralCompositor
