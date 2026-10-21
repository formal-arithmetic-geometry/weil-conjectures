/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.Paper.KFlatRingedToposPullback

/-! # Pasting constant-coefficient pro-etale pullback squares

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D,
`lemma-derived-pullback-composition`; the two-square deduction in the node
(blueprint: lem-pur-factorized-pullback-square-pasting).

## Main statements

- `proEtaleFactorizedPullback_pasting`: equality of the two canonical derived paths.
- `proEtaleFactorizedPullback_pasting_representatives`: their termwise normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The ordinary compositor with the published unit-section normalization.
The unit-section equation in the cited theorem determines its maps: the adjunction
identifies a map out of pullback with its composite with the unit. Thus this choice
selects the canonical isomorphism, rather than an unspecified witness of existence.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingOrdinaryComposition
    {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (k : Y ⟶ X) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h ≅
      proEtaleConstantRingPullback A (h ≫ k) :=
  (Classical.choose (proEtaleConstantRingPullbackComposition_ordinary h k A)).symm

/-- The ordinary square comparison, with the specified equality transport.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingOrdinarySquare
    {X Y : Scheme.{u}} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A vY ⋙ proEtaleConstantRingPullback A u ≅
      proEtaleConstantRingPullback A u ⋙ proEtaleConstantRingPullback A vX :=
  proEtalePastingOrdinaryComposition u vY A ≪≫
    eqToIso (congrArg (proEtaleConstantRingPullback A) e) ≪≫
      (proEtalePastingOrdinaryComposition vX u A).symm

/-- The left ordinary path in the factorized-square pasting equation.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingOrdinaryLeft
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A (rY ≫ sY) ⋙ proEtaleConstantRingPullback A u ≅
      proEtaleConstantRingPullback A u ⋙
        (proEtaleConstantRingPullback A sX ⋙ proEtaleConstantRingPullback A rX) :=
  Functor.isoWhiskerRight (proEtalePastingOrdinaryComposition rY sY A).symm
      (proEtaleConstantRingPullback A u) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingPullback A sY) 
      (proEtalePastingOrdinarySquare u rX rY er A) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (proEtalePastingOrdinarySquare u sX sY es A)
      (proEtaleConstantRingPullback A rX) ≪≫
    Functor.associator _ _ _

/-- The right ordinary path in the factorized-square pasting equation.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingOrdinaryRight
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A (rY ≫ sY) ⋙ proEtaleConstantRingPullback A u ≅
      proEtaleConstantRingPullback A u ⋙
        (proEtaleConstantRingPullback A sX ⋙ proEtaleConstantRingPullback A rX) :=
  proEtalePastingOrdinarySquare u (rX ≫ sX) (rY ≫ sY) et A ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingPullback A u) 
      (proEtalePastingOrdinaryComposition rX sX A).symm

/-- The derived square comparison, with the specified equality transport.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingDerivedSquare
    {X Y : Scheme.{u}} (u : X ⟶ Y) (vX : X ⟶ X) (vY : Y ⟶ Y)
    (e : u ≫ vY = vX ≫ u) (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A vY ⋙ proEtaleConstantRingDerivedPullback A u ≅
      proEtaleConstantRingDerivedPullback A u ⋙ proEtaleConstantRingDerivedPullback A vX :=
  proEtaleConstantRingPullbackComposition u vY A ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e) ≪≫
      (proEtaleConstantRingPullbackComposition vX u A).symm

/-- The left derived path in the factorized-square pasting equation.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingDerivedLeft
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A (rY ≫ sY) ⋙ proEtaleConstantRingDerivedPullback A u ≅
      proEtaleConstantRingDerivedPullback A u ⋙
        (proEtaleConstantRingDerivedPullback A sX ⋙ proEtaleConstantRingDerivedPullback A rX) :=
  Functor.isoWhiskerRight (proEtaleConstantRingPullbackComposition rY sY A).symm
      (proEtaleConstantRingDerivedPullback A u) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A sY) 
      (proEtalePastingDerivedSquare u rX rY er A) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (proEtalePastingDerivedSquare u sX sY es A)
      (proEtaleConstantRingDerivedPullback A rX) ≪≫
    Functor.associator _ _ _

/-- The right derived path in the factorized-square pasting equation.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting). -/
def proEtalePastingDerivedRight
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A (rY ≫ sY) ⋙ proEtaleConstantRingDerivedPullback A u ≅
      proEtaleConstantRingDerivedPullback A u ⋙
        (proEtaleConstantRingDerivedPullback A sX ⋙ proEtaleConstantRingDerivedPullback A rX) :=
  proEtalePastingDerivedSquare u (rX ≫ sX) (rY ≫ sY) et A ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A u) 
      (proEtaleConstantRingPullbackComposition rX sX A).symm

/-- Pasting the two canonical commuting-square comparisons agrees with the
comparison of their composite endomorphisms, as natural transformations.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting).
Proof: (1) The constant-ring-map and constant-coefficient-composition nodes identify
all coefficient maps with the specified constant-section maps, including composites.
(2) Equality elimination gives substitution for each index of the canonical compositor;
composite, inverse and whiskered equality transports are therefore the expected ones.
Proof irrelevance identifies any supplied outer-square equality with the pasted equality.
(3) Apply lem-trf-derived-pullback-coherence to (u,rY,sY). Expand C_r and cancel the
adjacent inverse compositors, transporting along er. The left path becomes
(P_rX C_s)(c_rX,u P_sY)c_urX,sY c_u,tY^{-1}.
(4) Apply coherence to (rX,u,sY), expand C_s and cancel its inverse compositor.
Transport along es to obtain (P_rX c_sX,u)c_rX,usX c_u,tY^{-1}.
(5) Apply coherence to (rX,sX,u). This is (d_X P_u) C_t, with the outer transport
from step (2). The associators only reassociate the three evaluated functors.
Extensionality in the derived object gives equality of natural transformations. -/
theorem proEtaleFactorizedPullback_pasting
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u)
    (A : Type u) [CommRing A] [Finite A] :
    (proEtalePastingDerivedLeft u rX sX rY sY er es A).hom =
      (proEtalePastingDerivedRight u rX sX rY sY et A).hom := by
  sorry

/-- On a K-flat complex with flat terms, each path is the class of its termwise
ordinary pasting map. `mapDerivedCategorySquareIso` is the canonical localization
of the termwise map, with source and target composition factorization isomorphisms;
the final whiskered comparison expands the target into its three pullback functors.
Source: Stacks Tag 0D6D (blueprint: lem-pur-factorized-pullback-square-pasting).
Proof: (6) Apply lem-weil-pbc-ringed-pullback-preserves-kflat repeatedly: all successive
ordinary pullbacks of K remain K-flat with flat terms. The normalized compositor in
lem-weil-pbc-proetale-derived-pullback-composition is the localization of its ordinary
termwise map; the published ordinary comparison has exactly its unit normalization.
Localization preserves inverses, so inverse compositors have the inverse termwise maps.
Exact termwise descent in def-weil-pbc-proetale-operations identifies whiskering with
ordinary pullback of those maps. Equality elimination identifies all equality transports
with the termwise transports, starting with identity maps in the reflexive case.
Compose these identities for each path, including the canonical associators. This gives
the two component formulas below. No boundedness assumption on K is needed. -/
theorem proEtaleFactorizedPullback_pasting_representatives
    {X Y : Scheme.{u}} (u : X ⟶ Y) (rX sX : X ⟶ X) (rY sY : Y ⟶ Y)
    (er : u ≫ rY = rX ≫ u) (es : u ≫ sY = sX ≫ u)
    (et : u ≫ (rY ≫ sY) = (rX ≫ sX) ≫ u)
    (A : Type u) [CommRing A] [Finite A]
    (K : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
    (hK : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt)
      (ProEt.topology Y) (proEtaleConstantRing Y A) K)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Y.ProEt) (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (K.X n)) :
    (proEtalePastingDerivedLeft u rX sX rY sY er es A).hom.app
        (DerivedCategory.Q.obj K) =
      (Functor.mapDerivedCategorySquareIso
          (F₁ := proEtaleConstantRingPullback A (rY ≫ sY))
          (F₂ := proEtaleConstantRingPullback A u)
          (G₁ := proEtaleConstantRingPullback A u)
          (G₂ := proEtaleConstantRingPullback A sX ⋙ proEtaleConstantRingPullback A rX)
          (proEtalePastingOrdinaryLeft u rX sX rY sY er es A) ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A u)
          (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A sX)
            (proEtaleConstantRingPullback A rX))).hom.app (DerivedCategory.Q.obj K) ∧
    (proEtalePastingDerivedRight u rX sX rY sY et A).hom.app
        (DerivedCategory.Q.obj K) =
      (Functor.mapDerivedCategorySquareIso
          (F₁ := proEtaleConstantRingPullback A (rY ≫ sY))
          (F₂ := proEtaleConstantRingPullback A u)
          (G₁ := proEtaleConstantRingPullback A u)
          (G₂ := proEtaleConstantRingPullback A sX ⋙ proEtaleConstantRingPullback A rX)
          (proEtalePastingOrdinaryRight u rX sX rY sY et A) ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A u)
          (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A sX)
            (proEtaleConstantRingPullback A rX))).hom.app (DerivedCategory.Q.obj K) := by
  sorry

end AlgebraicGeometry.Scheme
