/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.CondensedCoefficientComparisons
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # CondensedCompactSupportProjection

Source: blueprint sk-thm-purity-transport, Steps 2--3; the compact-support
realization prerequisite, proof Steps 6--17 (agent-formulated constructions).
(blueprint: def-pur-condensed-compact-support-projection). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

/- Canonical derived-unit factorization detects each comparison shift square on
K-injective representatives. The helper theorems are registered only within the proof. -/
private theorem rightComparison_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (G : DerivedCategory C ⥤ DerivedCategory D)
    [G.CommShift ℤ]
    (β : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ G)
    [NatTrans.CommShift β ℤ] (τ : F.rightDerivedFunctor ⟶ G)
    (h : F.rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh τ = β) :
    NatTrans.CommShift τ ℤ := by
  have : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift F
  have : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal)
      F.rightDerivedFunctorUnit) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ by
      obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
      dsimp
      infer_instance)
  have : NatTrans.CommShift
      (F.rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh τ) ℤ := by
    rw [h]
    infer_instance
  exact NatTrans.CommShift.of_comp_whiskerLeft_Qh F.rightDerivedFunctorUnit τ

private theorem rightNatIso_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) :
    NatTrans.CommShift (Functor.rightDerivedFunctorNatIso e).hom ℤ := by
  have : NatTrans.CommShift G.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift G
  apply rightComparison_shift F _
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
      DerivedCategory.Qh ≫ G.rightDerivedFunctorUnit) _
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso C (.up ℤ)) _

private theorem rightExactIso_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    NatTrans.CommShift F.rightDerivedFunctorIsoMapDerivedCategory.hom ℤ := by
  apply rightComparison_shift F _ F.mapDerivedCategoryFactorsh.inv _
  exact F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac

private theorem rightCompIso_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] :
    NatTrans.CommShift (Functor.rightDerivedFunctorCompIso F G).hom ℤ := by
  have : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift F
  have : NatTrans.CommShift G.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift G
  apply rightComparison_shift (F ⋙ G) _ (Functor.rightDerivedFunctorCompUnit F G) _
  simp [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso]

private theorem rightCompExactIso_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    NatTrans.CommShift (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G).hom ℤ := by
  have : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift F
  have : NatTrans.CommShift
      (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G) ℤ := by
    dsimp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit]
    infer_instance
  apply rightComparison_shift (F ⋙ G) _
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G) _
  simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso]

namespace WeilConjectures.CompactSupportCondensedRealization

universe a av b bv d dv e ev h hv z zv

/-- Pasting the proper coefficient mate with the open coefficient square.
Source: blueprint proof Step 6; archived ChangeOfCoefficients.lean
(blueprint: def-pur-condensed-compact-support-projection). -/
def pasteScalar {C : Type a} {D : Type b} {H : Type d}
    {C' : Type e} {D' : Type h} {H' : Type z}
    [Category.{av} C] [Category.{bv} D] [Category.{dv} H]
    [Category.{ev} C'] [Category.{hv} D'] [Category.{zv} H']
    (j : C ⥤ D) (r : D ⥤ H) (j' : C' ⥤ D') (r' : D' ⥤ H')
    (tx : C ⥤ C') (tz : D ⥤ D') (ty : H ⥤ H')
    (p : r ⋙ ty ⟶ tz ⋙ r') (q : j ⋙ tz ⟶ tx ⋙ j') :
    (j ⋙ r) ⋙ ty ⟶ tx ⋙ (j' ⋙ r') :=
  (Functor.associator j r ty).hom ≫ Functor.whiskerLeft j p ≫
    (Functor.associator j tz r').inv ≫ Functor.whiskerRight q r' ≫
      (Functor.associator tx j' r').hom

/-- Shorthand for the existing sectionwise finite-limit preservation instances.
Source: blueprint proof Steps 6 and 13; archived coefficient-change hypotheses
(blueprint: def-pur-condensed-compact-support-projection). -/
abbrev FlatCoefficientMap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] : Prop :=
  ∀ W : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a W))

section Projection
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [FlatCoefficientMap a]

/-- The actual small-Hom-universe derived extension of condensed coefficients.
Source: blueprint proof Steps 6 and 13
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalar (W : Scheme.{u}) :
    DerivedCategory
        (Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) ⥤
      DerivedCategory
        (Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ' W)) :=
  (Mod.extendScalars (coefficientMap a W)).leftDerivedFunctor

/-- The tensor shift is induced by the exact restriction-of-scalars adjunction.
Source: blueprint proof Step 17; the canonical derived tensor adjunction
(blueprint: def-pur-condensed-compact-support-projection). -/
instance condensedScalarShift (W : Scheme.{u}) : (condensedScalar a W).CommShift ℤ :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a W)).leftAdjointCommShift ℤ

/-- The canonical coefficient projection for a fixed compactification, in proper-then-open
order, exactly as in the archived condensed module-object construction.
Source: archived ChangeOfCoefficients.lean, derivedLowerShriekHom; blueprint proof Step 6
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c ⋙
        (condensedScalar a Y) ⟶
      (condensedScalar a X) ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c :=
  pasteScalar
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' c.g).rightDerivedFunctor
    (condensedScalar a X) (condensedScalar a c.Z) (condensedScalar a Y)
    (CondensedRing.derivedPushHom a c.g)
    (CondensedRing.derivedOpenImmersionShriekIso a c.i).hom

/-- The inherited shift of the archived proper/open support composite.
Source: blueprint proof Step 17; archived derived open and proper operations
(blueprint: def-pur-condensed-compact-support-projection). -/
instance condensedSupportShift
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ₀ c).CommShift ℤ :=
  inferInstance

/-- The original condensed scalar projection respects the canonical derived shifts.
Source: blueprint proof Step 17; derived adjunction shift compatibility
(blueprint: def-pur-condensed-compact-support-projection).
Proof: the ordinary tensor and open squares commute with cochain shifts. Their
universal derived units and counits fix the same shifted square. Taking the proper
adjunction mate preserves this equation, as does the open comparison and their paste.
The zero and addition shift coherences descend from those on cochain complexes. -/
theorem condensedProjection_commShift {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : NatTrans.CommShift (condensedProjection a c) ℤ := by
  let : (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.CommShift ℤ :=
    condensedScalarShift a X
  let : (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.CommShift ℤ :=
    condensedScalarShift a Y
  let : (Mod.extendScalars (coefficientMap a c.Z)).leftDerivedFunctor.CommShift ℤ :=
    condensedScalarShift a c.Z
  have : (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a X)).CommShift ℤ :=
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a X)).commShift_of_rightAdjoint ℤ
  have : (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a Y)).CommShift ℤ :=
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a Y)).commShift_of_rightAdjoint ℤ
  have : (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a c.Z)).CommShift ℤ :=
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a c.Z)).commShift_of_rightAdjoint ℤ
  have := rightNatIso_shift (CondensedRing.comapLowerStarIso a c.g)
  have := rightExactIso_shift
    (Mod.comap (coefficientMap a c.Z) :
      Mod (Sheaf (ProEt.topology c.Z) Ab.{u + 1}) (condensedRingObj Λ' c.Z) ⥤
        Mod (Sheaf (ProEt.topology c.Z) Ab.{u + 1}) (condensedRingObj Λ c.Z))
  have := rightCompIso_shift (Mod.comap (coefficientMap a c.Z))
    (CondensedRing.lowerStar Λ c.g)
  have := rightCompExactIso_shift (CondensedRing.lowerStar Λ' c.g)
    (Mod.comap (coefficientMap a Y))
  have : NatTrans.CommShift (CondensedRing.derivedComapLowerStarIso a c.g).hom ℤ := by
    dsimp only [CondensedRing.derivedComapLowerStarIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  have : NatTrans.CommShift (CondensedRing.derivedComapUpperStarIso a c.i).hom ℤ := by
    dsimp only [CondensedRing.derivedComapUpperStarIso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have : (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
      Λ c.i).CommShift ℤ := by
    dsimp only [CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction]
    infer_instance
  have : (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
      Λ' c.i).CommShift ℤ := by
    dsimp only [CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction]
    infer_instance
  have hp : NatTrans.CommShift (CondensedRing.derivedPushHom a c.g) ℤ := by
    dsimp [CondensedRing.derivedPushHom, Adjunction.pushHomOfComapIso,
      mateEquiv, TwoSquare.natTrans, TwoSquare.mk]
    infer_instance
  have ho : NatTrans.CommShift (CondensedRing.derivedOpenImmersionShriekIso a c.i).hom ℤ := by
    dsimp [CondensedRing.derivedOpenImmersionShriekIso, conjugateIsoEquiv,
      conjugateEquiv, mateEquiv, Iso.homCongr, TwoSquare.equivNatTrans,
      TwoSquare.natTrans, TwoSquare.mk]
    infer_instance
  unfold condensedProjection pasteScalar
  infer_instance


variable {Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ''] [IsCommMonObj Λ''] (b : Λ' ⟶ Λ'') [IsMonHom b]
  [FlatCoefficientMap b]
  [FlatCoefficientMap (a ≫ b)]

/-- Tensor transitivity is uniquely induced by the actual restriction compositor.
Source: blueprint proof Steps 9 and 13; Stacks 06YY
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalarComp (W : Scheme.{u}) :
    condensedScalar a W ⋙ condensedScalar b W ≅ condensedScalar (a ≫ b) W :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a W)).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b W))).leftAdjointUniq
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (a ≫ b) W)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso
          (Mod.comapCongr (coefficientMap_comp a b W) ≪≫ Mod.comapComp _ _) ≪≫
        Functor.mapDerivedCategoryCompIso
          _ _))

/-- The original coefficient projections satisfy the full tensor cocycle, including
an arbitrary finite-valued closure coefficient as the last ring.
Source: blueprint proof Steps 9, 12--13; ringed coefficient projection cocycle
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two paths under the scalar adjunctions. Their transposes are
the same proper counit followed by the same open unit and the restriction compositor.
Ordinary adjunction triangle identities give equality before derivation. Universal
derived units and counits descend it, and proper/open pasting gives the displayed
cocycle on all objects. The closure case uses the identical original maps. -/
theorem condensedProjection_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      :
    (condensedScalar b Y).map ((condensedProjection a c).app K) ≫
        (condensedProjection b c).app ((condensedScalar a X).obj K) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification Λ'' c).map
          ((condensedScalarComp a b X).hom.app K) =
      (condensedScalarComp a b Y).hom.app
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K) ≫
        (condensedProjection (a ≫ b) c).app K := by
  sorry

/-- Identity scalar extension is exact, with its actual tensor-unit normalization.
Source: blueprint proof Step 9; Stacks 06YY
(blueprint: def-pur-condensed-compact-support-projection).
Proof: the coefficient map is the identity by functoriality of coefficient pullback.
The ordinary scalar adjunction identifies its left adjoint with the identity by
Mod.extendScalarsId. Transport finite-limit preservation along that isomorphism. -/
theorem identityScalar_flat (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] (W : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap (𝟙 Λ₀) W)) := by
  exact preservesFiniteLimits_of_natIso
    (Mod.extendScalarsIsoOfEq (coefficientMap_id (Λ := Λ₀) W) ≪≫
      Mod.extendScalarsId).symm

attribute [instance] identityScalar_flat

/-- The derived scalar unit is induced by the original restriction identity.
Source: blueprint proof Step 9; Stacks 06YY
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalarId (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] (W : Scheme.{u}) :
    condensedScalar (𝟙 Λ₀) W ≅ 𝟭 _ :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (𝟙 Λ₀) W)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso
          (Mod.comapCongr (coefficientMap_id (Λ := Λ₀) W) ≪≫ Mod.comapId _) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm)

/-- The original projection at identity coefficients is precisely the tensor unit.
Source: blueprint proof Step 9; ringed coefficient projection cocycle
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the proper projection at the identity map. Both routes have the
original proper counit as their transpose; the open comparison has the original
open unit. Adjunction uniqueness and the ordinary scalar identity identify the
pasted projection with the displayed tensor-unit equation. -/
theorem condensedProjection_id (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X))) :
    (condensedProjection (𝟙 Λ₀) c).app K ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification Λ₀ c).map
          ((condensedScalarId Λ₀ X).hom.app K) =
      (condensedScalarId Λ₀ Y).hom.app
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ₀ c).obj K) := by
  sorry

end Projection

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The exact open adjunction expressed using the actual left-derived pullback.
Source: archived open-immersion derived adjunction; blueprint Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldOpenAdjunction {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory ⊣
      (CondensedRing.upperStar Λ j).leftDerivedFunctor :=
  (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm

/-- The restriction normalization of a proper refinement, before its invertibility
is asserted. Source: blueprint proof Steps 15--16
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      :=
  ((eqToIso (congrArg (fun h : X ⟶ d.Z ↦
      (CondensedRing.upperStar Λ h).leftDerivedFunctor) r.i_hom.symm)) ≪≫
    CondensedRing.leftDerivedUpperStarComp Λ c.i r.hom).hom.app
      ((CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor.obj
        ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K)) ≫
    (CondensedRing.upperStar Λ c.i).leftDerivedFunctor.map
      ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ r.hom).counit.app
        ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K))

/-- The proper/open refinement is uniquely fixed by the original open unit.
Source: blueprint proof Steps 15--16; Stacks 0F7B
(blueprint: def-pur-condensed-compact-support-projection).
Proof: restriction of direct image to the open is the direct image of the open
restriction, since open extension is an exact left adjoint. In the pulled-back square
the section defined by the refinement is clopen. Extension by zero restricts to the
original input on that component and vanishes on its complement. Thus the displayed
restriction normalization is invertible. The open Hom bijection supplies a unique
arrow with this transpose; no proper base change outside the open is needed. -/
theorem fieldProperOpen_existsUnique {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    ∃! e : (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory.obj K.obj ⟶
        (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor.obj
          ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj),
      (fieldOpenAdjunction Λ d.i).homEquiv _ _ e ≫
          fieldProperOpenRestriction Λ r K.obj =
        (fieldOpenAdjunction Λ c.i).unit.app K.obj := by
  sorry

/-- The unit-normalized refinement arrow, without an arbitrary splitting.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpen {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory.obj K.obj ⟶
      (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor.obj
        ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) :=
  (fieldProperOpen_existsUnique Λ r K).exists.choose

/-- Proper-image composition is the conjugate of the actual pullback composition.
Source: archived module-object derived operations; blueprint Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldPushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
        (CondensedRing.lowerStar Λ g).rightDerivedFunctor ≅
      (CondensedRing.lowerStar Λ (f ≫ g)).rightDerivedFunctor :=
  conjugateIsoEquiv
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f))
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (CondensedRing.leftDerivedUpperStarComp Λ f g)

/-- The canonical refinement component, in the direction from coarser to finer.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinementApp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ d).obj K.obj ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K.obj :=
  (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor.map
      (fieldProperOpen Λ r K) ≫
    (fieldPushComp Λ r.hom d.g).hom.app
      ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) ≫
    (eqToIso (congrArg (fun h : c.Z ⟶ Y ↦
      (CondensedRing.lowerStar Λ h).rightDerivedFunctor) r.hom_g)).hom.app
        ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj)

/-- Naturality of the fixed refinement components.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two composites under the open adjunction. Naturality of its
unit and of the proper counit makes the transposes equal; the Hom bijection then
gives the equation. Proper-image composition is itself natural. -/
theorem fieldRefinementApp_naturality {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    {K L : BoundedConstructible (condensedRingObj Λ X)} (v : K ⟶ L) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ d).map v.hom ≫
        fieldRefinementApp Λ r L =
      fieldRefinementApp Λ r K ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).map v.hom := by
  sorry

/-- The specified condensed refinement as a whole natural transformation.
Source: blueprint proof Steps 15--16
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ d ⟶
      (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ c where
  app := fieldRefinementApp Λ r
  naturality := fun _ _ v ↦ fieldRefinementApp_naturality Λ r v

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [FlatCoefficientMap a]

/-- Coefficient extension commutes with the original refinement map itself.
Source: blueprint proof Steps 15--16; proper/open coefficient mate pasting
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two composites under the open adjunction. Coefficient restriction
commutes with the original open unit and the proper counit, so both transposes are
the same section-normalized restriction map. Uniqueness in the open Hom bijection
and the proper compositor identify the original maps. This applies verbatim to the
finite-valued closure coefficient and requires no new choice of comparison arrow. -/
theorem condensedProjection_refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X))
    (hK : boundedConstructible (condensedRingObj Λ' X) ((condensedScalar a X).obj K.obj)) :
    (condensedScalar a Y).map ((fieldRefinement Λ r).app K) ≫
        (condensedProjection a c).app K.obj =
      (condensedProjection a d).app K.obj ≫
        (fieldRefinement Λ' r).app ⟨(condensedScalar a X).obj K.obj, hK⟩ := by
  sorry

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The field refinement construction respects identities with its original unit.
Source: blueprint proof Steps 15--16; Stacks 0F7B
(blueprint: def-pur-condensed-compact-support-projection).
Proof: apply the open Hom bijection to the identity refinement. Its defining
normalization is the original open unit, so the unique arrow and the proper
identity compositor reduce to the identity transformation. -/
theorem fieldRefinement_id {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    fieldRefinement Λ (Compactification.Refinement.id c) = 𝟙 _ := by
  sorry

/-- The field and closure refinements have the same composition normalization.
Source: blueprint proof Steps 15--16; Stacks 0F7B and 07A7
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two iterated maps under the open adjunction. Proper counit
pasting identifies their common transpose with the composite-refinement unit.
Uniqueness gives equality; the proper-image mate compositor is associative. -/
theorem fieldRefinement_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    fieldRefinement Λ (r.comp s) = fieldRefinement Λ s ≫ fieldRefinement Λ r := by
  sorry

end WeilConjectures.CompactSupportCondensedRealization
