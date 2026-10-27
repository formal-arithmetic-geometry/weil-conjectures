/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.FiniteFreeCoefficientExtension
public import Sheaf.SixFunctors.CompactCoefficientComposition
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import WeilConjectures.Compactification.Triangle
public import Sheaf.Paper.SystemCompactificationProjectionSubstitution

import all Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.VaryingRingOperations
import Sheaf.Paper.FiniteFreeCompactSupportComposition
import all Sheaf.Paper.CompactSupportSiteCoherence
import all Sheaf.Paper.CanonicalOriginCompactSupportComposition

/-! # Finite-free compact-support coefficient comparison and composition

Source: blueprint main-20261015, lem-coef-rational-operations, proof paragraph 8;
Stacks Project, Tags 0F7J, 0F7B, 06YY and 07A6
(blueprint: lem-coef-finite-free-compact-composition).

The system maps below are maps in the ordinary derived category of module sheaves
on the vertical sequence site, before evaluation or inverse limit. Coefficient
comparison is a scalar-adjunction mate. Composition is the proper/open word in a
triangle, transported through the graph common refinements of compactifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard
  DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.constantSheaf

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.SemilinearSections

namespace WeilConjectures.FiniteFreeCompactComposition

private local instance fixedSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _


section TensorTransportHelpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian

private def scalarAdj {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :
    (FiniteFreeCoefficients.Sites.scalar true φ W) ⊣
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) φ :=
  Adjunction.ofIsRightAdjoint _

private def tensorModelIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {W : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ W K) :
    (FiniteFreeCoefficients.Sites.scalar true φ W).obj K ≅ M.obj := by
  let ad := scalarAdj φ W
  let g := (ad.homEquiv K M.obj).symm M.unit
  have hu : Sheaf.IsDerivedBaseChange (ad.unit.app K) := by
    intro N
    change Function.Bijective (fun g ↦ ad.unit.app K ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) φ).map g)
    have he : (fun g : (FiniteFreeCoefficients.Sites.scalar true φ W).obj K ⟶ N ↦
        ad.unit.app K ≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) φ).map g) =
          ad.homEquiv K N := by
      funext g
      exact (ad.homEquiv_unit K N g).symm
    rw [he]
    exact (ad.homEquiv K N).bijective
  have hg : ad.unit.app K ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) φ).map g = M.unit := by
    change ad.homEquiv K M.obj g = M.unit
    exact Equiv.apply_symm_apply _ _
  have : IsIso g := Sheaf.IsDerivedBaseChange.isIso hu M.universal g hg
  exact asIso g

private theorem tensorModelIso_unit {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {W : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ W K) :
    (scalarAdj φ W).unit.app K ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) φ).map
        (tensorModelIso M).hom = M.unit := by
  change (scalarAdj φ W).homEquiv K M.obj
    (((scalarAdj φ W).homEquiv K M.obj).symm M.unit) = M.unit
  exact Equiv.apply_symm_apply _ _

attribute [local irreducible] tensorModelIso

private theorem tensorModelComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] {φ : A →+* B} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    (tensorModelIso N).hom ≫ compactSupportCoefficientComparison c M N =
      AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true φ c K ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          (tensorModelIso M).hom := by
  apply ((scalarAdj φ Y).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]
  simp only [CategoryTheory.Functor.map_comp, ← Category.assoc]
  rw [tensorModelIso_unit]
  have hn := Equiv.apply_symm_apply (Equiv.ofBijective _ (N.universal _))
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map M.unit ≫
      (compactSupportRestrictionIso φ c).hom.app M.obj)
  change N.unit ≫ _ = _ at hn
  change N.unit ≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
    (compactSupportCoefficientComparison c M N) = _ at hn
  rw [hn]
  dsimp only [AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap,
    AlgebraicGeometry.FiniteFreeCompactSupport.support,
    FiniteFreeCoefficients.Sites.scalar]
  erw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  erw [Category.assoc, ← (compactSupportRestrictionIso φ c).hom.naturality]
  erw [← CategoryTheory.Functor.map_comp_assoc, tensorModelIso_unit]

private theorem tensorModelMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {W : Scheme.{u}}
    {K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ W K) (N : CoefficientTensorModel φ W L) (v : K ⟶ L) :
    (tensorModelIso M).hom ≫ M.map N v =
      (FiniteFreeCoefficients.Sites.scalar true φ W).map v ≫ (tensorModelIso N).hom := by
  apply ((scalarAdj φ W).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]
  simp only [CategoryTheory.Functor.map_comp, ← Category.assoc]
  rw [tensorModelIso_unit]
  have hn := Equiv.apply_symm_apply (Equiv.ofBijective _ (M.universal N.obj))
    (v ≫ N.unit)
  change M.unit ≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) φ).map
    (M.map N v) = v ≫ N.unit at hn
  rw [hn]
  have h := (scalarAdj φ W).unit.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at h
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← Category.assoc,
    ← h, Category.assoc, tensorModelIso_unit]

private theorem tensorModelComparison_isIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] {φ : A →+* B} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K))
    [hcanonical : IsIso
      (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true φ c K)] :
    IsIso (compactSupportCoefficientComparison c M N) := by
  have h := tensorModelComparison c M N
  have : IsIso ((tensorModelIso N).hom ≫ compactSupportCoefficientComparison c M N) := by
    rw [h]
    exact IsIso.comp_isIso'
      (inferInstanceAs (IsIso
        (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true φ c K)))
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).mapIso
        (tensorModelIso M)).isIso_hom
  exact IsIso.of_isIso_comp_left (tensorModelIso N).hom _

attribute [local irreducible] scalarAdj

attribute [local irreducible] coherenceCompactificationChange coherenceBoundaryIso

private theorem self_change_of_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {a : C} {b : D} (j : F.obj a ≅ b) (x : a ⟶ a) (r : b ⟶ b)
    (hx : x = 𝟙 _) (hs : F.map x ≫ j.hom = j.hom ≫ r) : r = 𝟙 _ := by
  subst x
  apply (cancel_epi j.hom).mp
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    using hs.symm

private theorem compactificationChange_self (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceCompactificationChange A c c L).hom = 𝟙 _ := by
  apply self_change_of_square
    (DerivedCategory.Plus.ι ⋙ coherenceSiteFunctor A Y)
    ((coherenceBoundaryIso A c).app L)
    ((coherenceEtaleChangeIso A c c).hom.app L)
    (coherenceCompactificationChange A c c L).hom
  · simpa only [coherenceEtaleChangeIso, coherenceEtaleFunctor, Iso.refl_hom,
      NatTrans.id_app] using congrArg (fun e ↦ e.hom.app L)
        (Etale.rightDerivedLowerShriekOfCompactificationPlusIso_refl A c)
  · exact compactification_change_square A c c L

attribute [local irreducible] originCompositionModel

private theorem chosen_compositor_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    coherenceProEtaleCompositor A
        (HasCompactification.compactification f) (HasCompactification.compactification g)
        (HasCompactification.compactification (f ≫ g)) L =
      (coherenceChosenProEtaleCompositorComponent A f g L).hom := by
  dsimp only [coherenceProEtaleCompositor, coherenceCompositionData,
    coherenceCompositionDataOfChoice, CoherencePastingData.proMap, coherenceSixMap]
  rw [compactificationChange_self, compactificationChange_self,
    compactificationChange_self]
  simp only [Category.id_comp, Category.comp_id, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]

private theorem conjugate_naturality {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (η : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    F.map e.inv ≫ η.app X ≫ G.map e.hom = η.app Y := by
  rw [← η.naturality, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

attribute [local irreducible] originCompositionAmbient

private theorem originConjugation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (η : (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⟶
      (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (α : (FiniteFreeCoefficients.Sites.nu A X).obj L.obj ≅ K) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map α.inv) ≫
      η.app ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map α.hom =
      η.app ⟨K, hK⟩ := by
  let e : (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L ≅
      ⟨K, hK⟩ := ObjectProperty.isoMk _ α
  exact conjugate_naturality η e

attribute [local irreducible] comparisonUpperStarPlusEtaleOrigin

private theorem ambient_model (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
      (originCompositionAmbient A f g).hom = (originCompositionModel A f g).hom := by
  unfold originCompositionAmbient
  exact preimage_whiskerLeft _ _

attribute [local semireducible] comparisonUpperStarPlusEtaleOrigin

private theorem composition_chosen (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (α : (FiniteFreeCoefficients.Sites.nu A X).obj L.obj ≅ K) :
    AlgebraicGeometry.FiniteFreeCompactSupport.composition true A
        (HasCompactification.compactification f) (HasCompactification.compactification g)
        (HasCompactification.compactification (f ≫ g)) L α =
      (originCompositionAmbient A f g).hom.app ⟨K, hK⟩ := by
  have hm := (congr_app (ambient_model A f g) L).symm
  change (originCompositionModel A f g).hom.app L =
    (originCompositionAmbient A f g).hom.app
      ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) at hm
  unfold AlgebraicGeometry.FiniteFreeCompactSupport.composition
  dsimp only [AlgebraicGeometry.FiniteFreeCompactSupport.compositionReal]
  erw [chosen_compositor_eq]
  dsimp only [coherenceChosenProEtaleCompositorComponent, coherenceEvaluateTriple,
    coherenceChosenProEtaleCompositorIso]
  change (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map α.inv) ≫
      (originCompositionModel A f g).hom.app L ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map α.hom = _
  erw [hm]
  exact originConjugation A f g (originCompositionAmbient A f g).hom hK L α

private theorem compositor_equation_transport {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {a b : C} {α α' : a ⟶ b} (ha : α = α')
    {x y z : D} {β β' : y ⟶ z} (hb : β = β')
    (t : F.obj b ⟶ z) (r : F.obj a ⟶ x) (s : x ⟶ y)
    (h : F.map α ≫ t = r ≫ s ≫ β) :
    F.map α' ≫ t = r ≫ s ≫ β' := by
  subst α'
  subst β'
  exact h

private theorem tensorComposition_transport {C D E : Type*}
    [Category* C] [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    {m₀ m₁ : C} {n₀ n₁ : D} {p₀ p₁ q₀ q₁ : E}
    (um : m₀ ≅ m₁) (un : n₀ ≅ n₁) (up : p₀ ≅ p₁) (uq : q₀ ≅ q₁)
    (cf : n₀ ⟶ F.obj m₀) (af : n₁ ⟶ F.obj m₁)
    (cg : p₀ ⟶ G.obj n₀) (ag : p₁ ⟶ G.obj n₁)
    (ch : q₀ ⟶ H.obj m₀) (ah : q₁ ⟶ H.obj m₁)
    (γ₀ : G.obj (F.obj m₀) ⟶ H.obj m₀)
    (γ₁ : G.obj (F.obj m₁) ⟶ H.obj m₁) (s : p₀ ⟶ q₀) (v : p₁ ⟶ q₁)
    (hf : un.hom ≫ af = cf ≫ F.map um.hom)
    (hg : up.hom ≫ ag = cg ≫ G.map un.hom)
    (hh : uq.hom ≫ ah = ch ≫ H.map um.hom)
    (hv : up.hom ≫ v = s ≫ uq.hom)
    (hn : G.map (F.map um.hom) ≫ γ₁ = γ₀ ≫ H.map um.hom)
    (hc : s ≫ ch = cg ≫ G.map cf ≫ γ₀) :
    ag ≫ G.map af ≫ γ₁ = v ≫ ah := by
  apply (cancel_epi up.hom).mp
  simp only [← Category.assoc]
  rw [hg]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, hf, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hn, ← reassoc_of% hc, ← hh, ← reassoc_of% hv]

attribute [local irreducible] _root_.DerivedCategory _root_.instCategoryDerivedCategory

/-- Universal tensor presentations preserve any canonical coefficient-composition square.
The witness choices remain inside this proof; the constructed tensor isomorphisms are uniquely
specified by their units. Working over abstract rings avoids unfolding valuation quotients. -/
private theorem tensorPresentation_composition {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K))
    (P₀ : CoefficientTensorModel φ Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K)))
    (Q : CoefficientTensorModel φ Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj K))
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X M.obj)
    (hc : ∀
      (KA : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (α : (FiniteFreeCoefficients.Sites.nu A X).obj KA.obj ≅ K)
      (KB : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
      (β : (FiniteFreeCoefficients.Sites.nu B X).obj KB.obj ≅
        (FiniteFreeCoefficients.Sites.scalar true φ X).obj K),
      (FiniteFreeCoefficients.Sites.scalar true φ Z).map
        (AlgebraicGeometry.FiniteFreeCompactSupport.composition true A
          (HasCompactification.compactification f) (HasCompactification.compactification g)
          (HasCompactification.compactification (f ≫ g)) KA α) ≫
          AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true φ
            (HasCompactification.compactification (f ≫ g)) K =
      AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true φ
          (HasCompactification.compactification g)
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
          (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true φ
            (HasCompactification.compactification f) K) ≫
        AlgebraicGeometry.FiniteFreeCompactSupport.composition true B
          (HasCompactification.compactification f) (HasCompactification.compactification g)
          (HasCompactification.compactification (f ≫ g)) KB β) :
    compactSupportCoefficientComparison (HasCompactification.compactification g) N P₀ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
          (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ≫
        (originCompositionAmbient B f g).hom.app ⟨M.obj, hM⟩ =
      P₀.map Q ((originCompositionAmbient A f g).hom.app ⟨K, hK⟩) ≫
        compactSupportCoefficientComparison (HasCompactification.compactification (f ≫ g)) M Q := by
  let KA : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨hK.choose, hK.choose_spec.1⟩
  let α : (FiniteFreeCoefficients.Sites.nu A X).obj KA.obj ≅ K :=
    Classical.choice hK.choose_spec.2
  have hS := (ProEtale.DerivedCategory.plusEtaleOrigin _ X).prop_of_iso
    (tensorModelIso M).symm hM
  let KB : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) := ⟨hS.choose, hS.choose_spec.1⟩
  let β : (FiniteFreeCoefficients.Sites.nu B X).obj KB.obj ≅
      (FiniteFreeCoefficients.Sites.scalar true φ X).obj K := Classical.choice hS.choose_spec.2
  have hc := hc KA α KB β
  have hca := composition_chosen A f g hK KA α
  have hcb := composition_chosen B f g hS KB β
  have hcCanonical := compositor_equation_transport
    (FiniteFreeCoefficients.Sites.scalar true φ Z)
    hca hcb
    (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      φ (HasCompactification.compactification (f ≫ g)) K)
    (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      φ (HasCompactification.compactification g)
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K))
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
      (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
        φ (HasCompactification.compactification f) K))
    hc
  let v : ⟨(FiniteFreeCoefficients.Sites.scalar true φ X).obj K, hS⟩ ⟶
      (⟨M.obj, hM⟩ : (ProEtale.DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} B) X).FullSubcategory) :=
    ⟨(tensorModelIso M).hom⟩
  have hn := (originCompositionAmbient B f g).hom.naturality v
  change (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        (tensorModelIso M).hom) ≫ _ = _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g)).map
        (tensorModelIso M).hom at hn
  exact tensorComposition_transport
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (tensorModelIso M) (tensorModelIso N) (tensorModelIso P₀) (tensorModelIso Q)
    (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      φ (HasCompactification.compactification f) K)
    (compactSupportCoefficientComparison (HasCompactification.compactification f) M N)
    (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      φ (HasCompactification.compactification g)
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K))
    (compactSupportCoefficientComparison (HasCompactification.compactification g) N P₀)
    (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      φ (HasCompactification.compactification (f ≫ g)) K)
    (compactSupportCoefficientComparison (HasCompactification.compactification (f ≫ g)) M Q)
    ((originCompositionAmbient B f g).hom.app
      ⟨(FiniteFreeCoefficients.Sites.scalar true φ X).obj K, hS⟩)
    ((originCompositionAmbient B f g).hom.app ⟨M.obj, hM⟩)
    ((FiniteFreeCoefficients.Sites.scalar true φ Z).map
      ((originCompositionAmbient A f g).hom.app
        ⟨K, hK⟩))
    (P₀.map Q ((originCompositionAmbient A f g).hom.app
      ⟨K, hK⟩))
    (tensorModelComparison (HasCompactification.compactification f) M N)
    (tensorModelComparison (HasCompactification.compactification g) N P₀)
    (tensorModelComparison (HasCompactification.compactification (f ≫ g)) M Q)
    (tensorModelMap P₀ Q ((originCompositionAmbient A f g).hom.app
      ⟨K, hK⟩)) hn hcCanonical

end TensorTransportHelpers

section SystemComposition
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Compact support on the actual semilinear-system category, at a fixed compactification.
Source: blueprint paragraph 8, simultaneous model; Zheng 4.1 and 4.10
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  J C τ c.i ⋙ R C τ c.g

/-- The canonical reverse refinement word, with its open-unit and proper-compositor factors.
Source: Stacks 0F7B and 0F7J, proof paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def refinement {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) : support C τ d ⟶ support C τ c :=
  haveI := c.quasiCompact_openImmersion inferInstance
  haveI := d.quasiCompact_openImmersion inferInstance
  Functor.whiskerRight
    ((Functor.leftUnitor _).inv ≫ Functor.whiskerRight (sId C τ X).inv (J C τ d.i) ≫
      gamma C τ c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp _).symm)) (R C τ d.g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J C τ c.i)
      ((sComp C τ r.hom d.g).hom ≫
        eqToHom (congrArg (R C τ) r.hom_g))

/-- The graph common-refinement comparison, inverted only on its isomorphism domain.
The zero extension outside that domain is the existing `inverseOnDomain` convention.
Source: Stacks 0F7J; blueprint paragraph 8, fixed compactifications
(blueprint: lem-coef-finite-free-compact-composition). -/
def change {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (M : Derived C τ X) :
    (support C τ c).obj M ⟶ (support C τ d).obj M :=
  (refinement C τ (Compactification.infFst c d)).app M ≫
    FiniteFreeCoefficients.Sites.inverseOnDomain
      ((refinement C τ (Compactification.infSnd c d)).app M)

/-- The canonical proper/open composition word in a compatible triangle.
Source: Stacks 0F7J, the cartesian triangle; blueprint proof paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def triangleWord {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] (T : Compactification.Triangle f g) :
    support C τ T.cf ⋙ support C τ T.cg ⟶ support C τ T.cfg :=
  haveI := T.cf.quasiCompact_openImmersion inferInstance
  haveI := T.cg.quasiCompact_openImmersion inferInstance
  haveI : QuasiCompact T.q := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    T.isPullback inferInstance
  (Functor.associator _ _ _).symm.hom ≫
    Functor.whiskerRight ((Functor.associator _ _ _).hom) _ ≫
    Functor.whiskerRight (Functor.whiskerLeft (J C τ T.cf.i)
      (gamma C τ T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)) _ ≫
    Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
    Functor.whiskerRight (Functor.whiskerRight ((jComp C τ T.cf.i T.q).hom ≫
      (jCongr C τ T.i_q).hom) _) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J C τ T.cfg.i)
      ((sComp C τ T.p T.cg.g).hom ≫ eqToHom (congrArg (R C τ) T.p_g))

/-- The system compositor with the three prescribed compactifications. The auxiliary
triangle is the canonical geometric one; both transports use graph common refinements.
Source: Stacks 0F7J; blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def compositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (M : Derived C τ X) :
    (support C τ cg).obj ((support C τ cf).obj M) ⟶ (support C τ cfg).obj M :=
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  let T := Compactification.Triangle.ofHasCompactification f g
  (support C τ cg).map (change C τ cf T.cf M) ≫
    change C τ cg T.cg ((support C τ T.cf).obj M) ≫
    (triangleWord C τ T).app M ≫ change C τ T.cfg cfg M

end SystemComposition

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

/-- The upper quotient uses the image of the base uniformizer, even when ramified.
Level n denotes positive exponent n+1. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def upperStage (n : ℕ) : Stage l E where
  field := L
  inclusion := i
  exponent := ⟨n + 1, Nat.succ_pos n⟩

/-- The same positive exponent at the base field. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev lowerStage (n : ℕ) : Stage l E := baseStage ⟨n + 1, Nat.succ_pos n⟩

/-- Canonical inclusion on the quotient rings, induced by the integer-ring inclusion.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def inclusion (n : ℕ) : (lowerStage l E n).ring →+* (upperStage l E L i n).ring :=
  (Arrow.ringMap { embedding := i, over_base := AlgHom.comp_id i, level := le_rfl })

/-- Actual adjacent quotient maps at an arbitrary field-extension stage.
Source: blueprint paragraph 8, strict transitions
(blueprint: lem-coef-finite-free-compact-composition). -/
def upperTransition (n : ℕ) :
    (upperStage l E L i (n + 1)).ring →+* (upperStage l E L i n).ring :=
  (Arrow.ringMap (s := upperStage l E L i (n + 1))
    (t := upperStage l E L i n)
    { embedding := AlgHom.id (Padic l) L
      over_base := AlgHom.id_comp i
      level := Nat.le_succ _ })

/-- Base-field adjacent quotient maps. Source: blueprint paragraph 8, strict transitions
(blueprint: lem-coef-finite-free-compact-composition). -/
def lowerTransition (n : ℕ) : (lowerStage l E (n + 1)).ring →+* (lowerStage l E n).ring :=
  upperTransition l E E (AlgHom.id (Padic l) E) n

/-- The constant coefficient ring tower on the original small pro-etale skeleton.
Source: blueprint paragraph 8; Zheng Construction 4.1
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev upperRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (upperStage l E L i n).ring

/-- The base coefficient tower. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev lowerRings (n : ℕ) : CommRingCat.{u + 1} := CommRingCat.of (lowerStage l E n).ring

/-- Bundled quotient transition. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev upperMaps (n : ℕ) : upperRings l E L i (n + 1) ⟶ upperRings l E L i n :=
  CommRingCat.ofHom (upperTransition l E L i n)

/-- Bundled base quotient transition. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev lowerMaps (n : ℕ) : lowerRings l E (n + 1) ⟶ lowerRings l E n :=
  CommRingCat.ofHom (lowerTransition l E n)

/-- The coefficient inclusion is the constant sheaf of the actual quotient inclusion.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def coefficientInclusion (W : Scheme.{u}) (n : ℕ) :
    coefficients (lowerRings l E) W n ⟶ coefficients (upperRings l E L i) W n :=
  (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (inclusion l E L i n))

/-- The canonical inclusions commute with the strict quotient transitions.
Source: blueprint paragraph 8, system clause
(blueprint: lem-coef-finite-free-compact-composition).
Proof: both quotient composites send the residue of r in O_E to the residue of i(r)
in O_L/(i(pi)^(n+1)). Quotient induction proves equality of ring maps; functoriality
of constant sheafification gives the displayed equality on the whole ring tower. -/
theorem coefficientInclusion_commutes (W : Scheme.{u}) (n : ℕ) :
    coefficientInclusion l E L i W (n + 1) ≫
        transition (upperRings l E L i) (upperMaps l E L i) W n =
      transition (lowerRings l E) (lowerMaps l E) W n ≫
        coefficientInclusion l E L i W n := by
  unfold coefficientInclusion AlgebraicGeometry.ProEtale.SemilinearProperOpen.transition
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Simultaneous normalized K-flat coefficient extension, with evaluation comparisons
specified by the tensor/restriction adjunction. Only universal models are selected.
Source: Zheng 4.1, 4.10 and Stacks 06YY, blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def scalarData (W : Scheme.{u}) :=
  (semilinearDerivedSections.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)).some
      |>.coefficientExtension (coefficients (upperRings l E L i) W)
        (transition (upperRings l E L i) (upperMaps l E L i) W)
        (coefficientInclusion l E L i W) (coefficientInclusion_commutes l E L i W)

/-- Actual ordinary restriction along the map of ring sheaves on the sequence site.
Source: blueprint paragraph 8; Stacks 03CZ
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev restriction (W : Scheme.{u}) :=
  res (systemMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
    (coefficients (upperRings l E L i) W)
    (transition (upperRings l E L i) (upperMaps l E L i) W)
    (coefficientInclusion l E L i W) (coefficientInclusion_commutes l E L i W))


/-- Derived restriction is the exact localization of the actual system restriction.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
abbrev restrictionD (W : Scheme.{u}) := (restriction l E L i W).mapDerivedCategory

attribute [local semireducible] CategoryTheory.constantSheaf in
private theorem constantDirectImage_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
        Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    _ _) ((presheafToSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app ((Scheme.proEtaleBaseChange f).op.obj U))
    ((toSheafification (Scheme.ProEt.topology X) CommRingCat.{u + 1}).naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

private theorem restriction_push_iso
    {A B : Type*} [Category A] [Category B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (T : A ⥤ B) [T.IsContinuous J K]
    {RX SX : Sheaf K RingCat.{u + 1}} {RY SY : Sheaf J RingCat.{u + 1}}
    (aX : RX ⟶ SX) (aY : RY ⟶ SY)
    (bA : RY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj RX)
    (bB : SY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj SX)
    (h : bA ≫ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).map aX = aY ≫ bB) :
    ∃ d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bA ≅
        SheafOfModules.pushforward bB ⋙ SheafOfModules.restrictScalars aY,
      ∀ (M : SheafOfModules.{u + 1} SX) (U : Aᵒᵖ)
        (x : M.val.obj (T.op.obj U)), (d.hom.app M).val.app U x = x := by
  let d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bA ≅
      SheafOfModules.pushforward bB ⋙ SheafOfModules.restrictScalars aY :=
    SheafOfModules.pushforwardComp (F := T) (G := 𝟭 B) bA aX ≪≫
      SheafOfModules.pushforwardCongr h ≪≫
        (SheafOfModules.pushforwardComp (F := 𝟭 A) (G := T) aY bB).symm
  exact ⟨d, fun _ _ _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordinary direct-image restriction comparison is fixed on every section.
Source: blueprint paragraph 8, restriction of scalars
(blueprint: lem-coef-finite-free-compact-composition).
Proof: both functors have sections M_n(U times_Y X); the coefficient actions are
through the same inclusion of quotient rings. The identity gives mutually inverse
linear maps, commuting with every vertical and horizontal restriction. Extensionality
of module sheaves proves uniqueness of the natural isomorphism. -/
theorem pushRestriction_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! d : restriction l E L i X ⋙ push (lowerRings l E) (lowerMaps l E) f ≅
      push (upperRings l E L i) (upperMaps l E L i) f ⋙ restriction l E L i Y,
      ∀ (M : Modules (upperRings l E L i) (upperMaps l E L i) X)
        (n : ℕ) (U : Y.ProEt)
        (x : ((restriction l E L i X ⋙ push (lowerRings l E) (lowerMaps l E) f).obj M).val.obj
          (op (n, U))), HEq ((d.hom.app M).val.app (op (n, U)) x) x := by
  let a (W : Scheme.{u}) := systemMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
    (coefficients (upperRings l E L i) W)
    (transition (upperRings l E L i) (upperMaps l E L i) W)
    (coefficientInclusion l E L i W) (coefficientInclusion_commutes l E L i W)
  have ha (W : Scheme.{u}) (V : (ℕ × W.ProEt)ᵒᵖ) :
      (a W).hom.app V = (coefficientInclusion l E L i W V.unop.1).hom.app
        (op V.unop.2) :=
    (systemMap_existsUnique.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
      (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
      (coefficients (upperRings l E L i) W)
      (transition (upperRings l E L i) (upperMaps l E L i) W)
      (coefficientInclusion l E L i W)
      (coefficientInclusion_commutes l E L i W)).exists.choose_spec V.unop.1 (op V.unop.2)
  let bA := AlgebraicGeometry.ProEtale.SemilinearProperOpen.coefficientMap
    (lowerRings l E) (lowerMaps l E) f
  let bB := AlgebraicGeometry.ProEtale.SemilinearProperOpen.coefficientMap
    (upperRings l E L i) (upperMaps l E L i) f
  have hbA (V : (ℕ × Y.ProEt)ᵒᵖ) : bA.hom.app V =
      (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (lowerRings l E V.unop.1)).hom.app (op V.unop.2) :=
    eq_of_heq ((coefficientMap_existsUnique (lowerRings l E) (lowerMaps l E) f).choose_spec.1
      V.unop.1 V.unop.2)
  have hbB (V : (ℕ × Y.ProEt)ᵒᵖ) : bB.hom.app V =
      (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (upperRings l E L i V.unop.1)).hom.app (op V.unop.2) :=
    eq_of_heq ((coefficientMap_existsUnique
      (upperRings l E L i) (upperMaps l E L i) f).choose_spec.1 V.unop.1 V.unop.2)
  let forgetRing (W : Scheme.{u}) := sheafCompose
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let basePush := (siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
  have heComm : bA ≫ ((siteMap f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).map (a X) = a Y ≫ bB := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have hX := ha X ((siteMap f).op.obj V)
    have hY := ha Y V
    have h := congrArg (fun t ↦ t.hom.app (op V.unop.2))
      (constantDirectImage_naturality f (CommRingCat.ofHom
        (inclusion l E L i V.unop.1)))
    exact (congrArg₂ (fun a b ↦ a ≫ b) (hbA V) hX).trans
      (h.symm.trans (congrArg₂ (fun a b ↦ a ≫ b) hY (hbB V)).symm)
  have he : (forgetRing Y).map bA ≫ basePush.map ((forgetRing X).map (a X)) =
      (forgetRing Y).map (a Y) ≫ (forgetRing Y).map bB :=
    congrArg (fun t ↦ (forgetRing Y).map t) heComm
  obtain ⟨d, hd⟩ := restriction_push_iso (siteMap f)
    ((forgetRing X).map (a X)) ((forgetRing Y).map (a Y))
    ((forgetRing Y).map bA) ((forgetRing Y).map bB) he
  refine ⟨d, fun M n U x ↦ heq_of_eq (hd M (op (n, U)) x), ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (eq_of_heq (hd' M U.unop.1 U.unop.2 x)).trans (hd M U x).symm


section RestrictionHelpers
attribute [local irreducible] systemMap systemRing
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Detect the fourth inverse mate in a commutative diamond after evaluation. -/
private theorem inverse_mate_evaluation_isIso
    {A B C D E F G H : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F] [Category G] [Category H]
    {L₀ : A ⥤ B} {R₀ : B ⥤ A} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} {L₃ : G ⥤ H} {R₃ : H ⥤ G}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {T₀₁ : A ⥤ C} {S₀₁ : B ⥤ D} {T₁₃ : C ⥤ G} {S₁₃ : D ⥤ H}
    {T₀₂ : A ⥤ E} {S₀₂ : B ⥤ F} {T₂₃ : E ⥤ G} {S₂₃ : F ⥤ H}
    (w₀₁ : TwoSquare R₀ S₀₁ T₀₁ R₁) (w₁₃ : TwoSquare R₁ S₁₃ T₁₃ R₃)
    (w₀₂ : TwoSquare R₀ S₀₂ T₀₂ R₂) (w₂₃ : TwoSquare R₂ S₂₃ T₂₃ R₃)
    (a : T₀₁ ⋙ T₁₃ ≅ T₀₂ ⋙ T₂₃) (b : S₀₁ ⋙ S₁₃ ≅ S₀₂ ⋙ S₂₃)
    (h : Functor.whiskerLeft R₀ a.hom ≫ (w₀₂.vComp w₂₃).natTrans =
      (w₀₁.vComp w₁₃).natTrans ≫ Functor.whiskerRight b.hom R₃)
    [IsIso ((mateEquiv a₁ a₃).symm w₁₃).natTrans]
    [IsIso ((mateEquiv a₀ a₂).symm w₀₂).natTrans]
    [IsIso ((mateEquiv a₂ a₃).symm w₂₃).natTrans] (M : A) :
    IsIso (S₁₃.map (((mateEquiv a₀ a₁).symm w₀₁).app M)) := by
  have : IsIso ((mateEquiv a₀ a₃).symm (w₀₁.vComp w₁₃)).natTrans :=
    inverse_mate_pasted_isIso a₀ a₂ a₃ w₀₂ w₂₃ (w₀₁.vComp w₁₃) a b h
  have hm : (mateEquiv a₀ a₃).symm (w₀₁.vComp w₁₃) =
      ((mateEquiv a₀ a₁).symm w₀₁).hComp ((mateEquiv a₁ a₃).symm w₁₃) := by
    apply (mateEquiv a₀ a₃).injective
    rw [Equiv.apply_symm_apply, mateEquiv_vcomp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  have : IsIso ((((mateEquiv a₀ a₁).symm w₀₁).hComp
      ((mateEquiv a₁ a₃).symm w₁₃)).app M) := by
    rw [← hm]
    exact NatIso.isIso_app_of_isIso _ M
  have hi : IsIso (((mateEquiv a₁ a₃).symm w₁₃).app (T₀₁.obj M) ≫
      S₁₃.map (((mateEquiv a₀ a₁).symm w₀₁).app M)) := by
    dsimp only [TwoSquare.hComp, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft,
      Functor.whiskerRight] at this
    simpa only [Category.id_comp, Category.comp_id] using this
  have : IsIso (((mateEquiv a₁ a₃).symm w₁₃).app (T₀₁.obj M)) :=
    NatIso.isIso_app_of_isIso _ _
  exact IsIso.of_isIso_comp_left
    (((mateEquiv a₁ a₃).symm w₁₃).app (T₀₁.obj M))
    (S₁₃.map (((mateEquiv a₀ a₁).symm w₀₁).app M))

/-- The inverse mate of evaluation is its unit-normalized pullback comparison. -/
private theorem varyingEvaluationPull_isIso
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso ((mateEquiv (VaryingRing.moduleAdj C τ f)
      (Scheme.proEtaleRingModuleAdjunction f (VaryingRing.coefficients C Y n)
        (VaryingRing.coefficients C X n) (StrictTower.constantRingIso (C n) f))).symm
      (TwoSquare.mk _ _ _ _ (VaryingRing.moduleEvalP C τ f n).hom)).natTrans := by
  have hm : (mateEquiv (VaryingRing.moduleAdj C τ f)
      (Scheme.proEtaleRingModuleAdjunction f (VaryingRing.coefficients C Y n)
        (VaryingRing.coefficients C X n) (StrictTower.constantRingIso (C n) f))
      (VaryingRing.moduleEvalG C τ f n).inv).natTrans =
        (VaryingRing.moduleEvalP C τ f n).hom := by
    apply mate_of_unit_normalization
    exact (VaryingRing.moduleEvalG_existsUnique C τ f n).choose_spec.1
  change mateEquiv _ _ _ = _ at hm
  rw [← hm]
  erw [Equiv.symm_apply_apply]
  exact (VaryingRing.moduleEvalG C τ f n).isIso_inv

/-- Evaluation at all indices detects invertibility of ordinary system maps. -/
private theorem varyingEvaluation_reflectsIso
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (X : Scheme.{u}) {M N : VaryingRing.Modules C τ X} (h : M ⟶ N)
    (hh : ∀ n, IsIso ((VaryingRing.eval C τ X n).map h)) : IsIso h := by
  let R₀ := ring (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (systemRing (Scheme.ProEt.topology X) (VaryingRing.coefficients C X)
      (VaryingRing.coefficientTransition C τ X))
  let G₀ := SheafOfModules.forget R₀ ⋙ PresheafOfModules.toPresheaf R₀.obj
  apply (isIso_iff_of_reflects_iso h G₀).1
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro V
  have := hh V.unop.1
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hb := ConcreteCategory.bijective_of_isIso
    (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      ((VaryingRing.eval C τ X V.unop.1).map h)).app (op V.unop.2))
  change Function.Bijective (fun x ↦ h.val.app V x)
  change Function.Bijective (fun x ↦
    ((VaryingRing.eval C τ X V.unop.1).map h).val.app (op V.unop.2) x) at hb
  change Function.Bijective (fun x ↦ h.val.app V x) at hb
  exact hb

private abbrev ringTower (C : ℕ → Type (u + 1)) [∀ n, CommRing (C n)] :
    ℕ → CommRingCat.{u + 1} := fun n ↦ CommRingCat.of (C n)

/-- Constant coefficient restriction commutes with ordinary pullback, level by level. -/
private theorem ordinarySystemRestrictionPull_isIso
    (C B : ℕ → Type (u + 1)) [∀ n, CommRing (C n)] [∀ n, CommRing (B n)]
    (τ : ∀ n, CommRingCat.of (C (n + 1)) ⟶ CommRingCat.of (C n))
    (σ : ∀ n, CommRingCat.of (B (n + 1)) ⟶ CommRingCat.of (B n))
    (φ : ∀ (W : Scheme.{u}) (n : ℕ),
      VaryingRing.coefficients (ringTower C) W n ⟶ VaryingRing.coefficients (ringTower B) W n)
    (hφ : ∀ (W : Scheme.{u}) (n : ℕ),
      φ W (n + 1) ≫ VaryingRing.coefficientTransition (ringTower B) σ W n =
        VaryingRing.coefficientTransition (ringTower C) τ W n ≫ φ W n)
    (U : ∀ W : Scheme.{u},
      VaryingRing.Modules (ringTower B) σ W ⥤ VaryingRing.Modules (ringTower C) τ W)
    (hU : ∀ W, U W = res (systemMap (Scheme.ProEt.topology W)
      (VaryingRing.coefficients (ringTower C) W)
      (VaryingRing.coefficientTransition (ringTower C) τ W)
      (VaryingRing.coefficients (ringTower B) W)
      (VaryingRing.coefficientTransition (ringTower B) σ W)
      (φ W) (hφ W)))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ n, (StrictTower.constantRingIso (C n) f).hom ≫ φ X n =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (φ Y n) ≫
        (StrictTower.constantRingIso (B n) f).hom)
    (FB : VaryingRing.Modules (ringTower B) σ X ⥤ VaryingRing.Modules (ringTower B) σ Y)
    [FB.IsRightAdjoint]
    (hFB : FB = VaryingRing.push (ringTower B) σ f)
    (FC : VaryingRing.Modules (ringTower C) τ X ⥤ VaryingRing.Modules (ringTower C) τ Y)
    [FC.IsRightAdjoint]
    (hFC : FC = VaryingRing.push (ringTower C) τ f)
    (d : U X ⋙ FC ≅ FB ⋙ U Y)
    (hd : ∀ (M : VaryingRing.Modules (ringTower B) σ X) (n : ℕ) (V : Y.ProEt)
      (x : ((U X ⋙ FC).obj M).val.obj (op (n, V))),
      HEq ((d.hom.app M).val.app (op (n, V)) x) x) :
    IsIso ((mateEquiv (Adjunction.ofIsRightAdjoint FB)
      (Adjunction.ofIsRightAdjoint FC)).symm d.inv) := by
  subst FB FC
  have hu : U = fun W ↦ res (systemMap (Scheme.ProEt.topology W)
      (VaryingRing.coefficients (ringTower C) W)
      (VaryingRing.coefficientTransition (ringTower C) τ W)
      (VaryingRing.coefficients (ringTower B) W)
      (VaryingRing.coefficientTransition (ringTower B) σ W)
      (φ W) (hφ W)) := funext hU
  subst U
  let U (W : Scheme.{u}) := res (systemMap (Scheme.ProEt.topology W)
    (VaryingRing.coefficients (ringTower C) W) (VaryingRing.coefficientTransition (ringTower C) τ W)
    (VaryingRing.coefficients (ringTower B) W) (VaryingRing.coefficientTransition (ringTower B) σ W)
    (φ W) (hφ W))
  change IsIso ((mateEquiv (VaryingRing.moduleAdj (ringTower B) σ f)
    (VaryingRing.moduleAdj (ringTower C) τ f)).symm d.inv)
  have hdInv (M : VaryingRing.Modules (ringTower B) σ X) (V : (ℕ × Y.ProEt)ᵒᵖ)
      (x : ((VaryingRing.push (ringTower B) σ f ⋙ U Y).obj M).val.obj V) :
      HEq ((d.inv.app M).val.app V x) x := by
    have h := hd M V.unop.1 V.unop.2 ((d.inv.app M).val.app V x)
    have hi := congrArg (fun t ↦ t.val.app V x) (d.inv_hom_id_app M)
    change (d.hom.app M).val.app V ((d.inv.app M).val.app V x) = x at hi
    exact h.symm.trans (heq_of_eq hi)
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro M
  have hn (n : ℕ) : IsIso ((VaryingRing.eval (ringTower C) τ X n).map
      (((mateEquiv (VaryingRing.moduleAdj (ringTower B) σ f)
        (VaryingRing.moduleAdj (ringTower C) τ f)).symm d.inv).app M)) := by
    let adA := Scheme.proEtaleRingModuleAdjunction f (VaryingRing.coefficients (ringTower C) Y n)
      (VaryingRing.coefficients (ringTower C) X n) (StrictTower.constantRingIso (C n) f)
    let adB := Scheme.proEtaleRingModuleAdjunction f (VaryingRing.coefficients (ringTower B) Y n)
      (VaryingRing.coefficients (ringTower B) X n) (StrictTower.constantRingIso (B n) f)
    choose e he heuniq using fun W : Scheme.{u} ↦
      restrictionEvaluation_existsUnique (Scheme.ProEt.topology W)
        (VaryingRing.coefficients (ringTower C) W)
        (VaryingRing.coefficientTransition (ringTower C) τ W)
        (VaryingRing.coefficients (ringTower B) W)
        (VaryingRing.coefficientTransition (ringTower B) σ W) (φ W) (hφ W) n
    let qC := VaryingRing.moduleEvalP (ringTower C) τ f n
    let qB := VaryingRing.moduleEvalP (ringTower B) σ f n
    have hqC := (VaryingRing.moduleEvalP_existsUnique (ringTower C) τ f n).choose_spec.1
    have hqB := (VaryingRing.moduleEvalP_existsUnique (ringTower B) σ f n).choose_spec.1
    have hC := varyingEvaluationPull_isIso (ringTower C) τ f n
    have hB := varyingEvaluationPull_isIso (ringTower B) σ f n
    obtain ⟨p, hpsec, hpuniq⟩ := Scheme.proEtaleRingRestrictionDirectImage_existsUnique f
      (VaryingRing.coefficients (ringTower C) Y n) (VaryingRing.coefficients (ringTower B) Y n)
      (VaryingRing.coefficients (ringTower C) X n) (VaryingRing.coefficients (ringTower B) X n)
      (φ Y n) (φ X n) (StrictTower.constantRingIso (C n) f)
      (StrictTower.constantRingIso (B n) f) (hf n)
    have hpeq : p = Scheme.proEtaleRingRestrictionDirectImage f
        (VaryingRing.coefficients (ringTower C) Y n)
        (VaryingRing.coefficients (ringTower B) Y n)
        (VaryingRing.coefficients (ringTower C) X n)
        (VaryingRing.coefficients (ringTower B) X n)
        (φ Y n) (φ X n) (StrictTower.constantRingIso (C n) f)
        (StrictTower.constantRingIso (B n) f) (hf n) :=
      (Scheme.proEtaleRingRestrictionDirectImage_existsUnique f
        (VaryingRing.coefficients (ringTower C) Y n)
        (VaryingRing.coefficients (ringTower B) Y n)
        (VaryingRing.coefficients (ringTower C) X n)
        (VaryingRing.coefficients (ringTower B) X n)
        (φ Y n) (φ X n) (StrictTower.constantRingIso (C n) f)
        (StrictTower.constantRingIso (B n) f) (hf n)).choose_spec.2 p hpsec
    have hp : IsIso ((mateEquiv adB adA).symm (TwoSquare.mk _ _ _ _ p.hom)).natTrans := by
      rw [hpeq]
      have hm := Scheme.restrictionPullback_mate f
        (VaryingRing.coefficients (ringTower C) Y n) (VaryingRing.coefficients (ringTower B) Y n)
        (VaryingRing.coefficients (ringTower C) X n) (VaryingRing.coefficients (ringTower B) X n)
        (φ Y n) (φ X n) (StrictTower.constantRingIso (C n) f)
        (StrictTower.constantRingIso (B n) f) (hf n)
      change mateEquiv adB adA _ = _ at hm
      rw [← hm]
      erw [Equiv.symm_apply_apply]
      exact Scheme.proEtaleRingRestrictionPullbackInv_isIso f
        (VaryingRing.coefficients (ringTower C) Y n) (VaryingRing.coefficients (ringTower B) Y n)
        (VaryingRing.coefficients (ringTower C) X n) (VaryingRing.coefficients (ringTower B) X n)
        (φ Y n) (φ X n) (StrictTower.constantRingIso (C n) f)
        (StrictTower.constantRingIso (B n) f) (hf n)
    dsimp only [StrictTower.moduleDirectImage] at qC qB hqC hqB hC hB
    apply inverse_mate_evaluation_isIso (VaryingRing.moduleAdj (ringTower B) σ f)
      (VaryingRing.moduleAdj (ringTower C) τ f) adB adA (TwoSquare.mk _ _ _ _ d.inv)
      (TwoSquare.mk _ _ _ _ qC.hom)
      (TwoSquare.mk _ _ _ _ qB.hom)
      (TwoSquare.mk _ _ _ _ p.hom) (e Y) (e X) ?_ M
    apply NatTrans.ext
    funext N
    dsimp only [TwoSquare.vComp, TwoSquare.natTrans, TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft, Functor.whiskerRight, Functor.associator_hom_app,
      Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    ext V x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    have he' (W : Scheme.{u}) (N : VaryingRing.Modules (ringTower B) σ W)
        (V : W.ProEtᵒᵖ) (x : N.val.obj (op (n, V.unop))) :
        ((e W).hom.app N).val.app V x = x :=
      congrFun (eq_of_heq (he W N V)) x
    dsimp only [Scheme.proEtaleRingRestrictScalars, SheafOfModules.restrictScalars,
      PresheafOfModules.restrictScalars, ModuleCat.restrictScalars,
      ModuleCat.RestrictScalars.map', Functor.comp_map,
      Scheme.proEtaleRingModuleDirectImage, SheafOfModules.pushforward,
      PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
      VaryingRing.eval, SemilinearSections.evaluation]
    let ex := ((e Y).hom.app ((VaryingRing.push (ringTower B) σ f).obj N)).val.app V x
    let tx := (d.inv.app N).val.app (op (n, V.unop)) x
    let ty := (qC.hom.app ((U X).obj N)).val.app V tx
    have hL₀ := hpsec ((VaryingRing.eval (ringTower B) σ X n).obj N) V
      ((qB.hom.app N).val.app V ex)
    have hL₁ := hqB N V.unop ex
    have hL₂ := he' Y ((VaryingRing.push (ringTower B) σ f).obj N) V x
    have hhL₀ := heq_of_eq hL₀
    have hhL₁ := heq_of_eq hL₁
    have hhL₂ := heq_of_eq hL₂
    have hL := hhL₀.trans (hhL₁.trans hhL₂)
    have hR₀ := he' X N ((Scheme.proEtaleBaseChange f).op.obj V) ty
    have hR₁ := hqC ((U X).obj N) V.unop tx
    have hR₂ := hdInv N (op (n, V.unop)) x
    have hhR₀ := heq_of_eq hR₀
    have hhR₁ := heq_of_eq hR₁
    have hR := hhR₀.trans (hhR₁.trans hR₂)
    exact eq_of_heq (hL.trans hR.symm)
  exact varyingEvaluation_reflectsIso (ringTower C) τ X _ hn

end RestrictionHelpers

/-- The ordinary pullback restriction square is the transpose of the section identity.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def pullRestrictionInv {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv (ordinaryAdj (upperRings l E L i) (upperMaps l E L i) f)
    (ordinaryAdj (lowerRings l E) (lowerMaps l E) f)).symm
      (pushRestriction_existsUnique l E L i f).choose.inv

section PullRestrictionProof
attribute [local irreducible] systemRing systemMap
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionAbsoluteValue
  Stage.ideal Stage.parameter
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The specified pullback comparison is invertible.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition).
Proof: evaluate the ordinary restriction square at every coefficient index.
The normalized evaluation and scalar restriction squares have identical section maps,
so their two pastings agree. Their inverse mates are invertible by the unit-normalized
pullback evaluation comparison and ring-sheaf change of scalars. Mate pasting and
cancellation make every evaluation of the specified mate invertible. The conservative
forgetful functor to abelian presheaves then detects invertibility of the system map. -/
theorem pullRestrictionInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (pullRestrictionInv l E L i f) := by
  apply @ordinarySystemRestrictionPull_isIso
    (fun n ↦ (lowerStage l E n).ring) (fun n ↦ (upperStage l E L i n).ring)
    inferInstance inferInstance
    (lowerMaps l E) (upperMaps l E L i)
    (coefficientInclusion l E L i) (coefficientInclusion_commutes l E L i)
    (restriction l E L i) (fun _ ↦ rfl) X Y f ?_
    (push (upperRings l E L i) (upperMaps l E L i) f)
    (push_isRightAdjoint (upperRings l E L i) (upperMaps l E L i) f)
    (push_eq (upperRings l E L i) (upperMaps l E L i) f)
    (push (lowerRings l E) (lowerMaps l E) f)
    (push_isRightAdjoint (lowerRings l E) (lowerMaps l E) f)
    (push_eq (lowerRings l E) (lowerMaps l E) f)
    (pushRestriction_existsUnique l E L i f).choose
    (pushRestriction_existsUnique l E L i f).choose_spec.1
  intro n
  simpa only [StrictTower.constantRingIso, coefficientInclusion, asIso_hom] using
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (a := CommRingCat.ofHom (inclusion l E L i n))).symm

end PullRestrictionProof

/-- Exact localization of the specified inverse-image scalar square.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def pullRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P (upperRings l E L i) (upperMaps l E L i) f ⋙ restrictionD l E L i X ≅
      restrictionD l E L i Y ⋙ P (lowerRings l E) (lowerMaps l E) f :=
  letI := (pull_exact (lowerRings l E) (lowerMaps l E) f).1
  letI := (pull_exact (lowerRings l E) (lowerMaps l E) f).2.1
  letI := (pull_exact (lowerRings l E) (lowerMaps l E) f).2.2
  letI := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).1
  letI := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).2.1
  letI := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).2.2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (pullRestrictionInv l E L i f)
        (pullRestrictionInv_isIso l E L i f)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Proper direct-image restriction is the actual derived adjunction mate.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def pushRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R (upperRings l E L i) (upperMaps l E L i) f ⋙ restrictionD l E L i Y ⟶
      restrictionD l E L i X ⋙ R (lowerRings l E) (lowerMaps l E) f :=
  mateEquiv (adj (upperRings l E L i) (upperMaps l E L i) f)
    (adj (lowerRings l E) (lowerMaps l E) f) (pullRestriction l E L i f).inv

/-- Finite freeness makes the canonical direct-image restriction mate invertible.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition).
Proof: a fixed O_E-basis of O_L reduces to a basis of every B_n over A_n, compatible
with quotient transitions. Thus extension on strict systems is exact. Its right
adjoint restriction preserves K-injectives. The section identity computing ordinary
direct image therefore computes its derived mate on K-injective system resolutions.
The inverse section identity yields the inverse, compatibly with units and counits. -/
theorem pushRestriction_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (pushRestriction l E L i f) := by
  sorry

/-- The open restriction square is fixed by the open unit and the same pullback mate.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def openRestrictionInv {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (mateEquiv (jAdj (upperRings l E L i) (upperMaps l E L i) j)
    (jAdj (lowerRings l E) (lowerMaps l E) j)).symm (pullRestriction l E L i j).hom

/-- The open-unit restriction mate is an isomorphism on whole systems.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition).
Proof: on the open both maps are the identity on sections, and outside it both
extensions vanish. These maps commute with the quotient transitions and are inverse
already on ordinary systems. Exact localization preserves the inverse identities. -/
theorem openRestrictionInv_isIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    IsIso (openRestrictionInv l E L i j) := by
  sorry

/-- The whole-system compact-support restriction comparison, in open-then-proper order.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def supportRestriction {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    restrictionD l E L i X ⋙ support (lowerRings l E) (lowerMaps l E) c ≅
      support (upperRings l E L i) (upperMaps l E L i) c ⋙ restrictionD l E L i Y :=
  Functor.isoWhiskerRight
    (@asIso _ _ _ _ (openRestrictionInv l E L i c.i)
      (openRestrictionInv_isIso l E L i c.i)) _ ≪≫
    Functor.isoWhiskerLeft _
      (@asIso _ _ _ _ (pushRestriction l E L i c.g) (pushRestriction_isIso l E L i c.g)).symm

/-- The specified B-linear whole-system coefficient map, obtained by scalar adjunction.
Source: blueprint paragraph 8; Stacks 06YY and 07A6
(blueprint: lem-coef-finite-free-compact-composition). -/
def coefficientComparison {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    support (lowerRings l E) (lowerMaps l E) c ⋙ (scalarData l E L i Y).scalar.T ⟶
      (scalarData l E L i X).scalar.T ⋙ support (upperRings l E L i) (upperMaps l E L i) c :=
  ((mateEquiv (scalarData l E L i X).scalar.adjunction
    (scalarData l E L i Y).scalar.adjunction).symm
      (TwoSquare.mk _ (support (upperRings l E L i) (upperMaps l E L i) c)
        (support (lowerRings l E) (lowerMaps l E) c) _
          (supportRestriction l E L i c).hom)).natTrans


/-- The source simultaneous normalized K-flat calculus, retaining every reduction map.
Source: blueprint paragraph 8; Zheng 4.10
(blueprint: lem-coef-finite-free-compact-composition). -/
def lowerCalculus (W : Scheme.{u}) :=
  (semilinearDerivedSections.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)).some.systems

/-- The normalized finite-Tor constructible system domain. The ordered Tor interval is
allowed to depend on the positive level, and every degree-zero module sheaf is tested.
Source: blueprint paragraph 8, normalized systems; Stacks 08FZ and Zheng 4.10
(blueprint: lem-coef-finite-free-compact-composition). -/
def normalizedCtf (W : Scheme.{u})
    (M : Derived (lowerRings l E) (lowerMaps l E) W) : Prop :=
  Normalized.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
    (lowerCalculus l E W).scalar M ∧
    ∀ n : ℕ,
      Set.Finite {j : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
          (coefficients (lowerRings l E) W n)) j).obj
            ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
              (coefficients (lowerRings l E) W)
              (transition (lowerRings l E) (lowerMaps l E) W) n).obj M))} ∧
      (∀ j : ℤ, Scheme.IsConstructibleProEtaleCoefficientModuleSheaf W
        (lowerStage l E n).ring
          ((DerivedCategory.homologyFunctor
            (SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
              (coefficients (lowerRings l E) W n)) j).obj
                ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
                  (coefficients (lowerRings l E) W)
                  (transition (lowerRings l E) (lowerMaps l E) W) n).obj M))) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
          (coefficients (lowerRings l E) W n)) (j : ℤ),
          (j < a ∨ b < j) → IsZero ((DerivedCategory.homologyFunctor
            (SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
              (coefficients (lowerRings l E) W n)) j).obj
                (((lowerCalculus l E W).levelClosed n).tensor.obj
                  ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
                    (coefficients (lowerRings l E) W)
                    (transition (lowerRings l E) (lowerMaps l E) W) n).obj M,
                    (DerivedCategory.singleFunctor _ 0).obj N)))


/-- Finite-free coefficient extension preserves the bounded etale-origin class on
finite-Tor constructible inputs, for every universal B-linear tensor presentation.
Source: blueprint paragraph 8; lem-sf-proetale-constructible-origin
(blueprint: lem-coef-finite-free-compact-composition).
Proof: choose a bounded-below etale-origin witness for the constructible input.
Transport its Tor interval across the origin isomorphism and reflect that interval
through the site comparison. The scalar/tensor isomorphism then makes etale scalar
extension bounded below. The scalar/site comparison realizes this scalar extension
on the pro-etale site. Its adjunction unit and the given tensor presentation are
universal, so their unique unit-preserving comparison is an isomorphism. Transport
the etale-origin witness along this isomorphism. Finite freeness is not needed for
this bounded-below assertion; the finite Tor interval suffices. -/
theorem finiteTensorOrigin (n : ℕ) (X : Scheme.{u})
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (lowerStage l E n).ring)))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (lowerStage l E n).ring) X K)
    (M : CoefficientTensorModel (inclusion l E L i n) X K) :
    ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (upperStage l E L i n).ring) X M.obj := by
  let A := (lowerStage l E n).ring
  let B := (upperStage l E L i n).ring
  let φ := inclusion l E L i n
  obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := hK.plusEtaleOrigin
  obtain ⟨a, b, ht⟩ := hK.2
  have ht₀ : ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K₀) :=
    (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eK.symm ht
  have het := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
    (Λ := A) a b K₀).mp ht₀
  have htor : Etale.DerivedCategory.hasTorAmplitudeIn A X a b K₀ :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr het
  have hscalar : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ X).obj K₀) := by
    refine ⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr fun q hq ↦ ?_⟩
    apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
    exact (htor (Etale.scalarCoefficientSheaf φ X) q (Or.inl hq)).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((Etale.scalarTensorIso φ X).app K₀))
  let := pbcRestriction_isRightAdjoint.{u} (Scheme.ProEt.topology X) φ
  let U := Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ
  let S := pbcFixedScalarExtension.{u} (Scheme.ProEt.topology X) φ
  let ad : S ⊣ U := Adjunction.ofIsRightAdjoint U
  have hu : Sheaf.IsDerivedBaseChange.{u} (J := Scheme.ProEt.topology X)
      (f := φ) (ad.unit.app K) := by
    intro N
    change Function.Bijective (fun g : S.obj K ⟶ N ↦ ad.unit.app K ≫ U.map g)
    have he : (fun g : S.obj K ⟶ N ↦ ad.unit.app K ≫ U.map g) = ad.homEquiv K N := by
      funext g
      exact (ad.homEquiv_unit K N g).symm
    rw [he]
    exact (ad.homEquiv K N).bijective
  let g := (ad.homEquiv K M.obj).symm M.unit
  have hg : ad.unit.app K ≫ U.map g = M.unit := by
    change ad.homEquiv K M.obj g = M.unit
    exact Equiv.apply_symm_apply _ _
  have : IsIso g := Sheaf.IsDerivedBaseChange.isIso.{u} hu M.universal g hg
  let eM : (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
      ((Etale.scalarExtension φ X).obj K₀) ≅ M.obj :=
    (pbcComparisonReduction.{u} X φ).symm.app K₀ ≪≫ S.mapIso eK ≪≫ asIso g
  exact (ProEtale.DerivedCategory.plusEtaleOrigin _ X).prop_of_iso eM
    (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hscalar)

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))]
  [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))]
  [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [qcF : QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [qcG : QuasiCompact g]


attribute [local irreducible] tensorModelIso scalarAdj originCompositionModel
  originCompositionAmbient HasDerivedCategory.ofIsGrothendieckAbelian
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] AlgebraicGeometry.FiniteCoefficientAdjoints.upper
  etaleUpper etaleAdjunction projectionAtWitness refinementAtWitness
  pbcFixedScalarExtension pbcFixedScalarExtensionComp normalizedOriginScalarUnit
  compactSupportSiteComparison derivedComparisonAdjunction

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionAbsoluteValue Stage.ideal Stage.parameter

attribute [local irreducible] _root_.DerivedCategory _root_.instCategoryDerivedCategory

attribute [local irreducible] compactSupportCoefficientComparison CoefficientTensorModel.map
  AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap
  AlgebraicGeometry.FiniteFreeCompactSupport.composition

include D hl overX overY overZ sepX ftX qcX sepY ftY qcY sepZ ftZ qcZ
  overF overG sepF ftF qcF sepG ftG qcG in
/-- The specified finite-level B-linear coefficient maps commute with compact-support
composition. The equation uses universal tensor presentations, hence fixes B-linearity
and includes every presentation of the canonical derived tensor functor.
Source: blueprint paragraph 8; Stacks 0F7J
(blueprint: lem-coef-finite-free-compact-composition).
Proof: apply lem-pur-finite-free-compact-composition. Its c_h is exactly the proper
counit-transpose coefficient comparison followed by the open balancing comparison
of lem-coef-etale-open-tensor. The coefficient algebra is O_L/pi^n, finite free
by lem-coef-finite-free-extension, not O_L/v^n. Forgetting the B-action identifies
the comparison with finite-sum distributivity in a reduced O_E-basis of O_L.
The compact-support site comparison and comparison-open-tensor coherence transport
this same map and the canonical compositor to the pro-etale origin class. Substitute
M=K in that lemma's equation; universal tensor map functoriality gives the displayed
identity. Finite freeness makes each comparison invertible by finite-sum
distributivity. This calculation uses no faithfulness of derived scalar restriction. -/
theorem finiteLevelComposition (n : ℕ)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (lowerStage l E n).ring)))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (lowerStage l E n).ring) X K)
    (M : CoefficientTensorModel (inclusion l E L i n) X K)
    (N : CoefficientTensorModel (inclusion l E L i n) Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) f).obj K))
    (P₀ : CoefficientTensorModel (inclusion l E L i n) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) g).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) f).obj K)))
    (Q : CoefficientTensorModel (inclusion l E L i n) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) (f ≫ g)).obj K)) :
    IsIso (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ∧
    IsIso (compactSupportCoefficientComparison (HasCompactification.compactification g) N P₀) ∧
    IsIso (compactSupportCoefficientComparison
      (HasCompactification.compactification (f ≫ g)) M Q) ∧
    compactSupportCoefficientComparison (HasCompactification.compactification g) N P₀ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (upperStage l E L i n).ring) g).map
          (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ≫
        (originCompositionAmbient (upperStage l E L i n).ring f g).hom.app
          ⟨M.obj, finiteTensorOrigin l E L i n X K hK M⟩ =
      P₀.map Q ((originCompositionAmbient (lowerStage l E n).ring f g).hom.app
        ⟨K, hK.plusEtaleOrigin⟩) ≫
          compactSupportCoefficientComparison
            (HasCompactification.compactification (f ≫ g)) M Q := by
  let := finiteTypeNoetherian D.k X
  let := finiteTypeNoetherian D.k Y
  let := finiteTypeNoetherian D.k Z
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hF := ((finite_coefficient_adjoint_comparisons D.k D.p l D.prime.pos hl E f).choose.datum
    (lowerStage l E n) (HasCompactification.compactification f)).lower_preserves K hK
  let a : Arrow (lowerStage l E n) (upperStage l E L i n) :=
    { embedding := i, over_base := AlgHom.comp_id i, level := le_rfl }
  have h := AlgebraicGeometry.FiniteFreeCompactSupport.finite_free_compactSupport_composition
    D l hl E ⟨n + 1, Nat.succ_pos n⟩ (upperStage l E L i n) a rfl true f g
    (HasCompactification.compactification f) (HasCompactification.compactification g)
    (HasCompactification.compactification (f ≫ g)) K hK
  let : HasCompactification (g ≫ 𝟙 Z) := HasCompactification.of_eq (Category.comp_id g).symm
  have hg := AlgebraicGeometry.FiniteFreeCompactSupport.finite_free_compactSupport_composition
    D l hl E ⟨n + 1, Nat.succ_pos n⟩ (upperStage l E L i n) a rfl true g (𝟙 Z)
    (HasCompactification.compactification g) (Compactification.ofIsProper (𝟙 Z))
    (HasCompactification.compactification (g ≫ 𝟙 Z)) _ hF
  let : HasCompactification ((f ≫ g) ≫ 𝟙 Z) :=
    HasCompactification.of_eq (Category.comp_id (f ≫ g)).symm
  have hfg := AlgebraicGeometry.FiniteFreeCompactSupport.finite_free_compactSupport_composition
    D l hl E ⟨n + 1, Nat.succ_pos n⟩ (upperStage l E L i n) a rfl true (f ≫ g) (𝟙 Z)
    (HasCompactification.compactification (f ≫ g)) (Compactification.ofIsProper (𝟙 Z))
    (HasCompactification.compactification ((f ≫ g) ≫ 𝟙 Z)) K hK
  have hfIso : IsIso (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      (inclusion l E L i n) (HasCompactification.compactification f) K) := h.2.1
  have hgIso : IsIso (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      (inclusion l E L i n) (HasCompactification.compactification g)
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) f).obj K)) :=
    hg.2.1
  have hfgIso : IsIso (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      (inclusion l E L i n) (HasCompactification.compactification (f ≫ g)) K) := hfg.2.1
  refine ⟨tensorModelComparison_isIso (HasCompactification.compactification f) M N
      (hcanonical := hfIso),
    tensorModelComparison_isIso (HasCompactification.compactification g) N P₀
      (hcanonical := hgIso),
    tensorModelComparison_isIso (HasCompactification.compactification (f ≫ g)) M Q
      (hcanonical := hfgIso), ?_⟩
  have hM := finiteTensorOrigin l E L i n X K hK M
  exact tensorPresentation_composition (inclusion l E L i n) f g K hK.plusEtaleOrigin
    M N P₀ Q hM (fun KA α KB β ↦ (h.2.2.2.2.2 KA α KB β).1)


include D hl overX overY overZ sepX ftX qcX sepY ftY qcY sepZ ftZ qcZ
  overF overG sepF ftF qcF sepG ftG qcG in
/-- The same equality in the ordinary derived category of B-coefficient systems,
with the specified proper/open compositor and coefficient mate, before total limit.
Source: blueprint paragraph 8, simultaneous semilinear-section clause
(blueprint: lem-coef-finite-free-compact-composition).
Proof: (1) Fix one O_E-basis of O_L and reduce it at every positive level. It identifies
B_m tensor^L_A_m A_n with B_n, compatibly with strict quotient transitions. The B-tower
is normalized and constructible of Tor amplitude [0,0]. (2) The simultaneous model of
lem-coef-semilinear-derived-sections provides the actual system scalar adjunction and
geometric operations. Restriction is exact and, as the right adjoint of exact finite
free extension, preserves K-injectives. Hence it commutes with derived direct images,
open extension, their units and counits, and the displayed proper/open compositors.
(3) Under Res T=P tensor B, restriction of coefficientComparison is precisely the
system projection word: transpose the proper counit and then apply open balancing.
This identifies constructed system maps, not just their evaluations.
(4) Apply lem-pur-system-level-projection-formula-coherence to K and the normalized
constant B-tower. It gives equality of restrictions of the two displayed B-system
maps in D(A-systems). Their common source is T(F_g F_f K). The adjunction T ⊣ Res
identifies each map with its restriction composed with the unit; equal restrictions
therefore give equal transposes and equal B-system maps. Derived Res need not be
faithful. (5) Run this construction with the fixed compactifications. The refinement
substitution and cocycle laws of lem-pur-system-compactification-pf-substitution
identify the graph-refinement transports in compositor with the canonical ones.
The proper/open and refinement comparisons are isomorphisms on this domain;
finite-sum distributivity makes the coefficient comparisons isomorphisms. The
equality is established before evaluation and before any inverse limit. -/
theorem systemComposition
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : Derived (lowerRings l E) (lowerMaps l E) X) (hK : normalizedCtf l E X K) :
    IsIso ((coefficientComparison l E L i cf).app K) ∧
    IsIso ((coefficientComparison l E L i cg).app
      ((support (lowerRings l E) (lowerMaps l E) cf).obj K)) ∧
    IsIso ((coefficientComparison l E L i cfg).app K) ∧
    IsIso (compositor (lowerRings l E) (lowerMaps l E) cf cg cfg K) ∧
    IsIso (compositor (upperRings l E L i) (upperMaps l E L i) cf cg cfg
      ((scalarData l E L i X).scalar.T.obj K)) ∧
    (coefficientComparison l E L i cg).app ((support (lowerRings l E) (lowerMaps l E) cf).obj K) ≫
        (support (upperRings l E L i) (upperMaps l E L i) cg).map
          ((coefficientComparison l E L i cf).app K) ≫
        compositor (upperRings l E L i) (upperMaps l E L i) cf cg cfg
          ((scalarData l E L i X).scalar.T.obj K) =
      (scalarData l E L i Z).scalar.T.map
          (compositor (lowerRings l E) (lowerMaps l E) cf cg cfg K) ≫
        (coefficientComparison l E L i cfg).app K := by
  sorry

end Geometry
end Coefficients
end WeilConjectures.FiniteFreeCompactComposition
