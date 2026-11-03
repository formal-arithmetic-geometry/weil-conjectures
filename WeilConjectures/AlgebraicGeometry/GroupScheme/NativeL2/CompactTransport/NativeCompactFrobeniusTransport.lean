/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!
# Native compact-support Frobenius transport

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/sec-frobenius/
sec-purity-duality-and-frobenius/sk-thm-frobenius/_section.md,
canonical point insertion and ordinary/open compactification mates
(blueprint: def-a1-condensed-frobenius-transport).

This dependency module supplies the recorded transport definitions on actual condensed
modules. It uses the canonical pullback compositors, adjunction mates and geometric fibre.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeCompactTransport


variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The pullback equivalence with its specified inverse pullback. Its coherence maps
are precisely the identity and composition comparisons of module inverse image.
Source: latest blueprint, canonical pullback compositors
(blueprint: def-a1-condensed-frobenius-transport). -/
def constantExtensionPullEquivalence {X Y : Scheme.{u}} (a : X ≅ Y) :=
  CategoryTheory.Equivalence.mk (upperStar Λ a.hom) (upperStar Λ a.inv)
    ((upperStarId Λ Y).symm ≪≫ upperStarCongr Λ a.inv_hom_id.symm ≪≫
      upperStarComp Λ a.inv a.hom)
    ((upperStarComp Λ a.hom a.inv).symm ≪≫ upperStarCongr Λ a.hom_inv_id ≪≫
      upperStarId Λ X)

/-- The open exchange, computed as conjugation of the inverse-automorphism pullback
square. This is the inverse of the left-adjoint mate of the forward pullback square.
Source: latest blueprint, compactification transport in the second paragraph
(blueprint: def-a1-condensed-frobenius-transport). -/
def constantExtensionOpenExchange {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (aX : X ≅ X) (aZ : Z ≅ Z) (hj : CommSq aX.hom j j aZ.hom) :
    openImmersionLowerShriek Λ j ⋙ upperStar Λ aZ.hom ≅
      upperStar Λ aX.hom ⋙ openImmersionLowerShriek Λ j :=
  (conjugateIsoEquiv
    ((constantExtensionPullEquivalence Λ aX).toAdjunction.comp
      (openImmersionLowerShriekUpperStarAdjunction Λ j))
    ((openImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (constantExtensionPullEquivalence Λ aZ).toAdjunction)).symm
        (upperStarSquareComparison Λ hj.horiz_inv).symm

/-- The derived pullback square, with the termwise localization compositors retained.
Source: latest blueprint, canonical pullback composition
(blueprint: def-a1-condensed-frobenius-transport). -/
def constantExtensionDerivedSquare {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    (upperStar Λ g).mapDerivedCategory ⋙ (upperStar Λ f').mapDerivedCategory ≅
      (upperStar Λ f).mapDerivedCategory ⋙ (upperStar Λ g').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarSquareComparison Λ sq) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The direct proper-image exchange: unit, pullback-square comparison, then counit.
Source: latest blueprint, compactification transport
(blueprint: def-a1-condensed-frobenius-transport). -/
def constantExtensionProperExchange {Z S : Scheme.{u}} (p : Z ⟶ S)
    (aZ : Z ≅ Z) (aS : S ≅ S) (hp : CommSq aZ.hom p p aS.hom) :
    (lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ aS.hom).mapDerivedCategory ⟶
      (upperStar Λ aZ.hom).mapDerivedCategory ⋙ (lowerStar Λ p).rightDerivedFunctor :=
  Adjunction.exchangeRight
    ((upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction)
    ((upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction)
    (constantExtensionDerivedSquare Λ hp)

/-- The direct exchange on the compactification composite, before taking sections.
Source: latest blueprint, compact-support transport
(blueprint: def-a1-condensed-frobenius-transport). -/
def constantExtensionCompactExchange {X S : Scheme.{u}} {f : X ⟶ S}
    (c : Compactification f) (aX : X ≅ X) (aZ : c.Z ≅ c.Z) (aS : S ≅ S)
    (hj : CommSq aX.hom c.i c.i aZ.hom) (hp : CommSq aZ.hom c.g c.g aS.hom) :
    rightDerivedLowerShriekOfCompactification Λ c ⋙
        (upperStar Λ aS.hom).mapDerivedCategory ⟶
      (upperStar Λ aX.hom).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ c :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (constantExtensionProperExchange Λ c.g aZ aS hp) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).inv ≫
        (Functor.mapDerivedCategoryNatIso
          (constantExtensionOpenExchange Λ c.i aX aZ hj)).hom ≫
        (Functor.mapDerivedCategoryCompIso _ _).hom) _ ≫
    (Functor.associator _ _ _).hom

end AlgebraicGeometry.ProEtale.CondensedRing.NativeCompactTransport

namespace WeilConjectures.NativeL2.CompactTransport

/-- Direct geometric-point insertion in the ordinary derived coefficient category.
It derives the specified point trivialization and applies a given functor out of the
derived category of the point (below: derived geometric evaluation).
Source: latest blueprint, second proof paragraph
(blueprint: def-a1-condensed-frobenius-transport). -/
def derivedPointInsertion (l : ℕ) [Fact l.Prime]
    (K : Type u) [Field K] [IsAlgClosed K] (d : Spec (.of K) ⟶ Spec (.of K))
    {C : Type v} [Category.{w} C]
    (F : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of K)))) ⥤ C) :
    F ≅ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) d).mapDerivedCategory ⋙ F :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
        (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) d) ≪≫
          Functor.mapDerivedCategoryIdIso _).symm F

/-- The proper compactification model, with a named Over presentation.
Source: compactification of the finite-field structure map
(blueprint: def-a1-condensed-frobenius-transport). -/
def compactModel (D : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of D.k₀)))
    (c₀ : Compactification X₀.hom) : Over (Spec (.of D.k₀)) :=
  Over.mk c₀.g

/-- Finite type of the proper compactification model, in its Over presentation.
Source: definition of compactification
(blueprint: def-a1-condensed-frobenius-transport). -/
instance compactModel_lft (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) (c₀ : Compactification X₀.hom) :
    LocallyOfFiniteType (compactModel D X₀ c₀).hom :=
  inferInstanceAs (LocallyOfFiniteType c₀.g)

/-- Quasi-compactness of the proper compactification model in its Over presentation.
Source: definition of compactification
(blueprint: def-a1-condensed-frobenius-transport). -/
instance compactModel_qc (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) (c₀ : Compactification X₀.hom) :
    QuasiCompact (compactModel D X₀ c₀).hom :=
  inferInstanceAs (QuasiCompact c₀.g)

/-- Base change of an actual compactification of the finite-field model.
Source: latest blueprint, compactification paragraph
(blueprint: def-a1-condensed-frobenius-transport). -/
def compactBase (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (c₀ : Compactification X₀.hom) : Compactification (D.geometricFiber X₀).hom :=
  { Z := (D.geometricFiber (compactModel D X₀ c₀)).left
    g := (D.geometricFiber (compactModel D X₀ c₀)).hom
    i := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
      (Over.homMk c₀.i c₀.comm.symm : X₀ ⟶ compactModel D X₀ c₀)).left
    comm := ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        (Over.homMk c₀.i c₀.comm.symm : X₀ ⟶ compactModel D X₀ c₀)).w.symm
    isProper := inferInstanceAs (IsProper (pullback.snd c₀.g
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    isOpenImmersion := MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      (Over.homMk c₀.i c₀.comm.symm : X₀ ⟶ compactModel D X₀ c₀) c₀.isOpenImmersion }

variable (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The base-changed open map commutes with coefficient Frobenius by the two
pullback projection identities. Source: latest blueprint, compactification transport
(blueprint: def-a1-condensed-frobenius-transport). -/
abbrev compactOpenSquare (c₀ : Compactification X₀.hom) :
    CommSq (D.geometricFrobenius X₀).hom (compactBase D X₀ c₀).i
      (compactBase D X₀ c₀).i (D.geometricFrobenius (compactModel D X₀ c₀)).hom := by
  refine ⟨?_⟩
  apply pullback.hom_ext
  · simp [compactBase, compactModel, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, baseChangeMap, Category.assoc]
  · simp [compactBase, compactModel, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, baseChangeMap, Category.assoc]

/-- The proper factor's Frobenius square is its second geometric-fibre projection.
Source: latest blueprint, compactification transport
(blueprint: def-a1-condensed-frobenius-transport). -/
abbrev compactProperSquare (c₀ : Compactification X₀.hom) :
    CommSq (D.geometricFrobenius (compactModel D X₀ c₀)).hom (compactBase D X₀ c₀).g
      (compactBase D X₀ c₀).g (NativeCondensedModule.frobeniusPointIso D).hom :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  ⟨(D.galoisMap_projections c₀.g
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).2⟩

/-- Derive the actual Weil isomorphism in degree zero using the single-functor compositor.
Source: latest blueprint, geometric Weil structure on coefficient complexes
(blueprint: def-a1-condensed-frobenius-transport). -/
def derivedTheta (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} (g : X ⟶ X)
    (M : NativeCondensedModule.Modules l X)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M ≅ M) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj M :=
  ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).mapDerivedCategorySingleFunctor
    0).app M ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso θ

end WeilConjectures.NativeL2.CompactTransport
