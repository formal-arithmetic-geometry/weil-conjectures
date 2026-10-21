/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.FiniteSmoothPurityMaps

/-! # Finite smooth coefficient arrows

Source: main-20261015 blueprint, sk-lem-sp-reduction and its compatibility proof
(blueprint: def-pur-finite-smooth-coefficient-arrows).

## Main definitions

* `CoefficientLineComparison`: generator-normalized reduction of the actual root line.
* `pullbackTwistComparison`, `proLambda`: canonical purity-source balancing.
* `proCoefficientMap`, `proCompactCoefficientMap`: the actual exceptional and support maps.
* `proPullbackMap`, `proTwistMap`: the separate transported comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
/-- The quotient cocycle diagram, with both scalar associators displayed. In every
application below all six scalar functors and all three coefficient arrows are the
specified canonical maps. This notation avoids re-elaborating their expanded domains.
Source: sk-lem-sp-reduction/compatibilities (2)
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def QuotientCocycle {C₁ C₂ C₃ D₁ D₂ D₃ : Type v}
    [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Category.{w} D₁] [Category.{w} D₂] [Category.{w} D₃]
    (s₁₂ : C₁ ⥤ C₂) (s₂₃ : C₂ ⥤ C₃) (s₁₃ : C₁ ⥤ C₃)
    (t₁₂ : D₁ ⥤ D₂) (t₂₃ : D₂ ⥤ D₃) (t₁₃ : D₁ ⥤ D₃)
    (a : s₁₂ ⋙ s₂₃ ≅ s₁₃) (b : t₁₂ ⋙ t₂₃ ≅ t₁₃)
    (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
    (c₁₂ : ∀ K : C₁, t₁₂.obj (F₁.obj K) ⟶ F₂.obj (s₁₂.obj K))
    (c₂₃ : ∀ K : C₂, t₂₃.obj (F₂.obj K) ⟶ F₃.obj (s₂₃.obj K))
    (c₁₃ : ∀ K : C₁, t₁₃.obj (F₁.obj K) ⟶ F₃.obj (s₁₃.obj K)) (K : C₁) : Prop :=
  t₂₃.map (c₁₂ K) ≫ c₂₃ (s₁₂.obj K) ≫ F₃.map (a.hom.app K) =
    b.hom.app (F₁.obj K) ≫ c₁₃ K

variable {A : Type (u + 1)} [CommRing A]
variable {B : Type (u + 1)} [CommRing B]

/-- The published ordinary scalar extension, with its functor type elaborated once.
Source: Stacks 06YY (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def ordinaryScalar (phi : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  scalarExtension phi T

/-- The canonical quotient associator with the published scalar functors displayed.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def ordinaryAssociator (T : Scheme.{u}) (ell : ℕ) {r m n : ℕ}
    (hmr : m ≤ r) (hnm : n ≤ m) :
    ordinaryScalar (FiniteReduction.quotient ell hmr) T ⋙
      ordinaryScalar (FiniteReduction.quotient ell hnm) T ≅
        ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T :=
  ExceptionalCoefficients.quotientAssociator T ell hmr hnm

/-- The inverse component of the existing canonical scalar/pullback comparison.
Source: Stacks 07A4 (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def ordinaryPullbackMap (phi : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A Y) :
    (ordinaryScalar phi X).obj ((ordinaryFinitePullback A f).obj K) ⟶
      (ordinaryFinitePullback B f).obj ((ordinaryScalar phi Y).obj K) :=
  (scalarPullbackIso phi f).inv.app K

/-- The canonical shift comparison of scalar extension, as the mate of exact
restriction's shift. Source: Stacks 06YY
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def scalarShiftIso (phi : A →+* B) (T : Scheme.{u}) (i : ℤ) :
    shiftFunctor _ i ⋙ ordinaryScalar phi T ≅ ordinaryScalar phi T ⋙ shiftFunctor _ i :=
  letI : (ordinaryScalar phi T).CommShift ℤ :=
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology phi)).leftAdjointCommShift ℤ
  (ordinaryScalar phi T).commShiftIso i

/-- The derived scalar counit at a single sheaf, with all localization identifications.
Source: Stacks 06YY (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def scalarSingleMap (phi : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ordinaryScalar phi T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((ProEtale.etaleSheafExtendScalars phi T).obj M) :=
  (ordinaryScalar phi T).map
      ((_root_.DerivedCategory.singleFunctorIsoCompQ
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).hom.app M) ≫
    scalarExtensionRepresentative phi T ((CochainComplex.singleFunctor _ 0).obj M) ≫
    _root_.DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (ProEtale.etaleSheafExtendScalars phi T) (.up ℤ) 0).hom.app M) ≫
    (_root_.DerivedCategory.singleFunctorIsoCompQ
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).inv.app
        ((ProEtale.etaleSheafExtendScalars phi T).obj M)

/-- The root-line reduction, fixed on the root power map and every scalar/root generator.
The derived isomorphism is the actual scalar counit followed by that sheaf map.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
structure CoefficientLineComparison (phi : A →+* B) (N M : ℕ)
    (hA : (N : A) = 0) (hB : (M : B) = 0) (T : Scheme.{u}) where
  roots : T.rootsOfUnitySheaf N ⟶ T.rootsOfUnitySheaf M
  roots_power : roots ≫ kernel.ι (M • 𝟙 T.gmSheaf) =
    (N / M) • kernel.ι (N • 𝟙 T.gmSheaf)
  sheafIso : (ProEtale.etaleSheafExtendScalars phi T).obj
      (Scheme.finiteEtaleTateLine T N A hA) ≅ Scheme.finiteEtaleTateLine T M B hB
  generators : ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
    ((ProEtale.etaleSheafExtendScalarsAdjunction phi T).homEquiv _ _
      sheafIso.hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator B M T hB W (phi a) (roots.hom.app W z)
  derivedIso : (ordinaryScalar phi T).obj (ordinaryFiniteLine A N hA T) ≅
    ordinaryFiniteLine B M hB T
  derived_normalization : derivedIso.hom =
    scalarSingleMap phi T (Scheme.finiteEtaleTateLine T N A hA) ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map sheafIso.hom

/-- The zero-fold root comparison is the canonical scalar unit comparison.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def scalarZeroLineIso (phi : A →+* B) (N M : ℕ) (hA : (N : A) = 0)
    (hB : (M : B) = 0) (T : Scheme.{u}) :
    (ordinaryScalar phi T).obj (line A N hA T 0) ≅ line B M hB T 0 :=
  (ordinaryScalar phi T).mapIso
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T) ≪≫
    ExceptionalCoefficients.unitIso phi T ≪≫
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} B) T).symm

/-- One step of root-tensor reduction, using scalar tensor and shift comparisons.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def CoefficientLineComparison.tensorPowerStep {phi : A →+* B} {N M : ℕ}
    {hA : (N : A) = 0} {hB : (M : B) = 0} {T : Scheme.{u}}
    (e : CoefficientLineComparison phi N M hA hB T) (d : ℕ)
    (previous : (ordinaryScalar phi T).obj (line A N hA T d) ≅ line B M hB T d) :
    (ordinaryScalar phi T).obj (line A N hA T (d + 1)) ≅ line B M hB T (d + 1) :=
  (ExceptionalCoefficients.tensorIso phi T).app
      (line A N hA T d, (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} B) T).mapIso previous).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} B) T).obj (line B M hB T d)).mapIso
      ((scalarShiftIso phi T (2 : ℤ)).app _ ≪≫
        (shiftFunctor _ (2 : ℤ)).mapIso e.derivedIso)

/-- Canonical reduction of the ordered shifted tensor: scalar unit at zero, then
normalized tensor and shift comparisons on each concrete root-line factor.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def CoefficientLineComparison.tensorPower {phi : A →+* B} {N M : ℕ}
    {hA : (N : A) = 0} {hB : (M : B) = 0} {T : Scheme.{u}}
    (e : CoefficientLineComparison phi N M hA hB T) (d : ℕ) :
    (ordinaryScalar phi T).obj (line A N hA T d) ≅ line B M hB T d :=
  Nat.rec (motive := fun i ↦
    (ordinaryScalar phi T).obj (line A N hA T i) ≅ line B M hB T i)
    (scalarZeroLineIso phi N M hA hB T) (fun i previous ↦ e.tensorPowerStep i previous) d

/-- Lambda is scalar/tensor balancing, scalar/pullback balancing, then the normalized
root-line reduction. Source: sk-lem-sp-reduction/compatibilities (3)
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def pullbackTwistComparison {phi : A →+* B} {N M : ℕ}
    {hA : (N : A) = 0} {hB : (M : B) = 0} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) (e : CoefficientLineComparison phi N M hA hB X)
    (K : DerivedCategoryModule A Y) :
    (ordinaryScalar phi X).obj ((puritySource A f (line A N hA X d)).obj K) ≅
      (puritySource B f (line B M hB X d)).obj ((ordinaryScalar phi Y).obj K) :=
  (ExceptionalCoefficients.tensorIso phi X).app
      ((ordinaryFinitePullback A f).obj K, line A N hA X d) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).mapIso
      (((scalarPullbackIso phi f).app K).symm)).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((ordinaryFinitePullback B f).obj
        ((ordinaryScalar phi Y).obj K))).mapIso (e.tensorPower d)



/-- Coefficient extension on the pro-etale site, fixed by its adjunction to restriction.
Source: Stacks 06YY (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proScalar (phi : A →+* B) (T : Scheme.{u}) :
    proCategory A T ⥤ proCategory B T :=
  @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (Scheme.ProEt.topology T)
    A B inferInstance inferInstance phi

/-- The origin/scalar comparison is the transpose of the inverse of the specified
site/scalar comparison followed by scalar extension of the comparison counit.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def originReductionMap (phi : A →+* B) (T : Scheme.{u}) (K : proCategory A T) :
    (ordinaryScalar phi T).obj ((origin A T).obj K) ⟶
      (origin B T).obj ((proScalar phi T).obj K) :=
  (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) T).homEquiv _ _
    ((ProEtale.pbcComparisonReduction T phi).inv.app ((origin A T).obj K) ≫
      (proScalar phi T).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K))

/-- Reduction of the actual comparison root line, with the canonical site/scalar mate.
Source: sk-lem-sp-reduction/compatibilities (3)
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proTwistMap {phi : A →+* B} {N M : ℕ} {hA : (N : A) = 0} {hB : (M : B) = 0}
    {T : Scheme.{u}} (d : ℕ) (e : CoefficientLineComparison phi N M hA hB T) :
    (proScalar phi T).obj ((comparison A T).obj (line A N hA T d)) ⟶
      (comparison B T).obj (line B M hB T d) :=
  (ProEtale.pbcComparisonReduction T phi).hom.app (line A N hA T d) ≫
    (comparison B T).map (e.tensorPower d).hom

/-- The pure pullback comparison toward the chosen ordinary origin.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def pullbackToOrigin {X Y : Scheme.{u}} (f : X ⟶ Y) (K : proCategory A Y) :
    (proPullback A f).obj K ⟶
      (comparison A X).obj
        ((ordinaryFinitePullback A f).obj ((origin A Y).obj K)) :=
  (proPullback A f).map
      (originInverse A Y K) ≫
    (sitePullbackIso A f).hom.app ((origin A Y).obj K)

/-- The reverse pure pullback comparison, using the actual origin counit.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def pullbackFromOrigin {X Y : Scheme.{u}} (f : X ⟶ Y) (K : proCategory A Y) :
    (comparison A X).obj
        ((ordinaryFinitePullback A f).obj ((origin A Y).obj K)) ⟶
      (proPullback A f).obj K :=
  (sitePullbackIso A f).inv.app ((origin A Y).obj K) ≫
    (proPullback A f).map
      ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K)

/-- Scalar/pullback balancing on the original pro-etale object. Both origin counits
are displayed in the preceding comparisons, so this transports ordinary balancing.
Source: sk-lem-sp-reduction/compatibilities (3)
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proPullbackMap (phi : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : proCategory A Y) :
    (proScalar phi X).obj
        ((proPullback A f).obj K) ⟶
      (proPullback B f).obj
        ((proScalar phi Y).obj K) :=
  (proScalar phi X).map (pullbackToOrigin f K) ≫
    (ProEtale.pbcComparisonReduction X phi).hom.app
      ((ordinaryFinitePullback A f).obj ((origin A Y).obj K)) ≫
    (comparison B X).map
      ((scalarPullbackIso phi f).inv.app ((origin A Y).obj K) ≫
        (ordinaryFinitePullback B f).map
          (originReductionMap phi Y K)) ≫
    pullbackFromOrigin f ((proScalar phi Y).obj K)

/-- The exceptional comparison on pro-etale Dctf is the transport of the specified
ordinary counit transpose, through the canonical site/scalar and origin comparisons.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proCoefficientMap [Finite A] [Finite B] (phi : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (K : proCategory A Y) :
    (proScalar phi X).obj ((exceptional A f).obj K) ⟶
      (exceptional B f).obj ((proScalar phi Y).obj K) :=
  (ProEtale.pbcComparisonReduction X phi).hom.app
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj ((origin A Y).obj K)) ≫
    (comparison B X).map
      (ExceptionalCoefficients.mateMap phi f ((origin A Y).obj K) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).map (originReductionMap phi Y K))

/-- Lambda on the actual pro-etale source, with each scalar, pullback, twist, and
origin transport displayed. Source: sk-lem-sp-reduction/compatibilities (3)
(blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proLambda [Finite A] [Finite B] {phi : A →+* B} {N M : ℕ} {hA : (N : A) = 0} {hB : (M : B) = 0}
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (e : CoefficientLineComparison phi N M hA hB X)
    (K : proCategory A Y) :
    (proScalar phi X).obj ((proSource A f (line A N hA X d)).obj K) ⟶
      (proSource B f (line B M hB X d)).obj ((proScalar phi Y).obj K) :=
  (proScalar phi X).map (sourceToOrigin A f (line A N hA X d) K) ≫
    (ProEtale.pbcComparisonReduction X phi).hom.app
      ((puritySource A f (line A N hA X d)).obj ((origin A Y).obj K)) ≫
    (comparison B X).map
      ((pullbackTwistComparison f d e ((origin A Y).obj K)).hom ≫
        (puritySource B f (line B M hB X d)).map (originReductionMap phi Y K)) ≫
    sourceFromOrigin B f (line B M hB X d) ((proScalar phi Y).obj K)



/-- Transport of the canonical compactification coefficient map, through the same
proper/open site comparisons and origin counits used for the adjunction.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proCompactCoefficientMap [Finite A] [Finite B] (phi : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (M : proCategory A X) :
    (proScalar phi Y).obj ((proCompact A f).obj M) ⟶
      (proCompact B f).obj ((proScalar phi X).obj M) :=
  (proScalar phi Y).map
      ((proCompact A f).map (originInverse A X M) ≫
        compactSiteMap A f ((origin A X).obj M)) ≫
    (ProEtale.pbcComparisonReduction Y phi).hom.app
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj ((origin A X).obj M)) ≫
    (comparison B Y).map
      (ExceptionalCoefficients.compactSupportMap phi
        (HasCompactification.compactification f) ((origin A X).obj M)) ≫
    compactSiteInverse B f ((ordinaryScalar phi X).obj ((origin A X).obj M)) ≫
    (proCompact B f).map
      ((ProEtale.pbcComparisonReduction X phi).inv.app ((origin A X).obj M) ≫
        (proScalar phi X).map
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app M))

/-- The inverse coefficient comparison on its isomorphism locus.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def proCompactCoefficientInverse [Finite A] [Finite B] (phi : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (M : proCategory A X) :
    (proCompact B f).obj ((proScalar phi X).obj M) ⟶
      (proScalar phi Y).obj ((proCompact A f).obj M) :=
  open Classical in
  if h : IsIso (proCompactCoefficientMap phi f M) then
    @inv _ _ _ _ (proCompactCoefficientMap phi f M) h
  else 0


/-- Lambda at literal quotient levels, with every ring and annihilator fixed explicitly.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def finiteLambda (ell : ℕ) {r m : ℕ} (hmr : m ≤ r) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ)
    (e : CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X)
    (K : DerivedCategoryModule (coefficient ell r) Y) :
    (ordinaryScalar (FiniteReduction.quotient ell hmr) X).obj ((finiteSource ell r f d).obj K) ⟶
      (finiteSource ell m f d).obj
        ((ordinaryScalar (FiniteReduction.quotient ell hmr) Y).obj K) :=
  (pullbackTwistComparison (A := coefficient ell r) (B := coefficient ell m)
    (phi := FiniteReduction.quotient ell hmr) (N := ell ^ r) (M := ell ^ m)
    (hA := CharP.cast_eq_zero _ _) (hB := CharP.cast_eq_zero _ _) f d e K).hom

/-- The actual pro-etale lambda at literal quotient levels, with explicit coefficient data.
Source: sk-lem-sp-reduction (blueprint: def-pur-finite-smooth-coefficient-arrows). -/
def finiteProLambda (ell : ℕ) [Fact ell.Prime] {r m : ℕ} (hmr : m ≤ r)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (e : CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X)
    (K : proCategory (coefficient ell r) Y) :
    (proScalar (FiniteReduction.quotient ell hmr) X).obj ((finiteProSource ell r f d).obj K) ⟶
      (finiteProSource ell m f d).obj
        ((proScalar (FiniteReduction.quotient ell hmr) Y).obj K) :=
  proLambda (A := coefficient ell r) (B := coefficient ell m)
    (phi := FiniteReduction.quotient ell hmr) (N := ell ^ r) (M := ell ^ m)
    (hA := CharP.cast_eq_zero _ _) (hB := CharP.cast_eq_zero _ _) f d e K

end AlgebraicGeometry.Etale.FiniteSmoothPurity
