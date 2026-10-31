/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.OpenExternalTensorNormalization
public import WeilConjectures.SixFunctors.ProductCompactificationIdentity
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.SecSmoothPurity.CondensedOpenBaseChangeArbitrary
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients

import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
import WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange
import WeilConjectures.SecSmoothPurity.DetPropSfCbc
import WeilConjectures.AlgebraicGeometry.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.CondensedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.CondensedOpenDerivedCalculus
import WeilConjectures.SixFunctors.CondensedTowerCompositorNormalization
import WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting
import WeilConjectures.AlgebraicGeometry.CondensedCtfSixFunctorStability

/-!
# Native condensed product compactification comparison

Source: latest blueprint, sk-thm-sf-kunneth-relative, Coherence (i), reduction to proper
morphisms (blueprint: lem-sf-condensed-product-compactification-map).
The helpers spell out the canonical open comparison and the forward word, on ordinary
uncompleted module derived categories. No coefficient-system realization is involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedRing.ProductCompactificationMap
open CompactificationReindexing
open AlgebraicGeometry.ProEtale.OpenExternalTensor (Diagram Triple)

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Native tensor helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tensor (X : Scheme.{u}) (K L : D Λ X) : D Λ X := K ⊗ L

/-- Native tensorMap helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tensorMap (X : Scheme.{u}) {K K' L L' : D Λ X}
    (a : K ⟶ K') (b : L ⟶ L') := a ⊗ₘ b

/-- Native tensorIsoMap helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tensorIsoMap (X : Scheme.{u}) {K K' L L' : D Λ X}
    (a : K ≅ K') (b : L ≅ L') := tensorIso a b

/-- Native sigma helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def sigma (X : Scheme.{u}) (K L : D Λ X) :=
  (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) K L).hom

/-- Native tensorPullIso helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tensorPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) (K L : D Λ Y) :=
  ((leftDerivedUpperStarTensorIso Λ f).app K).app L

/-- Native square helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def square {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Z)
    (h : T ⟶ Y) (i : Y ⟶ Z) (e : f ≫ g = h ≫ i) :
    P Λ g ⋙ P Λ f ≅ P Λ i ⋙ P Λ h :=
  (leftDerivedUpperStarComp Λ f g).symm ≪≫
    eqToIso (congrArg (P Λ) e) ≪≫ leftDerivedUpperStarComp Λ h i

/-- Native shriekCongr helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def shriekCongr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : J Λ f ≅ J Λ g :=
  eqToIso (by cases h; rfl)

/-- Native gamma helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def gamma {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : D Λ X) (L : D Λ Y) := inv (openImmersionProjectionComparison Λ j K L)

/-- Native rho helper for the open-product comparison.
Source: the displayed open-product construction, blueprint Coherence (i)
(blueprint: lem-sf-condensed-product-compactification-map). -/
def rho {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : D Λ Y) (L : D Λ X) :=
  sigma Λ Y K ((J Λ j).obj L) ≫ gamma Λ j L K ≫
    (J Λ j).map (sigma Λ X L ((P Λ j).obj K))

variable {X Y Xb Yb T Tb : Scheme.{u}} {j : X ⟶ Xb} {k : Y ⟶ Yb}
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The ambient external product of the two extensions.
Source: the definition of H in proof step 6
(blueprint: lem-sf-condensed-product-compactification-map). -/
def ambient (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : D Λ Tb :=
  tensor Λ Tb
    ((P Λ d.pb).obj ((J Λ j).obj K))
    ((P Λ d.qb).obj ((J Λ k).obj L))

/-- The external product on the open.
Source: D in the statement (blueprint: lem-sf-condensed-product-compactification-map). -/
def inside (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : D Λ T :=
  tensor Λ T
    ((P Λ d.p).obj K) ((P Λ d.q).obj L)

/-- The prescribed first-factor construction: beta for j, gamma for j₁, beta for k,
then signed symmetry, gamma for k₁, signed symmetry inside k₁!, and the normalized
composition comparison. All equalities are transported by pullback composition.
Source: proof steps 3 and 4, Stacks 03S6 and 0GL1
(blueprint: lem-sf-condensed-product-compactification-map). -/
def comparison (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :=
  tensorMap Λ Tb
      ((beta Λ d.first).hom.app K) (𝟙 _) ≫
    gamma Λ d.j₁ ((P Λ d.r).obj K)
      ((P Λ d.qb).obj ((J Λ k).obj L)) ≫
    (J Λ d.j₁).map
      (tensorMap Λ d.S (𝟙 _)
        (((leftDerivedUpperStarComp Λ d.j₁ d.qb).symm ≪≫
          eqToIso (congrArg (P Λ) d.j₁_qb)).hom.app
            ((J Λ k).obj L))) ≫
    (J Λ d.j₁).map
      (tensorMap Λ d.S (𝟙 _)
        ((beta Λ d.second).hom.app L)) ≫
    (J Λ d.j₁).map
      (rho Λ d.k₁
        ((P Λ d.r).obj K) ((P Λ d.q).obj L) ≫
        (J Λ d.k₁).map
          (tensorMap Λ T
            (((leftDerivedUpperStarComp Λ d.k₁ d.r).symm ≪≫
              eqToIso (congrArg (P Λ) d.k₁_r)).hom.app K) (𝟙 _))) ≫
    (CompactSupportComposition.openFactor Λ d.k₁ d.j₁ d.u d.factor).hom.app (inside Λ d K L)

/-- Identify D with the restriction of H by the inverse tensor comparison, the two
projection squares and the section-normalized open units.
Source: proof step 5 (blueprint: lem-sf-condensed-product-compactification-map). -/
def restriction (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :=
  tensorMap Λ T
    ((P Λ d.p).map ((oa Λ j).unit.app K) ≫
      (square Λ _ _ _ _ d.left).inv.app ((J Λ j).obj K))
    ((P Λ d.q).map ((oa Λ k).unit.app L) ≫
      (square Λ _ _ _ _ d.right).inv.app ((J Λ k).obj L)) ≫
    (tensorPullIso Λ d.u _ _).inv

/-- The other factorization, with both signed interchanges in the specified places.
Source: proof step 6 (blueprint: lem-sf-condensed-product-compactification-map). -/
def oppositeComparison (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :=
  sigma Λ Tb _ _ ≫ comparison Λ d.swap L K ≫
    (J Λ d.u).map (sigma Λ T _ _)

/-- The binary normalization, opposite-factorization and signed-symmetry equations.
The symmetry is written after transporting the swapped products to the same cones.
Source: proof steps 5--7 (blueprint: lem-sf-condensed-product-compactification-map). -/
def BinaryAssertion (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : Prop :=
  IsIso (comparison Λ d K L) ∧ IsIso (oppositeComparison Λ d K L) ∧
    (restriction Λ d K L ≫ (P Λ d.u).map (comparison Λ d K L) =
      (oa Λ d.u).unit.app (inside Λ d K L)) ∧
    (oppositeComparison Λ d K L = comparison Λ d K L) ∧
    (comparison Λ d K L ≫ (J Λ d.u).map
        (sigma Λ T
          ((P Λ d.p).obj K) ((P Λ d.q).obj L)) =
      sigma Λ Tb
          ((P Λ d.pb).obj ((J Λ j).obj K))
          ((P Λ d.qb).obj ((J Λ k).obj L)) ≫
        comparison Λ d.swap L K)

variable {W Wb T₁₂ T₂₃ Tb₁₂ Tb₂₃ : Scheme.{u}} {l : W ⟶ Wb}
  [IsOpenImmersion l]

/-- The triple ambient object, with left bracketing and composed projection pullbacks.
Source: H₃ in proof step 8 (blueprint: lem-sf-condensed-product-compactification-map). -/
def tripleAmbient (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) : D Λ Tb :=
  tensor Λ Tb
    (tensor Λ Tb
      ((P Λ dL.pb).obj
        ((P Λ d₁₂.pb).obj ((J Λ j).obj K)))
      ((P Λ dL.pb).obj
        ((P Λ d₁₂.qb).obj ((J Λ k).obj L))))
    ((P Λ dL.qb).obj ((J Λ l).obj M))

/-- The triple open object with the same left bracketing.
Source: D₃ in proof step 8 (blueprint: lem-sf-condensed-product-compactification-map). -/
def tripleInside (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) : D Λ T :=
  tensor Λ T
    (tensor Λ T
      ((P Λ dL.p).obj ((P Λ d₁₂.p).obj K))
      ((P Λ dL.p).obj ((P Λ d₁₂.q).obj L)))
    ((P Λ dL.q).obj M)

/-- First compare the first two factors, then their product with the third.
Source: F in proof step 8 (blueprint: lem-sf-condensed-product-compactification-map). -/
def tripleLeft (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) :=
  (tensorIsoMap Λ _
    (tensorPullIso Λ dL.pb _ _).symm (Iso.refl _)).hom ≫
    tensorMap Λ Tb
      ((P Λ dL.pb).map (comparison Λ d₁₂ K L)) (𝟙 _) ≫
    comparison Λ dL (inside Λ d₁₂ K L) M ≫
    (J Λ dL.u).map
      (tensorIsoMap Λ _
        (tensorPullIso Λ dL.p _ _) (Iso.refl _)).hom

/-- The canonical outer reassociation and projection-composition identification.
Source: the ambient associator in proof step 8
(blueprint: lem-sf-condensed-product-compactification-map). -/
def outerAssociator
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) :
    tripleAmbient Λ d₁₂ dL K L M ≅
      tensor Λ Tb
        ((P Λ dR.pb).obj ((J Λ j).obj K))
        ((P Λ dR.qb).obj (ambient Λ d₂₃ L M)) :=
  tensorIsoMap Λ _ (tensorIsoMap Λ _
      (((leftDerivedUpperStarComp Λ dL.pb d₁₂.pb).symm ≪≫
        eqToIso (congrArg (P Λ) t.outer₁)).app ((J Λ j).obj K))
      ((square Λ _ _ _ _ t.outer₂).app ((J Λ k).obj L)))
    ((eqToIso (congrArg (P Λ) t.outer₃) ≪≫
      leftDerivedUpperStarComp Λ dR.qb d₂₃.qb).app ((J Λ l).obj M)) ≪≫
    (α_ _ _ _) ≪≫
      tensorIsoMap Λ _ (Iso.refl _)
      (tensorPullIso Λ dR.qb _ _).symm

/-- Reassociate the open factors using exactly the same projection-composition maps.
Source: the open associator in proof step 8
(blueprint: lem-sf-condensed-product-compactification-map). -/
def innerAssociator
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) :
    inside Λ dR K (inside Λ d₂₃ L M) ≅ tripleInside Λ d₁₂ dL K L M :=
  tensorIsoMap Λ _ (Iso.refl _) (tensorPullIso Λ dR.q _ _) ≪≫
    tensorIsoMap Λ _
      (((eqToIso (congrArg (P Λ) t.inner₁)).symm ≪≫
        leftDerivedUpperStarComp Λ dL.p d₁₂.p).app K)
      (tensorIsoMap Λ _ ((square Λ _ _ _ _ t.inner₂).symm.app L)
        (((leftDerivedUpperStarComp Λ dR.q d₂₃.q).symm ≪≫
          eqToIso (congrArg (P Λ) t.inner₃.symm)).app M)) ≪≫
    (α_ _ _ _).symm

/-- First compare the last two factors, then the first factor with their product.
The final transport is the identity of the common product open, followed by its
canonical associator. Source: G in proof step 8
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tripleRight
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) :=
  (outerAssociator Λ t K L M).hom ≫
    tensorMap Λ Tb (𝟙 _)
      ((P Λ dR.qb).map (comparison Λ d₂₃ L M)) ≫
    comparison Λ dR K (inside Λ d₂₃ L M) ≫
    (J Λ dR.u).map (innerAssociator Λ t K L M).hom ≫
    (shriekCongr Λ t.sameOpen).hom.app (tripleInside Λ d₁₂ dL K L M)

/-- The triple restriction uses the same section units and tensor comparisons on
both sides; it contains no occurrence of either triple comparison.
Source: the identity-on-the-open clause in proof step 8
(blueprint: lem-sf-condensed-product-compactification-map). -/
def tripleRestriction (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) :=
  tensorMap Λ T
    ((tensorPullIso Λ dL.p _ _).inv ≫
      (P Λ dL.p).map (restriction Λ d₁₂ K L) ≫
        (square Λ _ _ _ _ dL.left).inv.app (ambient Λ d₁₂ K L))
    ((P Λ dL.q).map ((oa Λ l).unit.app M) ≫
      (square Λ _ _ _ _ dL.right).inv.app ((J Λ l).obj M)) ≫
    (tensorPullIso Λ dL.u _ _).inv ≫
    (P Λ dL.u).map
      (tensorIsoMap Λ _
        (tensorPullIso Λ dL.pb _ _) (Iso.refl _)).hom

/-- Equality of the two triple composites, and their separate identity restrictions.
Source: proof step 8 (blueprint: lem-sf-condensed-product-compactification-map). -/
def TripleAssertion
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) : Prop :=
  tripleLeft Λ d₁₂ dL K L M = tripleRight Λ t K L M ∧
    (tripleRestriction Λ d₁₂ dL K L M ≫
      (P Λ dL.u).map (tripleLeft Λ d₁₂ dL K L M) =
        (oa Λ dL.u).unit.app
          (tripleInside Λ d₁₂ dL K L M)) ∧
    (tripleRestriction Λ d₁₂ dL K L M ≫
      (P Λ dL.u).map (tripleRight Λ t K L M) =
        (oa Λ dL.u).unit.app
          (tripleInside Λ d₁₂ dL K L M))



/-- The ordered forward word before the final compact-support compositor: symmetry,
projection, symmetry, exchange tensor identity, projection. Source: displayed lambda
(blueprint: lem-sf-condensed-product-compactification-map). -/
def chain {k₀ : Type u} [Field k₀]
    (H : CompactSupportComposition.CoherentData Λ k₀)
    {T X Y B : SepFinType k₀} {p : T.obj.left ⟶ X.obj.left}
    {q : T ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : IsPullback p q.hom.left f.hom.left g.hom.left)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cq : Compactification q.hom.left)
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) (L : D Λ Y.obj.left) :=
  sigma Λ B.obj.left ((F Λ cf).obj K.obj) ((F Λ cg).obj L) ≫
    pf Λ cg L ((F Λ cf).obj K.obj) ≫
    (F Λ cg).map
      (sigma Λ Y.obj.left L ((P Λ g.hom.left).obj ((F Λ cf).obj K.obj)) ≫
        ((H.exchange sq cf cq).hom.app K ⊗ₘ 𝟙 L) ≫
        pf Λ cq ((P Λ p).obj K.obj) L)

/-- The final arrow in the displayed word is the canonical normalized compositor,
evaluated in its localizing domain. Source: alpha in the item
(blueprint: lem-sf-condensed-product-compactification-map). -/
def forwardWord {k₀ : Type u} [Field k₀]
    (H : CompactSupportComposition.CoherentData Λ k₀)
    {T X Y B : SepFinType k₀} {p : T.obj.left ⟶ X.obj.left}
    {q : T ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : IsPullback p q.hom.left f.hom.left g.hom.left)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cq : Compactification q.hom.left)
    (ct : Compactification (q.hom.left ≫ g.hom.left))
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) (L : D Λ Y.obj.left)
    (hM : localizingClosureProEtale Λ T.obj.left
      ((P Λ p).obj K.obj ⊗ (P Λ q.hom.left).obj L)) :=
  chain Λ H sq cf cg cq K L ≫
    (H.comp q g cq cg ct).hom.app ⟨_, hM⟩

/-- The same ordered word on proper models, with the native direct-image compositor.
Source: lambda_{a,b} in the concluding equation
(blueprint: lem-sf-condensed-product-compactification-map). -/
def properWord {T X Y B : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g)
    (K : D Λ X) (L : D Λ Y) :=
  sigma Λ B ((R Λ f).obj K) ((R Λ g).obj L) ≫
    properProjectionMorphism Λ g L ((R Λ f).obj K) ≫
    (R Λ g).map
      (sigma Λ Y L ((P Λ g).obj ((R Λ f).obj K)) ≫
        ((baseChangeMap Λ sq.toCommSq).app K ⊗ₘ 𝟙 L) ≫
        properProjectionMorphism Λ q ((P Λ p).obj K) L) ≫
    (rightDerivedLowerStarComp Λ q g).hom.app
      ((P Λ p).obj K ⊗ (P Λ q).obj L)

/-- Regard a projection as its k-morphism, using its structural equation.
Source: the supplied fibre products over B
(blueprint: lem-sf-condensed-product-compactification-map). -/
def overHom {k₀ : Type u} [Field k₀] {X Y : SepFinType k₀}
    (f : X.obj.left ⟶ Y.obj.left) (h : f ≫ Y.obj.hom = X.obj.hom) : X ⟶ Y :=
  ObjectProperty.homMk (Over.homMk f h)

/-- The existing inclusion of constructible finite-Tor objects in their localizing
closure, with the object unchanged. Source: composition theorem, domain C
(blueprint: lem-sf-condensed-product-compactification-map). -/
def localizingObject (X : Scheme.{u}) (K : ConstantModelConstructibleFiniteTor Λ X) :
    (localizingClosureProEtale Λ X).FullSubcategory :=
  ⟨K.obj, fun _P _hP hS ↦ hS K.obj K.property⟩

/-- The native open product is invertible, restricts to identity, and is independent
of the factorization with the signed swap equation.
Source: Coherence (i), open-product normalization
(blueprint: lem-sf-condensed-product-compactification-map).
Proof: open base change and the open projection maps are invertible. Their normalized
units show term by term that comparison restricts to identity. The opposite chain has
the same restriction. The invertible open unit makes extension fully faithful, so the
two maps agree. Apply the same argument after signed factor interchange. The two Koszul
signs cancel on restriction. No reduction of coefficients is used. -/
theorem openProduct_normalization
    (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : BinaryAssertion Λ d K L := by
  sorry

/-- Three-factor associativity of the same canonical open comparison.
Source: Coherence (i), three-factor normalization
(blueprint: lem-sf-condensed-product-compactification-map).
Proof: pull back both bracketings to the open triple product. The normalized binary
maps are identities, and native pullback/tensor coherence identifies both associators
with the signed total-tensor associator. Full faithfulness of the product open extension
then identifies the two maps before restriction. -/
theorem openProduct_associativity
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) : TripleAssertion Λ t K L M := by
  sorry

/-- The native forward exchange/projection word equals the proper word followed by
the direct image of the constructed open-product comparison. The existential proof
only records membership in the compositor's domain; it supplies no map or comparison.
Source: latest blueprint sk-thm-sf-kunneth-relative, Coherence (i), reduction to proper
morphisms (blueprint: lem-sf-condensed-product-compactification-map).
Proof: pullbacks and tensor preserve C, hence the external tensor belongs to Loc(C).
Expand both words with the supplied compactifications. Removing the first open uses
exchange and projection naturality and gives the one-open comparison. For the second
open, take proper adjuncts. After restriction to the supported open, both adjuncts
are the proper counit tensor identity: mate compatibility identifies the restricted
counit, and normalized proper/open interchange cancels its inverse. The supported
source is an open extension, so the open Hom bijection gives equality before
restriction. The normalized tower compositor identifies these expansions with alpha.
Assembling the two one-open comparisons gives exactly comparison, with no inverse
projection formula and no assumed invertibility of the forward word. -/
theorem forwardWord_product_compactification
    (ℓ ch : ℕ) [Fact ℓ.Prime] [Fact ch.Prime] (hch : ch ≠ ℓ)
    (k₀ : Type u) [Field k₀] [CharP k₀ ch]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (H : CompactSupportComposition.CoherentData Λ k₀)
    {B X₀ Y₀ Xb₀ Yb₀ T₀ Tb₀ : SepFinType k₀}
    (j₀ : X₀ ⟶ Xb₀) (k₁ : Y₀ ⟶ Yb₀)
    (a : Xb₀ ⟶ B) (b : Yb₀ ⟶ B)
    [IsOpenImmersion j₀.hom.left] [IsOpenImmersion k₁.hom.left]
    [IsProper a.hom.left] [IsProper b.hom.left]
    (d : Diagram j₀.hom.left k₁.hom.left T₀.obj.left Tb₀.obj.left)
    (hq : d.q ≫ Y₀.obj.hom = T₀.obj.hom)
    (sq : IsPullback d.p d.q (j₀.hom.left ≫ a.hom.left)
      (k₁.hom.left ≫ b.hom.left))
    (sqb : IsPullback d.pb d.qb a.hom.left b.hom.left)
    (K : ConstantModelConstructibleFiniteTor Λ X₀.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ Y₀.obj.left) :
    ∃ hM : localizingClosureProEtale Λ T₀.obj.left (inside Λ d K.obj L.obj),
      forwardWord Λ H (q := overHom d.q hq) (f := j₀ ≫ a) (g := k₁ ≫ b) sq
        (ProEtale.ProductCompactification.factorCompactification j₀.hom.left a.hom.left)
        (ProEtale.ProductCompactification.factorCompactification k₁.hom.left b.hom.left)
        ((ProEtale.ProductCompactification.factorCompactification
          j₀.hom.left a.hom.left).ofIsPullback sq)
        (ProEtale.ProductCompactification.productCompactification a.hom.left b.hom.left d sqb)
        (localizingObject Λ X₀.obj.left K) L.obj hM =
      properWord Λ sqb ((J Λ j₀.hom.left).obj K.obj) ((J Λ k₁.hom.left).obj L.obj) ≫
        (R Λ (d.qb ≫ b.hom.left)).map (comparison Λ d K.obj L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.ProductCompactificationMap
