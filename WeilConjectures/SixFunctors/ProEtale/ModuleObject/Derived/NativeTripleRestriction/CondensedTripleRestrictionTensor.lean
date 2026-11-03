/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTripleRestriction.CondensedTripleRestrictionLegs

/-! # Tensor rebracketing of the original three open section units

Source: the coherence paragraph, three-factor normalization in the latest blueprint
`sk-thm-sf-kunneth-relative.proof.md`. These maps use section units and pullback
comparisons only; neither binary open-product comparison occurs in them.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeTripleRestriction
open CompactificationReindexing
open AlgebraicGeometry.ProEtale.OpenExternalTensor (Diagram Triple)

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp pullbackSquareComparison
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical native tensor-pullback comparison.
Source: tensor comparison in three-factor normalization
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def tensorPull {X Y : Scheme.{u}} (f : X ⟶ Y) (K L : D Λ Y) :
    (P Λ f).obj (K ⊗ L) ≅ (P Λ f).obj K ⊗ (P Λ f).obj L :=
  ((leftDerivedUpperStarTensorIso Λ f).app K).app L

variable {X Y Xb Yb T Tb : Scheme.{u}} {j : X ⟶ Xb} {k : Y ⟶ Yb}
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The ambient binary tensor before restriction.
Source: original two section units
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def ambient (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : D Λ Tb :=
  (P Λ d.pb).obj ((J Λ j).obj K) ⊗ (P Λ d.qb).obj ((J Λ k).obj L)

/-- The binary open tensor.
Source: original two section units
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def inside (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) : D Λ T :=
  (P Λ d.p).obj K ⊗ (P Λ d.q).obj L

/-- Tensor the two section units and collect them with the native tensorator.
Source: binary section-unit restriction, before either comparison
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def binary (d : Diagram j k T Tb) (K : D Λ X) (L : D Λ Y) :
    inside Λ d K L ⟶ (P Λ d.u).obj (ambient Λ d K L) :=
  (leg Λ j d.p d.pb d.u d.left K ⊗ₘ leg Λ k d.q d.qb d.u d.right L) ≫
    (tensorPull Λ d.u _ _).inv

variable {W Wb T₁₂ T₂₃ Tb₁₂ Tb₂₃ : Scheme.{u}} {l : W ⟶ Wb}
  [IsOpenImmersion l]

/-- Left-bracketed ambient threefold tensor.
Source: H3 in the three-factor normalization
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def tripleAmbient (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) : D Λ Tb :=
  ((P Λ dL.pb).obj ((P Λ d₁₂.pb).obj ((J Λ j).obj K)) ⊗
    (P Λ dL.pb).obj ((P Λ d₁₂.qb).obj ((J Λ k).obj L))) ⊗
      (P Λ dL.qb).obj ((J Λ l).obj M)

/-- Left-bracketed open threefold tensor.
Source: D3 in the three-factor normalization
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def tripleInside (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) : D Λ T :=
  ((P Λ dL.p).obj ((P Λ d₁₂.p).obj K) ⊗
    (P Λ dL.p).obj ((P Λ d₁₂.q).obj L)) ⊗ (P Λ dL.q).obj M

/-- Outer projection transports, tensor associator, and final binary tensorator.
Source: ambient reassociation in the three-factor normalization
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def outer
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR) (K : D Λ X) (L : D Λ Y) (M : D Λ W) :
    tripleAmbient Λ d₁₂ dL K L M ≅
      (P Λ dR.pb).obj ((J Λ j).obj K) ⊗ (P Λ dR.qb).obj (ambient Λ d₂₃ L M) :=
  tensorIso (tensorIso (first Λ t K).outside (second Λ t L).outside)
    (third Λ t M).outside ≪≫ (α_ _ _ _) ≪≫
      tensorIso (Iso.refl _) (tensorPull Λ dR.qb _ _).symm

/-- Inner tensorator followed by the inverse projection transports and reassociation.
Source: open reassociation in the three-factor normalization
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def inner
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR) (K : D Λ X) (L : D Λ Y) (M : D Λ W) :
    inside Λ dR K (inside Λ d₂₃ L M) ≅ tripleInside Λ d₁₂ dL K L M :=
  tensorIso (Iso.refl _) (tensorPull Λ dR.q _ _) ≪≫
    tensorIso (first Λ t K).inside
      (tensorIso (second Λ t L).inside (third Λ t M).inside) ≪≫ (α_ _ _ _).symm

/-- Original section restriction with the first two factors grouped first.
Source: left-bracketed triple section-unit restriction
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def left
    (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : D Λ X) (L : D Λ Y) (M : D Λ W) :
    tripleInside Λ d₁₂ dL K L M ⟶ (P Λ dL.u).obj (tripleAmbient Λ d₁₂ dL K L M) :=
  (((tensorPull Λ dL.p _ _).inv ≫
      (P Λ dL.p).map (binary Λ d₁₂ K L) ≫
        (square Λ _ _ _ _ dL.left).inv.app (ambient Λ d₁₂ K L)) ⊗ₘ
    leg Λ l dL.q dL.qb dL.u dL.right M) ≫
      (tensorPull Λ dL.u _ _).inv ≫
        (P Λ dL.u).map ((tensorPull Λ dL.pb _ _).hom ⊗ₘ 𝟙 _)

/-- Original section restriction with the last two factors grouped first, transported
back to the same triple source and target. All maps are explicit unit and tensor maps.
Source: right-bracketed triple section-unit restriction
(blueprint: lem-sf-condensed-triple-restriction-tensor). -/
def right
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR) (K : D Λ X) (L : D Λ Y) (M : D Λ W) :
    tripleInside Λ d₁₂ dL K L M ⟶ (P Λ dL.u).obj (tripleAmbient Λ d₁₂ dL K L M) :=
  (inner Λ t K L M).inv ≫
    (leg Λ j dR.p dR.pb dR.u dR.left K ⊗ₘ
      ((P Λ dR.q).map (binary Λ d₂₃ L M) ≫
        (square Λ _ _ _ _ dR.right).inv.app (ambient Λ d₂₃ L M))) ≫
    (tensorPull Λ dR.u _ _).inv ≫
    (P Λ dR.u).map (outer Λ t K L M).inv ≫
    (eqToIso (congrArg (P Λ) t.sameOpen)).hom.app _

/-- Tensor rebracketing of three original section units from their scalar path equations.
The scalar equations are a separate cube calculation; this result concerns the tensorators.
Neither side contains the open-product comparison or its inverse.

Source: the coherence paragraph, three-factor identity-on-the-open calculation in
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/`
`sk-thm-sf-kunneth-relative.proof.md`, and proof step 3 of
`lem-sf-condensed-product-compactification-map`.
(blueprint: lem-sf-condensed-triple-restriction-tensor).

Proof: expand binary restriction in both sides. Naturality of the native tensor-pullback
comparison moves each pair of section maps out of the pullback. Monoidality of each
projection-square comparison distributes it over those two factors. On the left this
gives the tensor of `first.left`, `second.left`, `third.left` followed by the two
left-bracketed tensorators of the product-open pullback. On the right it gives the
corresponding right scalar paths and the two right-bracketed tensorators. Substitute
the three supplied scalar equations. Naturality of the tensor associator moves the
three scalar maps across it. The strong monoidal associativity equation for the
product-open pullback identifies the remaining two tensorator composites. Its
monoidality under equality of the two product-open maps transports the last equation
along `sameOpen`. Cancel each paired inverse tensorator. The surviving equality is
exactly `left = right`. This calculation uses the native signed derived associators;
no unsigned replacement or invertibility of section maps is used.
-/
theorem tensor_rebracketing
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR) (K : D Λ X) (L : D Λ Y) (M : D Λ W)
    (h₁ : (first Λ t K).Commutes Λ t.sameOpen)
    (h₂ : (second Λ t L).Commutes Λ t.sameOpen)
    (h₃ : (third Λ t M).Commutes Λ t.sameOpen) :
    left Λ d₁₂ dL K L M = right Λ t K L M := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NativeTripleRestriction
