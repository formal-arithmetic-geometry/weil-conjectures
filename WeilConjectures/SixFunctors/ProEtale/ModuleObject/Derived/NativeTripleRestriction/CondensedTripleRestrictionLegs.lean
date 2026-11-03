/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Picard.FiniteOpenProduct.FiniteOpenProductOperations

/-! # Scalar projection paths in a native triple restriction

Source: the three-factor open-product normalization in the coherence paragraph of the latest
blueprint `sk-thm-sf-kunneth-relative.proof.md`.
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

/-- The native square, oriented from the first projection path to the second.
Source: pullback coherence used in the triple-product calculation
(blueprint: lem-sf-condensed-triple-restriction-legs). -/
def square {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Z)
    (h : T ⟶ Y) (i : Y ⟶ Z) (e : f ≫ g = h ≫ i) :
    P Λ g ⋙ P Λ f ≅ P Λ i ⋙ P Λ h :=
  (leftDerivedUpperStarComp Λ f g).symm ≪≫
    eqToIso (congrArg (P Λ) e) ≪≫ leftDerivedUpperStarComp Λ h i

/-- Restrict one original open-extension unit along a projection square.
Source: the section-unit formula for open-product restriction
(blueprint: lem-sf-condensed-triple-restriction-legs). -/
def leg {X Xb T Tb : Scheme.{u}} (j : X ⟶ Xb) [IsOpenImmersion j]
    (p : T ⟶ X) (pb : Tb ⟶ Xb) (u₀ : T ⟶ Tb) (e : u₀ ≫ pb = p ≫ j)
    (K : D Λ X) : (P Λ p).obj K ⟶ (P Λ u₀).obj ((P Λ pb).obj ((J Λ j).obj K)) :=
  (P Λ p).map ((oa Λ j).unit.app K) ≫
    (square Λ u₀ pb p j e).inv.app ((J Λ j).obj K)

/-- Four endpoints, their reindexing isomorphisms, and the two unit paths for one factor.
All fields below are supplied by the explicit constructions `first`, `second`, `third`.
Source: the three scalar paths of the triple normalization
(blueprint: lem-sf-condensed-triple-restriction-legs). -/
structure LegData {T Tb : Scheme.{u}} (uL uR : T ⟶ Tb) where
  innerLeft : D Λ T
  innerRight : D Λ T
  outerLeft : D Λ Tb
  outerRight : D Λ Tb
  inside : innerRight ≅ innerLeft
  outside : outerLeft ≅ outerRight
  left : innerLeft ⟶ (P Λ uL).obj outerLeft
  right : innerRight ⟶ (P Λ uR).obj outerRight

variable {X Y Xb Yb T Tb : Scheme.{u}} {j : X ⟶ Xb} {k : Y ⟶ Yb}
  [IsOpenImmersion j] [IsOpenImmersion k]
variable {W Wb T₁₂ T₂₃ Tb₁₂ Tb₂₃ : Scheme.{u}} {l : W ⟶ Wb}
  [IsOpenImmersion l]

/-- The first-factor unit paths and projection-composition transports.
Source: first factor of three-factor normalization
(blueprint: lem-sf-condensed-triple-restriction-legs). -/
def first {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR) (K : D Λ X) : LegData Λ dL.u dR.u where
  innerLeft := (P Λ dL.p).obj ((P Λ d₁₂.p).obj K)
  innerRight := (P Λ dR.p).obj K
  outerLeft := (P Λ dL.pb).obj ((P Λ d₁₂.pb).obj ((J Λ j).obj K))
  outerRight := (P Λ dR.pb).obj ((J Λ j).obj K)
  inside := (((eqToIso (congrArg (P Λ) t.inner₁)).symm ≪≫
    leftDerivedUpperStarComp Λ dL.p d₁₂.p).app K)
  outside := (((leftDerivedUpperStarComp Λ dL.pb d₁₂.pb).symm ≪≫
    eqToIso (congrArg (P Λ) t.outer₁)).app ((J Λ j).obj K))
  left := (P Λ dL.p).map (leg Λ j d₁₂.p d₁₂.pb d₁₂.u d₁₂.left K) ≫
    (square Λ _ _ _ _ dL.left).inv.app ((P Λ d₁₂.pb).obj ((J Λ j).obj K))
  right := leg Λ j dR.p dR.pb dR.u dR.left K

/-- The middle-factor paths use the inner and outer middle projection squares.
Source: middle factor of three-factor normalization
(blueprint: lem-sf-condensed-triple-restriction-legs). -/
def second {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR) (L : D Λ Y) : LegData Λ dL.u dR.u where
  innerLeft := (P Λ dL.p).obj ((P Λ d₁₂.q).obj L)
  innerRight := (P Λ dR.q).obj ((P Λ d₂₃.p).obj L)
  outerLeft := (P Λ dL.pb).obj ((P Λ d₁₂.qb).obj ((J Λ k).obj L))
  outerRight := (P Λ dR.qb).obj ((P Λ d₂₃.pb).obj ((J Λ k).obj L))
  inside := (square Λ _ _ _ _ t.inner₂).symm.app L
  outside := (square Λ _ _ _ _ t.outer₂).app ((J Λ k).obj L)
  left := (P Λ dL.p).map (leg Λ k d₁₂.q d₁₂.qb d₁₂.u d₁₂.right L) ≫
    (square Λ _ _ _ _ dL.left).inv.app ((P Λ d₁₂.qb).obj ((J Λ k).obj L))
  right := (P Λ dR.q).map (leg Λ k d₂₃.p d₂₃.pb d₂₃.u d₂₃.left L) ≫
    (square Λ _ _ _ _ dR.right).inv.app ((P Λ d₂₃.pb).obj ((J Λ k).obj L))

/-- The last-factor paths and projection-composition transports.
Source: last factor of three-factor normalization
(blueprint: lem-sf-condensed-triple-restriction-legs). -/
def third {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR) (M : D Λ W) : LegData Λ dL.u dR.u where
  innerLeft := (P Λ dL.q).obj M
  innerRight := (P Λ dR.q).obj ((P Λ d₂₃.q).obj M)
  outerLeft := (P Λ dL.qb).obj ((J Λ l).obj M)
  outerRight := (P Λ dR.qb).obj ((P Λ d₂₃.qb).obj ((J Λ l).obj M))
  inside := (((leftDerivedUpperStarComp Λ dR.q d₂₃.q).symm ≪≫
    eqToIso (congrArg (P Λ) t.inner₃.symm)).app M)
  outside := ((eqToIso (congrArg (P Λ) t.outer₃) ≪≫
    leftDerivedUpperStarComp Λ dR.qb d₂₃.qb).app ((J Λ l).obj M))
  left := leg Λ l dL.q dL.qb dL.u dL.right M
  right := (P Λ dR.q).map (leg Λ l d₂₃.q d₂₃.qb d₂₃.u d₂₃.right M) ≫
    (square Λ _ _ _ _ dR.right).inv.app ((P Λ d₂₃.qb).obj ((J Λ l).obj M))

/-- Commutation of a single scalar leg, including equality of the product opens.
Source: the scalar cube in the triple normalization
(blueprint: lem-sf-condensed-triple-restriction-legs). -/
def LegData.Commutes {T Tb : Scheme.{u}} {uL uR : T ⟶ Tb}
    (e : uR = uL) (a : LegData Λ uL uR) : Prop :=
  a.inside.hom ≫ a.left ≫ (P Λ uL).map a.outside.hom =
    a.right ≫ (eqToIso (congrArg (P Λ) e)).hom.app a.outerRight

/-- The three original section units respect all projection reindexings of a triple.
This statement contains no tensor comparison and no binary open-product comparison.

Source: the coherence paragraph, three-factor identity-on-the-open calculation in
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/`
`sk-thm-sf-kunneth-relative.proof.md`, and proof step 3 of
`lem-sf-condensed-product-compactification-map`.
(blueprint: lem-sf-condensed-triple-restriction-legs).

Proof: expand each `leg` as pullback of its original open unit followed by the
inverse projection-square comparison. For the first and third factors apply
horizontal pasting of square comparisons, identifying the composed projection
with the indicated `outer₁`, `inner₁`, `outer₃`, `inner₃` transports. Naturality
of the native pullback compositor moves the original unit across that transport.
For the middle factor apply cube coherence with top `inner₂`, bottom `outer₂`,
and side faces `d₁₂.right`, `d₂₃.left`, `dL.left`, `dR.right`; naturality moves
the k-unit through the remaining middle comparison. Cancel the inner inverse
compositors and identify the two product-open pullbacks by `sameOpen`. The three
surviving equations are exactly `Commutes`. Empty opens and zero objects require
no cancellation of section maps; all cancellation is of canonical isomorphisms.
-/
theorem legs_coherent
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR) (K : D Λ X) (L : D Λ Y) (M : D Λ W) :
    (first Λ t K).Commutes Λ t.sameOpen ∧
      (second Λ t L).Commutes Λ t.sameOpen ∧
        (third Λ t M).Commutes Λ t.sameOpen := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NativeTripleRestriction
