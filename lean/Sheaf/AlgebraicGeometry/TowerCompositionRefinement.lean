/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NE
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
public import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
public import Sheaf.AlgebraicGeometry.ProperOpenComparison
public import Sheaf.AlgebraicGeometry.OpenSectionClopen
public import Sheaf.Paper.EtaleDerivedDirectImageCoherence
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence

/-! # Composition in compatible towers commutes with proper refinements

Source: Stacks Project, More on Étale Cohomology, Tags 0F7C and 0F7D, assembled for
refining compatible compactification towers
(blueprint: lem-cbc-tower-composition-refinement).

The equality is written componentwise for every object of the ordinary small-étale `D⁺`.
This is equivalent to equality of the indicated natural transformations by extensionality.
`Compactification.Triangle` represents the intermediate fibre product up to its unique
projection-preserving isomorphism. Its `q` is the open arrow denoted `b` in the node.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/- The ordinary derived comparison selected by the normalized coherence theorem.
It is introduced here to keep the construction entirely in the small-etale derived
categories; no strict pro-etale tower is involved. -/
noncomputable def cbcSecondWitness {A : Sort v} {C : Sort w} {P : A → C → Prop}
    (h : ∃ a c, P a c) : C :=
  h.choose_spec.choose

noncomputable def cbcOrdinaryGamma
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r) ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p :=
  cbcSecondWitness (properOpenInterchangeCoherence Λ) k i r p h

/-- The component of refinement transport `Rp₂,* α_w`, followed by the canonical
ordinary étale derived direct-image compositor. The two equations orient the refinement
from compactification 1 to compactification 2, and the comparison in the reverse direction.
Source: Stacks Project, Tags 0F7B and 0F7C
(blueprint: lem-cbc-tower-composition-refinement). -/
noncomputable def cbcTowerRefinementComponent
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C₁ C₂ : Compactification f)
    (w : C₁.Z ⟶ C₂.Z) [IsProper w]
    (hi : C₁.i ≫ w = C₂.i) (hg : C₁.g = w ≫ C₂.g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) C₂.g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) C₂.i).mapDerivedCategoryPlus.obj K) ⟶
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) C₁.g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) C₁.i).mapDerivedCategoryPlus.obj K) :=
  (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) C₂.g).map
      (properOpenComparison Λ w C₁.i C₂.i hi K) ≫
    (Functor.rightDerivedFunctorPlusCompIso'
      (lowerStar (ModuleCat.{u + 1} Λ) w) (lowerStar (ModuleCat.{u + 1} Λ) C₂.g)
      (lowerStarComp (ModuleCat.{u + 1} Λ) w C₂.g C₁.g hg)).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) C₁.i).mapDerivedCategoryPlus.obj K)

/-- The canonical exact open compositor with a named composite arrow. Equality elimination
transports the already defined compositor, including its open-immersion instance.
Source: Stacks Project, Tag 0F7D
(blueprint: lem-cbc-tower-composition-refinement). -/
noncomputable def cbcTowerOpenCompositionComponent
    (Λ : Type (u + 1)) [CommRing Λ]
    {X U A : Scheme.{u}} (c : X ⟶ U) (b : U ⟶ A) (a : X ⟶ A)
    [IsOpenImmersion c] [IsOpenImmersion b] [IsOpenImmersion a]
    (ha : c ≫ b = a)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c).mapDerivedCategoryPlus.obj K) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.obj K := by
  subst a
  exact (extensionZeroCompDerivedPlusIso Λ c b).hom.app K

/-- The specified tower composition component `μ`: apply `Rq_* γ c_!`, compose the
exact open extensions, and compose ordinary étale derived direct images.
The ordinary normalized comparison selected by `properOpenInterchangeCoherence` is used
directly; no strict or pro-etale tower is involved.
Source: Stacks Project, Tags 0F7C and 0F7D
(blueprint: lem-cbc-tower-composition-refinement). -/
noncomputable def cbcTowerCompositionComponent
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T.cg.g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.cg.i).mapDerivedCategoryPlus.obj
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T.cf.g).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.cf.i).mapDerivedCategoryPlus.obj
              K))) ⟶
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T.cfg.g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.cfg.i).mapDerivedCategoryPlus.obj K) :=
  (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T.cg.g).map
      ((cbcOrdinaryGamma Λ T.q T.cf.g T.p T.cg.i
        T.isPullback.w.symm).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.cf.i).mapDerivedCategoryPlus.obj
            K)) ≫
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T.cg.g).map
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T.p).map
        (cbcTowerOpenCompositionComponent Λ T.cf.i T.q T.cfg.i T.i_q K)) ≫
    (Functor.rightDerivedFunctorPlusCompIso'
      (lowerStar (ModuleCat.{u + 1} Λ) T.p) (lowerStar (ModuleCat.{u + 1} Λ) T.cg.g)
      (lowerStarComp (ModuleCat.{u + 1} Λ) T.p T.cg.g T.cfg.g T.p_g.symm)).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.cfg.i).mapDerivedCategoryPlus.obj K)

/-- The `hf` refinement component. The equation on the composite proper maps is obtained
from `p₂ v = u p₁` and `q₂ u = q₁` and the two tower equations, without any cartesian
refinement condition. Source: Stacks Project, Tags 0F7C and 0F7D
(blueprint: lem-cbc-tower-composition-refinement). -/
noncomputable def cbcTowerCompositeRefinementComponent
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T₁ T₂ : Compactification.Triangle f h)
    (uY : T₁.cg.Z ⟶ T₂.cg.Z) (v : T₁.cfg.Z ⟶ T₂.cfg.Z) [IsProper v]
    (ha : T₁.cfg.i ≫ v = T₂.cfg.i)
    (hp : v ≫ T₂.p = T₁.p ≫ uY) (hq : uY ≫ T₂.cg.g = T₁.cg.g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T₂.cfg.g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T₂.cfg.i).mapDerivedCategoryPlus.obj K) ⟶
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T₁.cfg.g).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T₁.cfg.i).mapDerivedCategoryPlus.obj K) :=
  cbcTowerRefinementComponent Λ T₁.cfg T₂.cfg v ha
    (by rw [← T₂.p_g, ← Category.assoc, hp, Category.assoc, hq, T₁.p_g]) K

/-- Tower composition intertwines all three proper refinement comparisons.
Source: Stacks Project, Tags 0F7C and 0F7D, the explicit compatible-tower consequence
(blueprint: lem-cbc-tower-composition-refinement).

Proof plan, with the specified direct-image and open-extension compositors inserted:
1. Write `Pν = Rpν,*`, `Sν = RpY,ν,*`, `Qν = Rqν,*` and `U = Ru_*`, `V = Rv_*`,
   `W = Rw_*`. The compatible-tower node gives openness of b,c and properness of pY.
   Use lem-cbc-etale-derived-direct-image-coherence for identity and triple coherence,
   and lem-cbc-extension-zero-composition, degreewise by
   lem-weil-pbc-extension-by-zero-exact, for b!c! = a!.
2. For the commutative, possibly noncartesian square (b₁,b₂,w,v), let δ be its normalized
   interchange. Horizontal composition and refinement normalization in
   lem-cbc-proper-open-interchange-coherence give αv = (δ c₁!)(b₂! αw).
3. Paste this square above tower 2. The same outer rectangle is tower 1 above the
   refinement square (i₁,i₂,id,u). The vertical law of the same node gives
   (P₂δ)(γ₂W) = (Uγ₁)(αu S₁). All verticals are proper; no base-change claim is used.
4. Naturality of γ₂ at αw gives
   (P₂b₂!αw)(γ₂c₂!) = (γ₂Wc₁!)(i₂!S₂αw).
5. Expand C_hf μ₂, substitute step 2, then step 4, then step 3 whiskered by c₁!.
   Functoriality of Q₂,P₂ yields μ₁(C_h F₁)(H₂ C_f). The triple direct-image coherence
   identifies Q₂P₂V with Q₁P₁ through either parenthesization; the open compositor
   identifies bν!cν! with aν!. Thus the component equality is the required natural
   transformation equality. No restriction on the bases or cartesian refinement is used.
-/
theorem cbcTowerComposition_refinement
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T₁ T₂ : Compactification.Triangle f h)
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i] [QuasiCompact T₁.cfg.i]
    [QuasiCompact T₁.q]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i] [QuasiCompact T₂.cfg.i]
    [QuasiCompact T₂.q]
    (uY : T₁.cg.Z ⟶ T₂.cg.Z) (v : T₁.cfg.Z ⟶ T₂.cfg.Z)
    (w : T₁.cf.Z ⟶ T₂.cf.Z) [IsProper uY] [IsProper v] [IsProper w]
    (hi : T₁.cg.i ≫ uY = T₂.cg.i) (ha : T₁.cfg.i ≫ v = T₂.cfg.i)
    (hc : T₁.cf.i ≫ w = T₂.cf.i) (hb : T₁.q ≫ v = w ≫ T₂.q)
    (hp : v ≫ T₂.p = T₁.p ≫ uY) (hs : w ≫ T₂.cf.g = T₁.cf.g)
    (hq : uY ≫ T₂.cg.g = T₁.cg.g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    cbcTowerCompositionComponent Λ T₂ K ≫
        cbcTowerCompositeRefinementComponent Λ T₁ T₂ uY v ha hp hq K =
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T₂.cg.g).map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T₂.cg.i).mapDerivedCategoryPlus.map
          (cbcTowerRefinementComponent Λ T₁.cf T₂.cf w hc hs.symm K)) ≫
        cbcTowerRefinementComponent Λ T₁.cg T₂.cg uY hi hq.symm
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) T₁.cf.g).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T₁.cf.i).mapDerivedCategoryPlus.obj
              K)) ≫
        cbcTowerCompositionComponent Λ T₁ K := by
  sorry

end AlgebraicGeometry.Etale
