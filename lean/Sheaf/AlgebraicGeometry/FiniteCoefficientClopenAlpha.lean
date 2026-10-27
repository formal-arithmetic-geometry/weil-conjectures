/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars
public import Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization

/-! # The coefficient comparison for the clopen alpha

Source: Stacks Project, Tags 03DA, 099R, 09AF and 07A7; the first two steps of
lem-cbc-single-level-finite-proper-open-transport.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B Λ : Type (u + 1)) [CommRing B] [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)

/-- The ordinary inverse pullback comparison, with its specified inverse.
Source: Stacks Tags 03DA and 099R
(blueprint: lem-cbc-finite-coefficient-clopen-alpha). -/
def hPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    H B Y Λ φ ⋙ modulePullback B f ≅
      Etale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ H B X Λ φ :=
  @asIso _ _ _ _ (hPullbackInv B f Λ φ) (hPullbackInv_isIso B f Λ φ)

/-- Exact descent of the inverse pullback comparison. Source: Stacks Tags 03DA and 07A7
(blueprint: lem-cbc-finite-coefficient-clopen-alpha). -/
def hPullbackPlus {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (H B Y Λ φ).mapDerivedCategoryPlus ⋙ (modulePullback B f).mapDerivedCategoryPlus ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (H B X Λ φ).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (hPullbackIso B Λ φ f) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- Exact descent of the forward extension-by-zero comparison. Source: Stacks Tag 09AF
(blueprint: lem-cbc-finite-coefficient-clopen-alpha). -/
def hOpenPlus {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        (H B X Λ φ).mapDerivedCategoryPlus ≅
      (H B U Λ φ).mapDerivedCategoryPlus ⋙ (moduleJ B j).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (@asIso _ _ _ _ (hOpen B j Λ φ) (hOpen_isIso B j Λ φ)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- Coefficient realization preserves the clopen alpha before taking proper mates.
Source: Stacks Project, proetale.tex Tags 099R and 09AF, sites-modules.tex Tag 03DA,
and sites-cohomology.tex Tag 07A7; steps 1--2
of lem-cbc-single-level-finite-proper-open-transport
(blueprint: lem-cbc-finite-coefficient-clopen-alpha).

Proof: factor H as site inverse image followed by C. For the site factor use the
site alpha equation of finiteClopenAlphaSiteTransport on M[0] and take H⁰.
The exact single-complex comparison isomorphisms recover the ordinary equation.
For C first take identity scalars
on the finite ring: the realization is an equivalence, and cDirect is the unique
section-preserving direct-image comparison. Its inverse mate is the pullback
comparison and the next inverse mate is the open comparison. Their unit equations
identify the cartesian beta, by uniqueness of its open transpose. On the clopen lift
and its complementary open the realization preserves restrictions, identity maps
and zero maps. Descent for this disjoint open cover therefore identifies the
projector, including an empty image or an empty complement. The unit equations also
identify the open and pullback compositors, so composing gives the alpha equation.
For general B and φ, factor C through the identity-scalar realization and restriction
along the constant-section map induced by φ. The scalar alpha equation gives the
same compatibility after this restriction. These identifications agree with the
specified cDirect by its section normalization, hence with hPullbackInv and hOpen
by injectivity of their mate correspondences. This proves the ordinary sheaf
equation before applying complexes or localization. No proper mate or derived
direct-image comparison is used in this step. Zero rings and zero coefficient complexes cause
no change to the argument; scalar restriction requires no flatness. -/
theorem finiteCoefficientClopenAlpha
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (H B W Λ φ).map ((Etale.ClopenMateNormalization.alpha Λ k r p i h).app M) ≫
      (hOpen B k Λ φ).app ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj M) ≫
      (moduleJ B k).map ((hPullbackIso B Λ φ r).inv.app M) =
    (hPullbackIso B Λ φ p).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).obj M) ≫
      (modulePullback B p).map ((hOpen B i Λ φ).app M) ≫
      (singleAlpha B k r p i h).app ((H B S Λ φ).obj M) := by sorry

end AlgebraicGeometry.ProEtale.StrictTower
