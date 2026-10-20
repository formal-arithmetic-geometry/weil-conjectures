/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.CategoryTheory.RingedCoefficientChangePresentations
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-!
# Naturality of normalized coefficient changes

Source: Stacks, Tags 03D7, 07A6 and 0D6E.
(blueprint: lem-pur-ringed-coefficient-change-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingedCoefficientCounit

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [UnivLE.{max u v, r}] [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
  [JX.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{r})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{r})]
  [HasSheafify JX AddCommGrpCat.{r}] [JX.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify JY AddCommGrpCat.{r}] [JY.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify JX CommRingCat.{r}] [HasWeakSheafify JY CommRingCat.{r}]
  (A : CommRingCat.{r}) (RX RI : Sheaf JX CommRingCat.{r})
  (RY : Sheaf JY CommRingCat.{r})
  (inverse : Sheaf JY (Type r) ⥤ Sheaf JX (Type r))
  (direct : Sheaf JX (Type r) ⥤ Sheaf JY (Type r)) (geom : inverse ⊣ direct)
  [leftExact : PreservesFiniteLimits inverse]
  (IA : SheafOfModules.AlgebraicInverseImage inverse
    (constantRing JY A) (constantRing JX A))
  (IR : SheafOfModules.AlgebraicInverseImage inverse RY RI) (c : RI ⟶ RX)

include leftExact in
/-- Compatible coefficient maps admit normalized derived comparisons. Assuming the individual
counit compatibilities, every normalized comparison satisfies the two coefficient
naturality squares.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6 and 0D6E;
sites-modules.tex, Tag 03D7. The coefficient normalization is an agent consequence.
(blueprint: lem-pur-ringed-coefficient-change-normalization).

Proof:
1. Restricting successively along bX and aX has the same underlying module as restricting along
aX prime; the equality aX followed by bX = aX prime identifies the actions. The identity on
underlying sheaves gives the ordinary restriction-composition isomorphism, and similarly on Y.
Exactness of restriction gives the termwise localized functors vX and vY. Localize those
ordinary isomorphisms and compose with xFactors and yFactors to obtain rhoX and rhoY with
exactly the equations in CoefficientRestrictionChangeNormalized. The remaining five
normalization clauses are the given compatibility hypotheses.
2. Commutation of the structural ring maps makes the two ordinary pushR functors after
restriction have the same scalar action, as seen by transposing against the specified geometric
adjunction. Thus the identity underlying direct-image map lifts to ordinaryBeta; it is
invertible by the same construction in reverse. Apply normalized right-derived composition to
its two factorizations to construct beta. Its equation on I and a K-injective resolution j of
the restricted I is exactly CoefficientDirectChangeNormalized.
3. Both constant-coefficient left derived functors derive the same IA.modules. Their canonical
universal comparison gives alpha, with alpha followed by the primed counit equal to the unprimed
counit. The two ordinary pushA functors are right adjoints to IA.modules, with the same
geometric Hom formula. Right-adjoint uniqueness gives ordinaryGamma with the prescribed
underlying identity. Its right-derived comparison gives gamma; evaluating on K-injectives gives
the constant normalization. Take sigma to be the adjoint mate of beta after the primed derived
unit. Naturality of adjunction supplies a natural transformation, and its defining formula is
CoefficientChangeNormalized. Together these construct CoefficientChange.
4. For any normalized CoefficientChange, compare the two composites in the kappa naturality
square on a K-injective I. Resolve its restricted module complex once more by a K-injective T.
The normalization equations for beta, rhoX, rhoY, gamma and kappa identify both composites with
the same localized ordinary direct-image map to the final resolution. This ordinary equality
holds because all three underlying comparisons are identities and the coefficient actions
commute by the hypotheses. Common K-injective refinements and naturality of the comparison maps
remove the chosen resolutions. Every derived object has a K-injective representative, so this
proves the kappa square for all objects.
5. Use the assumed CounitCompatibility equations for p and p prime: tau is the adjoint mate of
kappa, and tau prime is the mate of kappa prime. The normalized constant comparisons alpha and
gamma preserve the canonical derived adjunction by the representative Hom formula. The preceding
kappa square, after taking adjoint mates, becomes the displayed tau square: sigma is the mate of
beta by its normalization, while rhoX and rhoY are the restriction-composition identifications.
The triangle identities cancel the inserted units and counits. Taking mates is a bijection on
natural transformations, so this is equality of the specified derived maps and requires no
faithfulness of restriction. This establishes both clauses of IsNatural for every normalized
comparison. -/
theorem coefficientChange_exists
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI)
    [IA.modules.Additive]
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))]
    (p : DerivedPresentation o) (hp : CounitCompatibility p)
    (RX' RI' : Sheaf JX CommRingCat.{r}) (RY' : Sheaf JY CommRingCat.{r})
    (IR' : SheafOfModules.AlgebraicInverseImage inverse RY' RI') (c' : RI' ⟶ RX')
    (aX' : constantRing JX A ⟶ RX') (aY' : constantRing JY A ⟶ RY')
    (aI' : constantRing JX A ⟶ RI')
    (o' : OrdinaryPresentation direct geom IA IR' c' aX' aY' aI')
    [HasDerivedCategory.{w} (modules RX')] [HasDerivedCategory.{w} (modules RY')]
    (p' : DerivedPresentation o') (hp' : CounitCompatibility p')
    (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI')
    (haX : aX ≫ bX = aX') (haY : aY ≫ bY = aY') (haI' : aI ≫ bI = aI')
    (hc' : c ≫ bX = bI ≫ c')
    (hIR : IR.ringUnderlying.hom ≫ (sheafCompose JX (forget CommRingCat.{r})).map bI =
      inverse.map ((sheafCompose JY (forget CommRingCat.{r})).map bY) ≫ IR'.ringUnderlying.hom) :
    Nonempty (CoefficientChange p p' bX bY bI) ∧
      ∀ m : CoefficientChange p p' bX bY bI, m.IsNatural := by sorry

end CategoryTheory.RingedCoefficientCounit
