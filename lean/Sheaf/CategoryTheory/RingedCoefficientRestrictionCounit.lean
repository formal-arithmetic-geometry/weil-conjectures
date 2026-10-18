/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.CategoryTheory.RingedCoefficientChangePresentations
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedTopoiDerivedPullback

/-!
# Derived ringed-topos counit under coefficient restriction

Source: Stacks, Tags 03D7, 07A6 and 0D6E
(blueprint: lem-pur-ringed-coefficient-restriction-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
/-- Canonical coefficient comparisons exist and respect the derived counit and every
compatible coefficient homomorphism. Exactness of coefficient restriction is supplied
by the resulting presentation. No flatness of aX or aY is assumed.
Source: Stacks 03D7, 07A6, 0FND and 0D6E
(blueprint: lem-pur-ringed-coefficient-restriction-counit).

Proof:
1. Restriction preserves the underlying abelian sheaf, hence kernels and sheafified
cokernels, so it is exact (lem-pur-sheaf-ring-derived-coefficient-adjunction).
Inverse image with constant coefficients is exact. Choose flat-term K-flat resolutions
(lem-pc-kflat-resolution). The sheafified map x ↦ 1 tensor x is A-linear by haI and hc,
commutes with differentials and is natural in chain maps. The canonical left-derived
comparison on these resolutions therefore descends to tau; its representative equation
is tauFormula. No flatness of the coefficient maps is used.
2. The ordinary coefficient/direct-image square is fixed by the underlying geometric
adjunction (lem-weil-pbc-ringed-topoi-module-adjunction, Tag 03D7). Apply the normalized
K-injective composition comparison (lem-weil-pbc-ringed-topoi-derived-pushforward-
composition, Tag 0D6E) to its two factorizations. For K-injective I and a K-injective
resolution j:U_X I→J it is the class of f_*j. This gives kappaFormula.
3. Represent K by a K-injective I and resolve f_*I by a flat-term K-flat P→f_*I.
The representative Hom formula for the canonical derived adjunction
(lem-pc-pre-derived-adjoint-functors-general and def-weil-pbc-projection-formula-arrows)
represents epsilon_R by s tensor x ↦ s e(f⁻¹q(x)), where e is the geometric counit.
Precomposing with tau gives e f⁻¹q, hence the class of e after the resolution identifications.
4. Choose j:U_X I→J K-injective. The ordinary adjunct of j e is f_*j by the triangle
identity. The same representative Hom formula says that the derived adjunct of the
class of e is the class of f_*j, which is kappa by Step 2. Apply the adjunct-counit identity
(lem-weil-pbc-adjunct-counit-identity) to obtain CounitCompatibility for every K.
5. All comparisons are natural in K because they are natural transformations. For
compatible coefficient maps bX,bY,bI, restriction is again exact, the ordinary scalar
unit is the same map x ↦ 1 tensor x, and the underlying direct-image comparisons are
identities. Descend these equations through the canonical resolution identifications.
The normalized composition maps give beta, rhoX, rhoY, alpha and gamma in CoefficientChange;
the pullback comparison sigma is their adjoint mate. The two resulting diagrams are
exactly CoefficientChange.IsNatural. This also constructs CoefficientChange for every
compatible triple, including identities and non-flat quotient maps. -/
theorem ringedCoefficientRestrictionCounit
    (aX : constantRing JX A ⟶ RX) (aY : constantRing JY A ⟶ RY)
    (aI : constantRing JX A ⟶ RI)
    (haI : (sheafCompose JX (forget CommRingCat.{r})).map aI =
      IA.ringUnderlying.inv ≫ inverse.map
        ((sheafCompose JY (forget CommRingCat.{r})).map aY) ≫ IR.ringUnderlying.hom)
    (hc : aI ≫ c = aX)
    (o : OrdinaryPresentation direct geom IA IR c aX aY aI)
    [IA.modules.Additive]
    [HasDerivedCategory.{w} (modules RX)] [HasDerivedCategory.{w} (modules RY)]
    [HasDerivedCategory.{w} (modules (constantRing JX A))]
    [HasDerivedCategory.{w} (modules (constantRing JY A))] :
    Nonempty (DerivedPresentation o) ∧
    ∀ p : DerivedPresentation o, CounitCompatibility p ∧
      ∀ (RX' RI' : Sheaf JX CommRingCat.{r}) (RY' : Sheaf JY CommRingCat.{r})
        (IR' : SheafOfModules.AlgebraicInverseImage inverse RY' RI') (c' : RI' ⟶ RX')
        (aX' : constantRing JX A ⟶ RX') (aY' : constantRing JY A ⟶ RY')
        (aI' : constantRing JX A ⟶ RI')
        (o' : OrdinaryPresentation direct geom IA IR' c' aX' aY' aI')
        [HasDerivedCategory.{w} (modules RX')] [HasDerivedCategory.{w} (modules RY')]
        (p' : DerivedPresentation o') (bX : RX ⟶ RX') (bY : RY ⟶ RY') (bI : RI ⟶ RI'),
        aX ≫ bX = aX' → aY ≫ bY = aY' → aI ≫ bI = aI' →
        c ≫ bX = bI ≫ c' →
        IR.ringUnderlying.hom ≫ (sheafCompose JX (forget CommRingCat.{r})).map bI =
          inverse.map ((sheafCompose JY (forget CommRingCat.{r})).map bY) ≫
            IR'.ringUnderlying.hom →
        Nonempty (CoefficientChange p p' bX bY bI) ∧
          ∀ m : CoefficientChange p p' bX bY bI, m.IsNatural := by
  sorry

end CategoryTheory.RingedCoefficientCounit
