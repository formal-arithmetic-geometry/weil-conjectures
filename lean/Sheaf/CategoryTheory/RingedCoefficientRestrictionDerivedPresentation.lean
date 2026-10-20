/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.CategoryTheory.RingedCoefficientCounitPresentations
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiDerivedPullback

/-!
# Existence of normalized derived coefficient presentations

Source: Stacks, Tags 07A6 and 0D6E.
(blueprint: lem-pur-ringed-coefficient-derived-presentation-exists).
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
/-- A normalized derived presentation can be chosen from the ordinary one.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6 and 0D6E;
sites-modules.tex, Tag 03D7. The coefficient normalization is an agent consequence.
(blueprint: lem-pur-ringed-coefficient-derived-presentation-exists).

Proof:
1. Restriction of scalars preserves the underlying abelian sheaf. Kernels are computed
sectionwise and cokernels by sheafifying sectionwise cokernels; hence both restrictions are
exact. Let x and y be their exact derived functors with the canonical termwise factorization
isomorphisms. Inverse image of constant-A modules is exact: its underlying set sheaf is the
geometric inverse image, so it preserves kernels and epimorphisms; additivity gives exactness.
This supplies CoefficientExactness and the invertible constant-coefficient comparison.
2. Take the universal left derived functor of o.pull, computed by flat-term K-flat resolutions,
and the universal right derived functor of o.pushR, computed by K-injectives. Apply the derived
adjunction theorem to o.adjR. Its representative Hom characterization gives exactly
r.homFormula, for every complex P and K-injective I. Do the same for o.adjA. The resolving-class
computation gives flatComparison, and exactness of IA.modules makes a.epsilon an isomorphism on
every complex.
3. Whisker the left-derived counit r.epsilon with exact coefficient restriction x. It remains
the absolute left-derived counit, since it is invertible on the flat-term K-flat resolving
class. Compose the termwise factorization of y and the counit a.epsilon with the degreewise
ordinary scalarUnit. The universal left-derived lift of this composite is tau. Evaluating its
factorization equation at P gives tauFormula. This constructs a natural transformation on the
whole derived category; the universal property, rather than a choice of a representative map for
each object, ensures independence of resolutions.
4. Compare the two factorizations of the composite ringed-topos direct image through constant
coefficients. Exact coefficient restriction identifies its own right derived functor with the
termwise localization. The normalized right-derived composition isomorphisms therefore give
kappa: r.right followed by y is isomorphic to x followed by a.right. If I is K-injective and
j:restriction(aX)(I) to T is a K-injective resolution, the composition formula says its
component is the class of ordinaryKappa followed by pushA(j), followed by a.eta and the inverse
resolution identifications. These are precisely the factors of kappaFormula. Assemble all these
data into DerivedPresentation. No counit square or coefficient-change naturality is asserted
here. -/
theorem exists_derivedPresentation
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
    Nonempty (DerivedPresentation o) := by sorry

end CategoryTheory.RingedCoefficientCounit
