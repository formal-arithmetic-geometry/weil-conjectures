/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison

/-!
# Acyclicity of comparison pullbacks of injective constant-ring modules

Source: blueprint, `sec-proetale-coefficients/sk-lem-pe-injective-acyclicity`;
Stacks Project, Tags 099U and 099V (blueprint: sk-lem-pe-injective-acyclicity).

The coefficient ring is arbitrary and discrete. Its pro-etale realization is the
inverse image of the constant etale ring sheaf. The canonical module inverse image
is constructed on the existing small models and transported back to the original
sites. The theorem computes the higher direct image using any injective module
resolution, as in the node's convention.

## Main definitions and statement

* `comparisonRingedModuleInverseImage`: inverse image over the inverse-image ring.
* `comparisonRingedModuleDirectImage`: restriction along the inclusion with its ring unit.
* `isZero_homology_comparisonRingedModuleDirectImage_of_injective`: vanishing in every
  positive degree for every injective module resolution of the inverse image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The small model of the etale site, enlarging only its morphism universe.
Source: Stacks, Tags 00VC and 099V (blueprint: sk-lem-pe-injective-acyclicity). -/
abbrev comparisonEtaleModel (X : Scheme.{u}) := AsSmall.{u + 1} X.Etale

/-- Transport of the small etale topology along the canonical model equivalence.
Source: Stacks, Tags 00VC and 099V (blueprint: sk-lem-pe-injective-acyclicity). -/
noncomputable abbrev comparisonEtaleModelTopology (X : Scheme.{u}) :=
  (AsSmall.down : comparisonEtaleModel X ⥤ X.Etale).inducedTopology X.smallEtaleTopology

/-- The constant etale ring sheaf for an arbitrary discrete commutative ring.
Source: Stacks, Tag 0H7J (blueprint: sk-lem-pe-injective-acyclicity). -/
noncomputable abbrev comparisonEtaleRing (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  (constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)

/-- Ring inverse image by the canonical left Kan extension and sheafification.
Source: Stacks, Tags 00WX and 00YV (blueprint: sk-lem-pe-injective-acyclicity). -/
noncomputable abbrev comparisonRingAdjunction (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (toProEt X)
    RingCat.{u + 1} X.smallEtaleTopology (ProEt.topology X)

/-- The coefficient ring on the pro-etale site is exactly the inverse-image ring.
Source: Stacks, Tags 00YV and 099V (blueprint: sk-lem-pe-injective-acyclicity). -/
noncomputable abbrev comparisonProEtaleRing (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :=
  (Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
    RingCat.{u + 1} X.smallEtaleTopology (ProEt.topology X)).obj (comparisonEtaleRing X Λ)

/-- Inclusion of the small etale model into the small pro-etale model.
Source: Stacks, Tag 099R (blueprint: sk-lem-pe-injective-acyclicity). -/
noncomputable abbrev comparisonModelInclusion (X : Scheme.{u}) :
    comparisonEtaleModel X ⥤ proEtaleSiteModel X :=
  AsSmall.down ⋙ toProEt X ⋙ AsSmall.up

/-- The transported inclusion is continuous.
Source: Stacks, Tags 00VC and 099R (blueprint: sk-lem-pe-injective-acyclicity). -/
instance comparisonModelInclusion_isContinuous (X : Scheme.{u}) :
    (comparisonModelInclusion X).IsContinuous
      (comparisonEtaleModelTopology X) (proEtaleModelTopology X) :=
  haveI := Functor.isContinuous_comp (toProEt X) AsSmall.up
    X.smallEtaleTopology (ProEt.topology X) (proEtaleModelTopology X)
  Functor.isContinuous_comp AsSmall.down (toProEt X ⋙ AsSmall.up)
    (comparisonEtaleModelTopology X) X.smallEtaleTopology (proEtaleModelTopology X)

/-- The canonical ring unit on the small models. This is the actual ring-adjunction
unit, with its section maps unchanged by transport.
Source: Stacks, Tags 00YV and 03D2 (blueprint: sk-lem-pe-injective-acyclicity). -/
noncomputable def comparisonModelRingUnit (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    ((AsSmall.down : comparisonEtaleModel X ⥤ X.Etale).sheafPushforwardContinuous
      RingCat.{u + 1} (comparisonEtaleModelTopology X) X.smallEtaleTopology).obj
        (comparisonEtaleRing X Λ) ⟶
    ((comparisonModelInclusion X).sheafPushforwardContinuous RingCat.{u + 1}
      (comparisonEtaleModelTopology X) (proEtaleModelTopology X)).obj
        (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
            (comparisonProEtaleRing X Λ)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (((comparisonRingAdjunction X).unit.app (comparisonEtaleRing X Λ)).hom)⟩

/-- The module inverse image over the pulled-back coefficient ring. Module Kan
extension and sheafification on the small models construct its data; transport
back retains every object and section of the original pro-etale site.
Source: Stacks, Tags 00YV and 03D2 (blueprint: sk-lem-pe-injective-acyclicity). -/
noncomputable def comparisonRingedModuleInverseImage (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    ringedSiteModules.{u + 1} (comparisonEtaleRing X Λ) ⥤
      ringedSiteModules.{u + 1} (comparisonProEtaleRing X Λ) :=
  SheafOfModules.pushforward.{u + 1} (F := AsSmall.down)
      (J := comparisonEtaleModelTopology X) (K := X.smallEtaleTopology)
      (R := comparisonEtaleRing X Λ) (𝟙 _) ⋙
    SheafOfModules.pullback (comparisonModelRingUnit X Λ) ⋙
      proEtaleModuleFromModel (comparisonProEtaleRing X Λ)

/-- The corresponding module direct image, by restriction and the ring-adjunction
unit. No finite-coefficient realization or arbitrary scalar map occurs.
Source: Stacks, Tags 03D1 and 099V (blueprint: sk-lem-pe-injective-acyclicity). -/
noncomputable def comparisonRingedModuleDirectImage (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    ringedSiteModules.{u + 1} (comparisonProEtaleRing X Λ) ⥤
      ringedSiteModules.{u + 1} (comparisonEtaleRing X Λ) :=
  SheafOfModules.pushforward.{u + 1}
    ((comparisonRingAdjunction X).unit.app (comparisonEtaleRing X Λ))

/-- Direct image preserves addition sectionwise.
Source: Stacks, Tag 03D1 (blueprint: sk-lem-pe-injective-acyclicity). -/
instance comparisonRingedModuleDirectImage_additive (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    (comparisonRingedModuleDirectImage X Λ).Additive where

/-- The positive higher direct images of the comparison pullback of an injective
module vanish, computed with any injective module resolution.
Source: blueprint, `sk-lem-pe-injective-acyclicity`; Stacks, Tags 099U and 099V
(blueprint: sk-lem-pe-injective-acyclicity).

Proof:
1. Put the sites and coefficient modules in the common larger universe. The module
categories are Grothendieck by `lem-weil-pbc-ring-sheaves-grothendieck`, and have
enough injectives by `lem-sp-grothendieck-enough-injectives`.
2. Apply part (1) of `det-pe-injective-acyclicity-reduction`: higher direct images
are sheafifications of cohomology on affine etale objects W. Part (2) identifies
the restricted inverse image with the inverse image of the restricted injective I.
3. The restricted module I has zero positive derived evaluation by
`lem-weil-pbc-derived-functor-injective-vanishing`. The module/abelian evaluation
comparison `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` gives
the same vanishing for its underlying abelian sheaf, without requiring that
underlying abelian sheaf to be injective.
4. Apply `lem-cbc-abelian-etale-proetale-cohomology-comparison` on W, then the
module/abelian evaluation comparison on W_proet. The underlying abelian inverse
image is the underlying sheaf of the module inverse image, by its construction.
Thus all positive module cohomology groups on affine etale W vanish.
5. Part (1) of `det-pe-injective-acyclicity-reduction` gives zero higher direct
image. By `InjectiveResolution.isoRightDerivedObj`, applying module direct image
to any injective module resolution J computes exactly these higher direct images.
-/
theorem isZero_homology_comparisonRingedModuleDirectImage_of_injective
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (I : ringedSiteModules.{u + 1} (comparisonEtaleRing X Λ)) [Injective I]
    (J : InjectiveResolution ((comparisonRingedModuleInverseImage X Λ).obj I))
    (q : ℕ) (hq : 0 < q) :
    IsZero (((comparisonRingedModuleDirectImage X Λ).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex |>.homology q) := by
  sorry

end AlgebraicGeometry.Scheme
