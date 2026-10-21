/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.SixFunctors.ComparisonOpenTensorCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
import Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.Paper.RingedExchangeTensorCoherence
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Finite site comparison of counits, projections and transposes

Source: blueprint main-20261015, lem-pur-co-smooth-etale-locality, Steps 1 and 3;
Stacks Project, Tags 0B65, 07A4, 0GL1 and 0F7F
(blueprint: lem-pur-finite-site-counit-projection-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Bounded constructible etale complexes are bounded below.
Source: blueprint finite derived-category convention
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: choose the lower endpoint of the finite cohomological interval in hM.
The defining vanishing outside that interval implies vanishing below its lower endpoint. -/
theorem finiteSiteProjectionInput_plus_source
    (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (_hM : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X M) :
    _root_.DerivedCategory.TStructure.t.plus M := by
  sorry

/-- The tensor input in the projection square is bounded below on its stated domain.
Source: blueprint lem-pur-co-smooth-etale-locality, Steps 1 and 3
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: pullback preserves the finite Tor interval of K. Tensoring a bounded complex
M with this pullback has cohomology only in the sum of their two finite intervals.
Thus it is bounded, in particular bounded below. No flatness of A is assumed. -/
theorem finiteSiteProjectionInput_plus
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X M)
    (_hK : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y K) :
    _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj
        (L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K)) := by
  sorry

/-- Comparison preserves the actual proper-mate/open compactification projection.
Source: blueprint lem-pur-co-smooth-etale-locality, Steps 1 and 3;
Stacks Tags 07A4, 0E48 and 0GL1
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: apply ringed tensor/exchange coherence to the proper factor r and the
comparison morphisms. The proper comparison is its direct-image counit mate,
so this identifies the specified proper projections, without an automorphism ambiguity.
Apply comparison_open_tensor_coherence to j and r^*K. Expand both compactification
projections as proper projection, open tensor map, and pullback composition.
Naturality moves the proper comparison past the open map. The open comparison
and monoidal pullback-composition coherence identify the remaining factors.
Their composite is B at M tensor f^*K followed by the specified tensor comparison.
These are precisely proof steps 2 and 3 of the node. -/
theorem finiteSiteCounitProjectionTransport
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f)
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (hM : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X M)
    (hK : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y K) :
    D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map
        (((Etale.projectionMapOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).app M).app K) ≫
      (compactSupportSiteComparison P.Coefficient c).inv.app
        ⟨_, finiteSiteProjectionInput_plus P f M K hM hK⟩ ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c).map
          (comparisonOpenTensorIso P.Coefficient f M K).hom =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient)
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c).obj M)).hom.app K ≫
      ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
        ((compactSupportSiteComparison P.Coefficient c).inv.app
          ⟨M, finiteSiteProjectionInput_plus_source P X M hM⟩)).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M)).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) := by
  sorry

/-- Counit preservation and transport of every compatible adjunction transpose.
The dimension certificate is a conclusion, not an extra geometric hypothesis.
Source: blueprint lem-pur-co-smooth-etale-locality, Steps 1 and 3; Stacks Tag 0B65
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: finite type over k gives a finite nonnegative bound on dim c.Z, choosing zero
for the empty compactification. Apply boundedSiteAdjunctionTranspose with this bound,
the same compactification and its specified B. Its rho is comparison of H applied
to the site-comparison unit. That unit is invertible on D+. The inverse Hom chain
identifies the relative counit. Naturality of B and the etale counit, followed by
the comparison triangle identity, gives the counit equation. Applying the same
Hom-chain bijection to compatible maps gives the transpose equation. This is step 1
of the node; it uses no exceptional adjunction on arbitrary pro-etale objects. -/
theorem finiteSiteCounitAndTranspose
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f) :
    ∃ (d : ℕ) (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)),
    ∀ (H : Etale.DerivedCategoryModule P.Coefficient Y ⥤
      Etale.DerivedCategoryModule P.Coefficient X)
      (adj : Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
      (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
      (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
      (hHK : _root_.DerivedCategory.TStructure.t.plus (H.obj K.obj)),
      IsIso (boundedSiteRho P.Coefficient H K.obj) ∧
      ((compactSupportSiteComparison P.Coefficient c).inv.app ⟨H.obj K.obj, hHK⟩ ≫
          (rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} P.Coefficient) c).map
            (boundedSiteRho P.Coefficient H K.obj) ≫
          boundedSiteCounit P aX aY f hf c d hd H adj
            ((siteComparisonDerivedPullbackPlus Y P.Coefficient).obj K) =
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map
          (adj.counit.app K.obj)) ∧
      (∀ (ze : (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).obj J.obj ⟶ K.obj)
        (zp : (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).obj
          (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj J.obj) ⟶
          D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K.obj),
        (compactSupportSiteComparison P.Coefficient c).inv.app J ≫ zp =
          D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map ze →
        boundedSiteHomEquiv P aX aY f hf c d hd H adj J
            ((siteComparisonDerivedPullbackPlus Y P.Coefficient).obj K) zp =
          D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
            ((adj.homEquiv J.obj K.obj) ze) ≫ boundedSiteRho P.Coefficient H K.obj) := by
  sorry

/-- Both specified projections are invertible on the finite-Tor domain used below.
Source: blueprint lem-pur-co-smooth-etale-locality, Step 3; node proof step 4
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: the finite compact projection formula makes the etale component invertible.
The projection comparison square identifies its comparison image with the actual
pro-etale projection, with all other factors isomorphisms. Hence that component is
invertible too. Only the stated bounded constructible/finite-Tor inputs are used. -/
theorem finiteSiteProjections_isIso
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f)
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X M)
    (_hK : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y K) :
    IsIso (((Etale.projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app M).app K) ∧
    IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M)).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)) := by
  sorry

/-- The uniquely counit-normalized tensor maps and their specified transposes.
No arbitrary replacement map is chosen: the two forward-projection equations
uniquely specify the inverse-projection/counit composites. At E equal to the
coefficient unit and e equal to its canonical left unitor, followed by tensor
symmetry on the source, this is precisely theta with the specified normalization.
Source: blueprint lem-pur-co-smooth-etale-locality, Step 3; node proof step 4
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: both projections are invertible on this finite-Tor domain. Compose their
inverses with the counit tensored with K and the displayed comparison and unitor
maps to obtain the pair. Cancellation by each projection gives uniqueness.
The projection square and the counit equation show that the pro-etale member
precomposed with B equals comparison of the etale member. The bounded-site
adjunction transpose formula then gives the final equation. Monoidal comparison
preserves symmetry, the coefficient unit and its unitors, so the unit specialization
is exactly the theta map of def-pur-co-smoothness, with rho on its target. -/
theorem finiteSiteTensorTranspose
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : Etale.DerivedCategoryModule P.Coefficient Y ⥤
      Etale.DerivedCategoryModule P.Coefficient X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (E K : Etale.DerivedCategoryModule P.Coefficient Y)
    (hHE : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X (H.obj E))
    (hK : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y K)
    (Q : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (e : ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj E).obj K ≅ Q.obj) :
    ∃! z :
      (((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj (H.obj E)).obj
          (L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K)) ⟶ Q.obj) ×
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
          (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj (H.obj E)).obj
            (L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K))) ⟶
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj Q.obj)),
      ((((Etale.projectionMapOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c).app (H.obj E)).app K) ≫ z.1 =
        ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
          (adj.counit.app E)).app K ≫ e.hom) ∧
      ((((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj (H.obj E))).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).map
          (comparisonOpenTensorIso P.Coefficient f (H.obj E) K).inv ≫ z.2 =
        ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
          ((compactSupportSiteComparison P.Coefficient c).hom.app
            ⟨H.obj E, finiteSiteProjectionInput_plus_source P X (H.obj E) hHE⟩)).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) ≫
          (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
            (ModuleCat.{u + 1} P.Coefficient)
            ((Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} P.Coefficient) c).obj (H.obj E))).inv.app K ≫
          D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map
            (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
              (adj.counit.app E)).app K ≫ e.hom)) ∧
      boundedSiteHomEquiv P aX aY f hf c d hd H adj
        ⟨_, finiteSiteProjectionInput_plus P f (H.obj E) K hHE hK⟩
        ((siteComparisonDerivedPullbackPlus Y P.Coefficient).obj Q) z.2 =
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
          ((adj.homEquiv _ Q.obj) z.1) ≫ boundedSiteRho P.Coefficient H Q.obj := by
  sorry

/-- The named theta map has the normalized pro-etale adjunction transpose.
The displayed pro-etale input map is the uniquely projection/counit-normalized
map in finiteSiteTensorTranspose specialized to the coefficient unit and unitor.
Thus it is the specified theta, rather than an arbitrary isomorphism of endpoints.
Source: blueprint lem-pur-co-smooth-etale-locality, Step 3
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: specialize the tensor-transpose calculation to the coefficient unit,
using its canonical unitor. The etale adjunct is dualizingComplexTensorMap by its
definition. The preceding projection and counit equations identify its comparison
with the actual pro-etale inverse-projection/counit map. The specified Hom-chain
formula gives rho composed with comparison of that named theta. Tensor symmetry
is carried across the specified monoidal comparison as well. -/
theorem finiteSiteThetaTransport
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) [HasCompactification f] (d : ℕ)
    (hd : topologicalKrullDim (HasCompactification.compactification f).Z ≤
      (d : WithBot ℕ∞)) :
    let c := HasCompactification.compactification f
    let H := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f
    let adj := Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) f
    ∀ (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
      (hω : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X
        (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f))
      (hK : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
        P.level P.level_pos Y K.obj),
      let J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient)) :=
        ⟨_, finiteSiteProjectionInput_plus P f _ K.obj hω hK⟩
      let θ := Etale.dualizingComplexTensorMap P.Coefficient f K.obj
      boundedSiteHomEquiv P aX aY f hf c d hd H adj J
        ((siteComparisonDerivedPullbackPlus Y P.Coefficient).obj K)
        ((compactSupportSiteComparison P.Coefficient c).hom.app J ≫
          D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map
            ((adj.homEquiv J.obj K.obj).symm θ)) =
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map θ ≫
          boundedSiteRho P.Coefficient H K.obj := by
  sorry

/-- All generated refinement, composition and restriction diagrams commute after
site comparison. Consequently the Hom transposes of their counit composites agree.
The diagram constructors fix the geometric maps; no commutativity is assumed here.
Source: blueprint lem-pur-co-smooth-etale-locality, Steps 1 and 3;
Stacks Tags 0F7C, 0F7D and 0B65; node proof steps 5 and 6
(blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: compactSupportSiteCoherence gives the square for every generator, identity,
composition and whiskering, including further open restrictions and compatible
boundary changes. Postcompose with the etale counit or any map z and cancel the
invertible target boundary. Precompose with the source boundary and its etale
identification. The resulting two maps satisfy the compatibility premise of
boundedSiteAdjunctionTranspose. Its transpose formula identifies the right-adjoint
conjugates when z is a counit, including iterated compact-support compositors.
Apply mate-pasting to the generated compositions; injectivity of the Hom equivalence
proves all identity, refinement, composition and restriction compatibilities. -/
theorem finiteSiteDiagramTransposes
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X T : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (f : X ⟶ T) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aT = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : Etale.DerivedCategoryModule P.Coefficient T ⥤
      Etale.DerivedCategoryModule P.Coefficient X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (diagram : CompactSupportSiteDiagram P b₀ b₁)
    (e : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj J.obj ≅ b₀.etale.obj)
    (z : b₁.etale.obj ⟶ K.obj) :
    boundedSiteHomEquiv P aX aT f hf c d hd H adj J
      ((siteComparisonDerivedPullbackPlus T P.Coefficient).obj K)
      ((compactSupportSiteComparison P.Coefficient c).hom.app J ≫
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).map e.hom ≫
        b₀.comparison.hom ≫ diagram.proEtaleMap ≫ b₁.comparison.inv ≫
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).map z) =
    D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
      ((adj.homEquiv J.obj K.obj)
        (e.hom ≫ DerivedCategory.Plus.ι.map diagram.etaleMap ≫ z)) ≫
      boundedSiteRho P.Coefficient H K.obj := by
  sorry

/-- Cartesian compact-support exchange and every counit transpose are preserved.
No separatedness assumption is imposed on the base-change map g. The arbitrary
postmap z includes the counit defining the dualizing base-change map. The second
clause retains the canonical exchange under every change of origin.
Source: blueprint lem-pur-co-smooth-etale-locality, Step 3; Stacks Tag 0F7F;
node proof step 6 (blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: compactSupport_exchange_transport identifies the actual compactification
exchanges under their two specified boundary isomorphisms. Compose with C(z)
after the inverse target boundary. Taking the specified Hom-chain transpose gives
the first equation. Invertibility of compact-support exchange on the bounded-below
etale-origin domain also identifies its inverse, giving the dualizing comparison.
Mate-pasting and compactSupportSiteCoherence give successive Cartesian base changes
and all further compatible open restrictions. Naturality in an origin isomorphism
cancels that isomorphism and gives the second clause, exactly as in node step 6. -/
theorem finiteSiteExchangeTransposes
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (aX' : X' ⟶ Spec (.of P.field.k)) (aY' : Y' ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX'] [QuasiCompact aX']
    [LocallyOfFiniteType aY'] [QuasiCompact aY']
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (hf' : f' ≫ aY' = aX') (d : ℕ)
    (hd : topologicalKrullDim (c.ofIsPullback sq).Z ≤ (d : WithBot ℕ∞))
    (H : Etale.DerivedCategoryModule P.Coefficient Y' ⥤
      Etale.DerivedCategoryModule P.Coefficient X')
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq) ⊣ H) :
    (∀ (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
      (J : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
      (K : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
      (e : (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq)).obj J.obj ≅
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).mapDerivedCategoryPlus.obj
          ((coherenceEtaleFunctor P.Coefficient c).obj L)).obj)
      (z : ((coherenceEtaleFunctor P.Coefficient (c.ofIsPullback sq)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) g').mapDerivedCategoryPlus.obj
          L)).obj ⟶ K.obj),
      boundedSiteHomEquiv P aX' aY' f' hf' (c.ofIsPullback sq) d hd H adj J
        ((siteComparisonDerivedPullbackPlus Y' P.Coefficient).obj K)
        ((compactSupportSiteComparison P.Coefficient (c.ofIsPullback sq)).hom.app J ≫
          D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y').map e.hom ≫
          (compactExchangeTransportSource P.Coefficient g c).hom.app L ≫
          (rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} P.Coefficient) sq c).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj L.obj) ≫
          (compactExchangeTransportTarget P.Coefficient sq c).inv.app L ≫
          D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y').map z) =
      D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').map
        ((adj.homEquiv J.obj K.obj)
          (e.hom ≫ DerivedCategory.Plus.ι.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
              P.Coefficient sq c).app L) ≫ z)) ≫ boundedSiteRho P.Coefficient H K.obj) ∧
    (∀ (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
      (N : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (α : D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj L.obj ≅ N),
      IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} P.Coefficient) sq c).app N) ∧
      compactExchangeTransportAtWitness P.Coefficient sq c L N α =
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} P.Coefficient) sq c).app N) := by
  sorry

/-- Equality is reflected by site comparison, and the transport of every natural map
is independent of both retained etale origins. This applies simultaneously to all
counit, projection and exchange composites above, since they are natural in inputs.
Source: blueprint lem-pur-co-smooth-etale-locality, Step 3; Stacks Tag 09AK;
node proof step 7 (blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: comparison is fully faithful on bounded-below etale complexes. For two origins
of N, fullness lifts the transition between the two origin isomorphisms uniquely;
faithfulness lifts its inverse and both identity equations. Naturality in that lifted
isomorphism identifies the two transported maps. With two inputs apply this argument
in each variable. Every bounded constructible pro-etale input has an etale origin by
constructible_proEtale_origin, so no input on the stated domain is lost. -/
theorem finiteSiteOriginIndependence
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (∀ (J K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) (v w : J.obj ⟶ K.obj),
      D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).map v =
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).map w ↔ v = w) ∧
    (∀ (J J' : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
      (N : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
      (α : D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj J.obj ≅ N)
      (α' : D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj J'.obj ≅ N),
      ∃! v : J.obj ⟶ J'.obj,
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).map v =
          α.hom ≫ α'.inv) ∧
    (∀ (F G : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))
        ⥤ _root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
      (τ : F ⟶ G)
      (J J' : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) (e : J ≅ J')
      (N₀ N₁ : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
      (a : F.obj J ≅ N₀) (b : G.obj J ≅ N₁),
      a.inv ≫ τ.app J ≫ b.hom =
        (F.mapIso e.symm ≪≫ a).inv ≫ τ.app J' ≫ (G.mapIso e.symm ≪≫ b).hom) := by
  sorry

/-- Every intrinsically bounded constructible pro-etale complex has a bounded
constructible etale origin. Source: blueprint lem-pur-co-smooth-etale-locality,
Step 3, Stacks Tag 09AK (blueprint: lem-pur-finite-site-counit-projection-transport).
Proof: finite type over the field makes T Noetherian. Apply the fixed-module
constructible comparison theorem to the given bounded complex and its intrinsic
constructible cohomology sheaves. The reconstructed etale complex is bounded
constructible, hence bounded below, and its comparison isomorphism is the required
origin. This includes the empty scheme and the zero complex. -/
theorem finiteSiteConstructibleOrigin
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (N : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (_hb : _root_.DerivedCategory.TStructure.t.bounded N)
    (_hc : ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T P.Coefficient
      ((_root_.DerivedCategory.homologyFunctor _ i).obj N)) :
    ∃ J : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)),
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient T J.obj ∧
        Nonempty (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj J.obj ≅ N) := by
  sorry

end AlgebraicGeometry.ProEtale
