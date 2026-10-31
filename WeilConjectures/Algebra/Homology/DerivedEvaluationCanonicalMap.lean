/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingHomExtensionDefsSupplement
public import WeilConjectures.Algebra.Homology.RingedInternalHomSignedCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.KFlatConeTrianglePresentation
import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # The canonical derived evaluation comparison

Source: Stacks Project, More on Algebra, Tags 0A67, 0A60 and 064J;
Cohomology on Sites, Tag 08JC (blueprint: lem-trf-derived-evaluation-canonical-map).

The comparison is uniquely determined by its adjunction-transpose formula.
Its existence theorem supplies that formula and its functorial and signed
triangulated interface, without importing any downstream invertibility theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace DerivedCategory

/-- The one-object-site presentation of the ordinary module derived category.
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-canonical-map). -/
abbrev evaluationDerivedCategory (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (RingSiteModules R)] := DerivedCategory (RingSiteModules R)

variable (R : Type u) [CommRing R] [HasDerivedCategory.{u} (RingSiteModules R)]

/-- Derived tensor with the fixed derived Hom object.
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-canonical-map). -/
abbrev evaluationTensorFunctor (L M : evaluationDerivedCategory R) :
    evaluationDerivedCategory R ⥤ evaluationDerivedCategory R :=
  tensorLeft ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) L).obj M)

/-- Contravariant internal Hom into a fixed target.
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-canonical-map). -/
def evaluationDualFunctor (L : evaluationDerivedCategory R) :
    (evaluationDerivedCategory R)ᵒᵖ ⥤ evaluationDerivedCategory R :=
  Prod.sectL (evaluationDerivedCategory R)ᵒᵖ L ⋙
    SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)

/-- The covariant double derived Hom functor.
Source: Stacks 0A67 (blueprint: lem-trf-derived-evaluation-canonical-map). -/
def evaluationDoubleHomFunctor (L M : evaluationDerivedCategory R) :
    evaluationDerivedCategory R ⥤ evaluationDerivedCategory R :=
  (evaluationDualFunctor R L).rightOp ⋙ evaluationDualFunctor R M

/-- The signed double contravariant source-shift comparison, including the
triangle-reversal factor `(-1)^m`. Each source shift is the canonical adjunction
mate of the Koszul total-tensor shift, and `shiftFunctor` transports `-(-m)` to `m`.
Source: Stacks 0A60, 08JC (blueprint: lem-trf-derived-evaluation-canonical-map). -/
def evaluationDoubleHomShift (L M K : evaluationDerivedCategory R) (m : ℤ) :
    (evaluationDoubleHomFunctor R L M).obj (K⟦m⟧) ⟶
      ((evaluationDoubleHomFunctor R L M).obj K)⟦m⟧ :=
  m.negOnePow •
    (((evaluationDualFunctor R M).mapIso
      (((SignedRingedHom.sourceShift ⊥
        (CochainComplex.onePointRingSheaf R) K m).app L).op)).inv ≫
      ((SignedRingedHom.sourceShift ⊥ (CochainComplex.onePointRingSheaf R)
        ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)
        (-m)).app M).hom ≫
      eqToHom (congrArg
        (fun n : ℤ ↦ ((evaluationDoubleHomFunctor R L M).obj K)⟦n⟧) (neg_neg m)))

/-- The specified evaluation transpose is natural in all three variables and is
a morphism of exact functors with the standard signed shift comparison.
Source: Stacks 0A67, 0A60, 064J and 08JC
(blueprint: lem-trf-derived-evaluation-canonical-map).

Proof:
1. Use the closed derived tensor--Hom adjunction on the one-object ringed site
(lem-sf-ringed-derived-closed-symmetric-monoidal). Swap the third tensor factor
past the second and compose the two counits. Its transpose is the specified map.
2. Counit naturality identifies the three variable squares after uncurrying:
they evaluate respectively f(u(x)), v(h(f(x))) and h(t(f(x))). Transpose back.
3. K-injective representatives J,I and a K-flat representative P, supplied by
prop-pur-kinjective-resolutions-exist and lem-pc-kflat-resolution, compute the
map as h tensor x sent to f ↦ (-1)^(|x||f|) h(f(x)). This uses
def-pur-derived-internal-hom, lem-weil-pbc-site-derived-tensor-descent,
lem-sc-derived-hom-tensor-total and def-pur-hom-complex. Tensor direct sums have
finite support, so the formula also defines the unbounded comparison.
4. Present triangles by K-flat cones (lem-pc-kflat-cone-triangle-presentation).
The tensor-cone comparison (lem-pc-tensor-mapping-cone-iso) multiplies the
shifted summand by (-1)^|h|. Double contravariant Hom reverses triangles twice
(lem-weil-pbc-ringed-internal-hom-exact-restriction), with the extra (-1)^m.
5. The source-Hom shift multiplies degree-q maps by (-1)^(mq). The resulting
double comparison on g in degree n, tested at f in degree c, is (-1)^(m(n+c)).
For |h|=a, |x|=b and n=a+b-m, the identity
(b-m)(c+m)+m(n+c) ≡ bc+ma mod 2 proves the shift square.
6. Naturality gives the first two triangle squares. Its square on the connecting
map, followed by the shift square, gives the third. Thus the components are
a morphism of distinguished triangles, without asserting invertibility. -/
theorem derived_evaluation_canonical_map :
    ∃ e : ∀ K L M : evaluationDerivedCategory R,
      (evaluationTensorFunctor R L M).obj K ⟶ (evaluationDoubleHomFunctor R L M).obj K,
    (∀ K L M : evaluationDerivedCategory R,
      e K L M =
        (SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf R)
          ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf R) K).obj L)).homEquiv
          _ M ((α_ _ _ _).hom ≫
            _ ◁ ((β_ K _).hom ≫
              (SignedRingedHom.adjunction ⊥
                (CochainComplex.onePointRingSheaf R) K).counit.app L) ≫
            (SignedRingedHom.adjunction ⊥
              (CochainComplex.onePointRingSheaf R) L).counit.app M)) ∧
    (∀ (K K' L L' M M' : evaluationDerivedCategory R)
      (f : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M'),
      ((SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
        (l.op, m) ⊗ₘ f) ≫ e K' L' M' =
      e K L M ≫
        (SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
          (X := (op ((SignedRingedHom.hom ⊥
            (CochainComplex.onePointRingSheaf R) K).obj L), M))
          (Y := (op ((SignedRingedHom.hom ⊥
            (CochainComplex.onePointRingSheaf R) K').obj L'), M'))
          (((SignedRingedHom.homFunctor ⊥ (CochainComplex.onePointRingSheaf R)).map
            (f.op, l)).op, m)) ∧
    ∀ L M : evaluationDerivedCategory R,
      (evaluationTensorFunctor R L M).IsTriangulated ∧
      ∃ _ : (evaluationDoubleHomFunctor R L M).CommShift ℤ,
        (∀ (K : evaluationDerivedCategory R) (m : ℤ),
          ((evaluationDoubleHomFunctor R L M).commShiftIso m).hom.app K =
            evaluationDoubleHomShift R L M K m) ∧
        (evaluationDoubleHomFunctor R L M).IsTriangulated ∧
        (∀ (K : evaluationDerivedCategory R) (m : ℤ),
          e (K⟦m⟧) L M ≫
            ((evaluationDoubleHomFunctor R L M).commShiftIso m).hom.app K =
          ((evaluationTensorFunctor R L M).commShiftIso m).hom.app K ≫
            (e K L M)⟦m⟧') ∧
        ∀ (T : Pretriangulated.Triangle (evaluationDerivedCategory R))
          (_hT : T ∈ Pretriangulated.distinguishedTriangles),
          ∃ t : (evaluationTensorFunctor R L M).mapTriangle.obj T ⟶
            (evaluationDoubleHomFunctor R L M).mapTriangle.obj T,
            t.hom₁ = e T.obj₁ L M ∧
            t.hom₂ = e T.obj₂ L M ∧
            t.hom₃ = e T.obj₃ L M := by
  sorry

end DerivedCategory
