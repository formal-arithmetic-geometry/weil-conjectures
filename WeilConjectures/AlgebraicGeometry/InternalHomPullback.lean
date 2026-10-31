/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LegacySitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientConventions
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.FinitePullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.Algebra.Homology.RingedInternalHomSignedCalculus
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.RingedSitePerfectDuality
import WeilConjectures.CategoryTheory.RingedSiteDualityMaps
import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Internal Hom and pullback from a site-perfect first variable

Source: Weil conjectures blueprint, main-20261015,
sec-six-functors/sk-thm-sf-internal-hom-pullback/thm-trf-internal-hom-pullback.md
(blueprint: thm-trf-internal-hom-pullback).

The comparison is the transpose of pulled-back evaluation after the inverse
canonical tensor comparison. Its shift and triangle assertions refer to the
representative-normalized Hom shifts, including the connecting arrow.
The natural-number index n denotes the positive coefficient level n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
  {X Y : Scheme.{u}} (g : Y ⟶ X)
  [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
  [hX : ∀ x : X, Invertible (l : X.residueField x)]

/-- The canonical comparison, with exactly the pulled-back evaluation as transpose.
Source: blueprint proof step 1 (blueprint: thm-trf-internal-hom-pullback). -/
def finiteHomPullback
    (M N : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) :
    (finiteDerivedPullback l E n g).obj
        ((finiteIntrinsicDerivedInternalHom l E X n).obj (op M, N)) ⟶
      (finiteIntrinsicDerivedInternalHom l E Y n).obj
        (op ((finiteDerivedPullback l E n g).obj M),
          (finiteDerivedPullback l E n g).obj N) :=
  finiteIntrinsicTranspose l E Y n _ _ _
    (((canonicalFinitePullbackTensor l E g n)
        ((finiteIntrinsicDerivedInternalHom l E X n).obj (op M, N)) M).inv ≫
      (finiteDerivedPullback l E n g).map (finiteIntrinsicEvaluation l E X n M N))

/-- Naturality includes arbitrary, possibly noninvertible, maps in the perfect
first variable. In fact this identity holds for all ambient objects.
Source: blueprint proof step 6 (blueprint: thm-trf-internal-hom-pullback).
Proof: the counit identity for H(a,b) is naturality of evaluation in the closed
structure (lem-sf-ringed-derived-closed-symmetric-monoidal). Apply pullback,
use bifunctoriality of its canonical tensor comparison
(lem-sfb-ringed-derived-monoidal-comparisons), and transpose. The injectivity
of the adjunction Hom equivalence gives the displayed equality. -/
theorem finiteHomPullback_naturality
    (M M' N N' : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1)))
    (a : M' ⟶ M) (b : N ⟶ N') :
    (finiteDerivedPullback l E n g).map
        ((finiteIntrinsicDerivedInternalHom l E X n).map (Prod.mkHom a.op b)) ≫
        finiteHomPullback l E n g M' N' =
      finiteHomPullback l E n g M N ≫
        (finiteIntrinsicDerivedInternalHom l E Y n).map
          (Prod.mkHom ((finiteDerivedPullback l E n g).map a).op
            ((finiteDerivedPullback l E n g).map b)) := by
  sorry

/-- Pullback after the fixed-source internal-Hom functor.
Source: blueprint comparison source (blueprint: thm-trf-internal-hom-pullback). -/
abbrev finiteHomPullbackSource
    (M : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) :=
  RingedHomUniverses.hom.{u + 1, u, u, u + 2} (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n) M ⋙
    finiteDerivedPullback l E n g

/-- Internal Hom from the pulled-back first variable, after pullback.
Source: blueprint comparison target (blueprint: thm-trf-internal-hom-pullback). -/
abbrev finiteHomPullbackTarget
    (M : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) :=
  finiteDerivedPullback l E n g ⋙
    RingedHomUniverses.hom.{u + 1, u, u, u + 2} (ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)
      ((finiteDerivedPullback l E n g).obj M)

/-- Compatibility in the second variable with the normalized derived shifts.
The square uses the canonical termwise-derived shift of pullback.
Source: blueprint shift clause (blueprint: thm-trf-internal-hom-pullback). -/
def FiniteHomPullbackRightShift
    (M N : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) (s : ℤ) : Prop :=
  ((finiteHomPullbackSource l E n g M).commShiftIso s).hom.app N ≫
      (finiteHomPullback l E n g M N)⟦s⟧' =
    finiteHomPullback l E n g M (N⟦s⟧) ≫
      ((finiteHomPullbackTarget l E n g M).commShiftIso s).hom.app N

/-- Compatibility with the signed first-variable shift, including the inverse
pullback shift on the contravariant input.
Source: blueprint shift clause and proof step 6
(blueprint: thm-trf-internal-hom-pullback). -/
def FiniteHomPullbackLeftShift
    (M N : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) (s : ℤ) : Prop :=
  (finiteDerivedPullback l E n g).map
      ((RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n) M s).hom.app N) ≫
      finiteHomPullback l E n g (M⟦s⟧) N ≫
      (finiteIntrinsicDerivedInternalHom l E Y n).map
        (Prod.mkHom (((finiteDerivedPullback l E n g).commShiftIso s).inv.app M).op
          (𝟙 ((finiteDerivedPullback l E n g).obj N))) =
    ((finiteDerivedPullback l E n g).commShiftIso (-s)).hom.app
        ((finiteIntrinsicDerivedInternalHom l E X n).obj (op M, N)) ≫
      (finiteHomPullback l E n g M N)⟦-s⟧' ≫
      (RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2} (ProEt.topology Y)
        (integralCoefficientCommRingSheaf l E Y n)
          ((finiteDerivedPullback l E n g).obj M) s).hom.app
            ((finiteDerivedPullback l E n g).obj N)

/-- The comparison is a morphism between the two distinguished image triangles,
with its three specified components. The definition of TriangleMorphism includes
commutation with the connecting arrow, using the normalized shift structures.
Source: blueprint distinguished-triangle clause
(blueprint: thm-trf-internal-hom-pullback). -/
def FiniteHomPullbackTriangle
    (M : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1)))
    (T : Triangle (proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1)))) : Prop :=
  (finiteHomPullbackSource l E n g M).mapTriangle.obj T ∈ distTriang _ ∧
    (finiteHomPullbackTarget l E n g M).mapTriangle.obj T ∈ distTriang _ ∧
    ∃ τ : (finiteHomPullbackSource l E n g M).mapTriangle.obj T ⟶
        (finiteHomPullbackTarget l E n g M).mapTriangle.obj T,
      τ.hom₁ = finiteHomPullback l E n g M T.obj₁ ∧
      τ.hom₂ = finiteHomPullback l E n g M T.obj₂ ∧
      τ.hom₃ = finiteHomPullback l E n g M T.obj₃

/-- All clauses for the stated site-perfect and finite-Tor constructible variables.
Naturality in both variables is expressed by finiteHomPullback_naturality.
Source: blueprint theorem and proof step 6 (blueprint: thm-trf-internal-hom-pullback). -/
def FiniteHomPullbackProperties : Prop :=
  ∀ (M : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))),
    IsFiniteCoefficientSitePerfect l E X n M →
    (∀ N : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1)),
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X N →
      IsIso (finiteHomPullback l E n g M N) ∧
        (∀ s : ℤ, FiniteHomPullbackRightShift l E n g M N s) ∧
        (∀ s : ℤ, FiniteHomPullbackLeftShift l E n g M N s)) ∧
    (∀ T : Triangle (proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))),
      T ∈ distTriang _ →
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X T.obj₁ →
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X T.obj₂ →
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X T.obj₃ →
      FiniteHomPullbackTriangle l E n g M T)

/-- Transport the base-field unit along the canonical affine morphism from the
residue-field point. This supplies the implied invertibility assumption without
adding a hypothesis on either scheme.
Source: coefficient conventions, ell different from p
(blueprint: thm-trf-internal-hom-pullback). -/
@[instance_reducible]
def finiteHomPrimeInvertible (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (x : W) :
    Invertible (l : W.residueField x) :=
  IsUnit.invertible (by
    let φ : D.k →+* W.residueField x :=
      (Scheme.Spec.preimage
        (W.fromSpecResidueField x ≫ (W ↘ Spec (.of D.k)))).unop.hom
    simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map φ)

/-- The evaluation-normalized internal-Hom pullback comparison is invertible,
natural in both inputs, commutes with their shifts, and acts on distinguished
triangles in the finite-Tor constructible second input.
Source: Weil blueprint main-20261015, thm-trf-internal-hom-pullback
(blueprint: thm-trf-internal-hom-pullback).

Proof:
1. Use the closed ringed-site derived structure and the coherent strong monoidal
pullback (lem-sf-ringed-derived-closed-symmetric-monoidal,
lem-sfb-ringed-derived-monoidal-comparisons). finiteHomPullback is exactly the
transpose of pulled-back evaluation after the inverse tensor comparison.
2. Site-perfectness gives the canonical finite-perfect evaluation isomorphism
T tensor H(M,1) to H(M,T) (lem-sfb-ringed-site-perfect-duality). The internal
composition normalization (lem-sfb-ringed-site-duality-maps,
def-coef-ringed-tensor-hom-model) identifies its counit with 1_T tensor e.
The closed adjunction therefore gives - tensor M adjoint to - tensor H(M,1).
Its unit at 1 and the two triangle identities give an actual dual pair.
3. Apply pullback to both triangle identities. Coherent tensor and unit
comparisons identify the images with the two triangle identities for FM and FD.
4. Apply lem-sfb-dual-tensor-adjunctions to this dual pair. Its explicit inverse
Hom bijections identify - tensor FD with H(FM,-); transposing their counits
shows the two comparison arrows are inverse.
5. Compose F(H(M,N)) to F(N tensor D), then FN tensor FD, then H(FM,FN).
Transpose, use the evaluation identities in steps 2 and 4, and cancel the
invertible finite-perfect evaluation. The result is precisely the transpose
in step 1, so the canonical map itself, rather than an arbitrary iso, is invertible.
6. Naturality is finiteHomPullback_naturality. Exact pullback and exact internal
Hom are lem-weil-pbc-ringed-topoi-derived-pullback and
lem-weil-pbc-ringed-internal-hom-exact-restriction. On representatives the Hom
differential is d_N f - (-1)^degree f d_M (def-pur-hom-complex). The normalized
right shift is unsigned reindexing; the left shift multiplies a degree-k map
by (-1)^(s*k). Evaluation commutes with these reindexings and the termwise
pullback shift. Evaluation into a cone is componentwise on N2 plus N1[1],
so also commutes with inclusion, projection, differential and connecting arrow.
Descend these identities and restrict the second variable to D^b_ctf. -/
theorem internalHomPullback
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] :
    @FiniteHomPullbackProperties l _ E _ _ _ n X Y g
      (finiteHomPrimeInvertible l D hl Y) (finiteHomPrimeInvertible l D hl X) := by
  sorry

end WeilConjectures
