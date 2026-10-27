module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.Topology.SpectralSpace.ClopenComponentHomeomorphism
import Sheaf.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Spectral.Basic

/-!
# Assembly of the norm-topological scalar tests

Source: blueprint main-20261015, six-functors basics, direct-images proof paragraph (3),
agent-formulated sublemma, retained norm-coefficient argument steps 6--7
(blueprint: lem-sfb-norm-scalar-test-assembly).

Derived evaluation on the small site of X computes sections on its localized sites.
Restriction is derived from the actual section restriction, using K-injective resolutions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Sections of an abelian sheaf over a pro-etale object.
Source: direct-images paragraph (3), scalar tests
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
abbrev normScalarEvaluation (X : Scheme.{u}) (V : X.ProEt) :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)

/-- Actual restriction of sections, natural in the abelian sheaf.
Source: direct-images paragraph (3), scalar tests
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
def normScalarSectionRestriction {X : Scheme.{u}} {T V : X.ProEt} (j : T ⟶ V) :
    normScalarEvaluation X V ⟶ normScalarEvaluation X T :=
  Functor.whiskerLeft (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    ((evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).map j.op)

/-- The abelian coefficient sheaf p_X^* C(-,F), with every continuous function retained.
Source: direct-images paragraph (3), norm coefficients
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
def normScalarCoefficient (X : Scheme.{u}) (F : Type u) [NormedField F] :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (upperStarFromPoint X).obj (Profinite.continuousMapRingObjOfUniverse.{u, u} F)

/-- Unbounded derived evaluation of an abelian sheaf in degree zero.
Source: Stacks 0D6F, localized derived sections, and direct-images paragraph (3)
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
def normScalarDerivedSections (X : Scheme.{u}) (V : X.ProEt)
    (A : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  (normScalarEvaluation X V).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor _ 0).obj A)

/-- The canonical derived restriction, obtained by deriving section restriction.
Source: direct-images paragraph (3), actual scalar restriction
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
def normScalarDerivedRestriction {X : Scheme.{u}} {T V : X.ProEt} (j : T ⟶ V)
    (A : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    normScalarDerivedSections X V A ⟶ normScalarDerivedSections X T A :=
  (Functor.rightDerivedFunctorNatTrans (normScalarSectionRestriction j)).app
    ((DerivedCategory.singleFunctor _ 0).obj A)

/-- The canonical identification H^0 RΓ(V,A[0]) = A(V), for left exact evaluation.
Source: Stacks 01FT and direct-images paragraph (3)
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
def normScalarH0SectionsIso (X : Scheme.{u}) (V : X.ProEt)
    (A : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).obj
      (normScalarDerivedSections X V A) ≅ A.obj.obj (op V) :=
  (normScalarEvaluation X V).homologyRightDerivedFunctorObjSingleFunctorIso A 0 ≪≫
    (normScalarEvaluation X V).rightDerivedZeroIsoSelf.app A

/-- The principal open in a pro-etale test, as an object of the original small site.
It is the base change of X[1/f], including the empty and identity opens.
Source: direct-images paragraph (3), punctured tests
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
def normScalarPuncturedTest (X : Scheme.{u}) (f : Γ(X, ⊤)) (V : X.ProEt) : X.ProEt :=
  Scheme.ProEt.mk ((V.left.basicOpen (V.hom.appTop.hom f)).ι ≫ V.hom)

/-- The actual principal-open inclusion over X.
Source: direct-images paragraph (3), punctured tests
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
def normScalarPuncturedInclusion (X : Scheme.{u}) (f : Γ(X, ⊤)) (V : X.ProEt) :
    normScalarPuncturedTest X f V ⟶ V :=
  MorphismProperty.Over.homMk (V.left.basicOpen (V.hom.appTop.hom f)).ι rfl

/-- The continuous-function abelian sheaf used to express the degree-zero normalization.
Source: Hemo--Richarz--Scholbach, Example 3.1, all continuous functions
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
def normScalarContinuousSheaf (X : Scheme.{u}) (F : Type u) [NormedField F] :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf X F)

/-- The scalar conclusion: the actual derived restriction is invertible, its H^0 map is
restriction of all continuous functions under the canonically normalized realization,
and positive cohomology on the punctured test vanishes. The realization is characterized
by pulling each profinite test function back along the specified projection, so no
arbitrary identification or finite-subextension-valued replacement is used.
Source: direct-images paragraph (3), retained norm argument steps 6--7
(blueprint: lem-sfb-norm-scalar-test-assembly). -/
def NormScalarTestResult (X : Scheme.{u}) (f : Γ(X, ⊤)) (V : X.ProEt)
    (F : Type u) [NormedField F] : Prop :=
  IsIso (normScalarDerivedRestriction (normScalarPuncturedInclusion X f V)
    (normScalarCoefficient X F)) ∧
  (∃ e : normScalarCoefficient X F ≅ normScalarContinuousSheaf X F,
    (∀ (S : Profinite.{u}) (g : C(S, F)),
      (((pointUpperStarLowerStarAdjunction.comp
          (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv
            _ _ e.hom).hom.app (op S)) (ULift.up g) =
        ULift.up (g.comp (profiniteTestProjection X S))) ∧
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        (normScalarDerivedRestriction (normScalarPuncturedInclusion X f V)
          (normScalarCoefficient X F)) ≫
        (normScalarH0SectionsIso X (normScalarPuncturedTest X f V)
          (normScalarCoefficient X F)).hom ≫
        e.hom.hom.app (op (normScalarPuncturedTest X f V)) =
      (normScalarH0SectionsIso X V (normScalarCoefficient X F)).hom ≫
        e.hom.hom.app (op V) ≫
        (normScalarContinuousSheaf X F).obj.map (normScalarPuncturedInclusion X f V).op) ∧
  ∀ (q : ℤ), 0 < q → IsZero
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
      (normScalarDerivedSections X (normScalarPuncturedTest X f V)
        (normScalarCoefficient X F)))

/-- Complete scalar tests and the cyclic degree-zero test imply the scalar tests for a
finite l-adic extension and its algebraic closure with the extended norm topology.
Source: blueprint main-20261015, direct-images paragraph (3); agent-formulated sublemma
from retained norm-coefficient proof steps 6--7
(blueprint: lem-sfb-norm-scalar-test-assembly).

Proof: (1) The finite constant representation identifies Z/ell sections with clopen
partitions. Naturality in finite label maps gives pointwise ring operations. Idempotents
are characteristic functions of clopens, so the cyclic bijection gives a clopen bijection.
Use lem-weil-pbc-proetale-finite-constant-representable.
(2) V and its principal open T are affine, hence qcqs and spectral, by
lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-qcqs-scheme-spectral. Apply
lem-sfb-spectral-clopen-component-homeomorphism to obtain the actual component homeomorphism.
(3) The extending norms on E and Omega are ultrametric, by
lem-weil-l-adic-extension-absolute-value, applied to finite subextensions for Omega.
Clopen norm balls separate points, so both fields are totally disconnected. The canonical
realization lem-weil-pbc-condensed-field-continuous-realization identifies coefficient
restriction with precomposition by T -> V. Localization is
lem-weil-proetale-weakly-etale-localization.
(4) Continuous functions factor through the quotient component spaces. Composing with
the inverse component homeomorphism gives the unique continuous extension to V, including
empty spaces. This is the degree-zero restriction and the displayed normalized square.
(5) Exact weakly contractible evaluation, supplied by
lem-weil-pbc-proetale-abelian-evaluation-colimits, makes positive source cohomology zero.
The finite extension E is complete by lem-weil-l-adic-extension-complete, so the complete
scalar assumption applies to E and gives the E conclusion.
(6) The isometric field completion from lem-sfb-normed-field-completion is ultrametric by
continuity of the norm inequality. The complete scalar test makes its positive T-cohomology
zero. The actual completion map is injective in positive degrees by
lem-sfb-norm-completion-positive-cohomology-mono, on precisely the given tower and tests.
Thus positive T-cohomology with the original Omega coefficients is zero.
(7) Sections are left exact. Use lem-weil-pbc-ring-sheaves-grothendieck,
lem-weil-pbc-derived-functor-negative-vanishing and src-right-derived-functor-plus-compatibility
to identify H^0 with sections and make negative cohomology vanish. The actual restriction
is therefore a quasi-isomorphism in every degree, hence invertible in the ordinary derived
category. No completeness of Omega or union of finite-extension-valued functions is used. -/
theorem norm_scalar_test_assembly
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E Ω : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] [NormedField Ω] [NormedAlgebra E Ω]
    [IsAlgClosure E Ω]
    (I : Type u) [PartialOrder I] [OrderBot I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [HasColimit R]
    (κ : (Functor.const I).obj (CommRingCat.of k) ⟶ R)
    (hregular : ∀ i : I, IsRegularScheme (Spec (R.obj i)))
    (hfiniteType : ∀ i : I, LocallyOfFiniteType (Spec.map (κ.app i)) ∧
      QuasiCompact (Spec.map (κ.app i)))
    (hfiniteFlat : ∀ (i j : I) (h : i ≤ j),
      IsFinite (Spec.map (R.map (homOfLE h))) ∧ Flat (Spec.map (R.map (homOfLE h))))
    (f₀ : R.obj ⊥)
    (hregularElement : ∀ i : I, (R.map (homOfLE (bot_le : ⊥ ≤ i))).hom f₀ ∈
      nonZeroDivisors (R.obj i))
    (htorsion : ∀ (V : (Spec (colimit R)).ProEt) [IsAffine V.left],
      (Scheme.ProEt.topology (Spec (colimit R))).IsWeaklyContractible.{u + 1} V →
      Function.Bijective
        (((constantSheaf (Scheme.ProEt.topology (Spec (colimit R)))
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))).obj.map
            (normScalarPuncturedInclusion (Spec (colimit R))
              ((Scheme.ΓSpecIso (colimit R)).inv ((colimit.ι R ⊥).hom f₀)) V).op))
    (hcomplete : ∀ (V : (Spec (colimit R)).ProEt) [IsAffine V.left],
      (Scheme.ProEt.topology (Spec (colimit R))).IsWeaklyContractible.{u + 1} V →
      ∀ (B : Type u) [NormedField B] [NormedAlgebra ℚ_[ℓ] B]
        [CompleteSpace B] [IsUltrametricDist B],
      IsIso (normScalarDerivedRestriction
        (normScalarPuncturedInclusion (Spec (colimit R))
          ((Scheme.ΓSpecIso (colimit R)).inv ((colimit.ι R ⊥).hom f₀)) V)
        (normScalarCoefficient (Spec (colimit R)) B))) :
    ∀ (V : (Spec (colimit R)).ProEt) [IsAffine V.left],
      (Scheme.ProEt.topology (Spec (colimit R))).IsWeaklyContractible.{u + 1} V →
      NormScalarTestResult (Spec (colimit R))
          ((Scheme.ΓSpecIso (colimit R)).inv ((colimit.ι R ⊥).hom f₀)) V E ∧
      NormScalarTestResult (Spec (colimit R))
          ((Scheme.ΓSpecIso (colimit R)).inv ((colimit.ι R ⊥).hom f₀)) V Ω := by
  sorry

end AlgebraicGeometry.ProEtale
