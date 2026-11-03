/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedEssentialImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenUnitEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePairFlasque
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ClosedFiniteTransport.ClosedFiniteAdjointCounitTransport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedAmbient
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactDerivedAdjunctionUnitShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenClosedTriangle
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-!
# The intrinsic support-localization triangle and its finite exceptional comparison

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/`
`lem-pur-support-localization-triangle.md`, proof paragraphs 1--3, with the finite-domain
correction recorded in the DAG (blueprint: lem-pur-support-localization-triangle).

The ambient support functor is the right derived functor of the actual supported kernel.
The finite exceptional functor is the recorded comparison transport of the etale adjoint.
The latter comparison is asserted only on bounded-below inputs of etale origin.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open WeilConjectures

namespace AlgebraicGeometry.Scheme

variable (P : PurityFiniteSetting.{u})
variable {Z X : Scheme.{u}}
  [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable (s : Z ⟶ X) [IsClosedImmersion s]

/-- The specified support triangle has the meaning of `supportTriangleMeaning`, the derived
support functor preserves bounded-below objects, and every specified support triangle is
distinguished and isomorphic to the adjunction triangle of any derived adjunction
s_* ⊣ Rs_supp^!, with middle component inverse to the resolution map. The hypotheses `hS` and
`a0` are not used by the statement.

Source: blueprint `lem-pur-support-localization-triangle`, proof paragraphs 1--3
(DAG steps 1--5) (blueprint: lem-pur-support-localization-triangle-core-rest).

Proof:
1. Rs_supp^! is computed on a K-injective resolution I with injective terms by the left
exact s_0^!, so a complex bounded below in degree a gives one bounded below in degree a.
2. The support sequence 0 → s_*s_0^!I → I → j_*j^*I → 0 is termwise exact. The cone map
t(b,a)=q(b) has kernel Cone(id), contracted by h(x,a)=(0,x), so t is a quasi-isomorphism
and the transported cone triangle is distinguished (Stacks 0152).
3. Its first arrow is the counit of the normalized derived adjunction and its second the
open unit (with j_*j^*I computing Rj_*j^*K, Stacks 08FI). For an arbitrary derived
adjunction adj, uniqueness of adjoints writes adj.counit as s_*(θ) followed by the
normalized counit for an automorphism θ of Rs_supp^!, which is absorbed in the first
component of the triangle isomorphism; the middle component is the inverse of Q(r.map).
4. Derived maps K → L are unique homotopy classes of chain maps between K-injective
resolutions (Stacks 070Y). The additive functors s_*s_0^!, identity and j_*j^* take such a
map to a morphism of the termwise short exact support sequences and preserve homotopies
(F(f)-F(g)=dF(h)+F(h)d), so the three derived components and the boundary square do not
depend on the representative; uniqueness gives identity and composition.
5. For etale v : X' → X, restriction is exact and preserves injectives and K-injectives
(Stacks 08FI), so v^*I resolves v^*K. Closed and open localization identify v^*s_* with
s'_*v_Z^* and v^*j_* with j'_*v_U^* compatibly with adjunction maps, and exact restriction
commutes with the supported kernel; this gives etale base change. Steps 4 and 5 give
`supportTriangleMeaning`.
-/
theorem purSupportLocalizationTriangleCoreRest
    (P : PurityFiniteSetting.{u}) {Z X U : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (s : Z ⟶ X) [IsClosedImmersion s] [s.IsOver (Spec (.of P.field.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
    (hS : PreservesFiniteColimits (sfConstantModuleDirectImage s P.Ring))
    (a0 : sfConstantModuleDirectImage s P.Ring ⊣ sfIntrinsicClosedUpperShriek s j P.Ring)
    (adj : (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor ⊣
      (sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor) :
    supportTriangleMeaning s j hcomp P.Ring ∧
      (∀ K : DerivedCategory.Plus
          (proEtaleRingModules X (proEtaleConstantRing X P.Ring)),
        DerivedCategory.TStructure.t.plus
          ((sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor.obj K.obj)) ∧
      (∀ (K : CochainComplex.Plus
            (proEtaleRingModules X (proEtaleConstantRing X P.Ring)))
          (r : CochainComplex.KInjectiveResolutionChoice K.obj)
          (hI : ∀ n : ℤ, Injective (r.complex.X n)),
        supportTriangle s j hcomp P.Ring K r hI ∈
          distTriang (proEtaleDerivedCategory X P.Ring) ∧
        ∃ δ, ∃ e : supportTriangle s j hcomp P.Ring K r hI ≅
          purSupportAdjunctionTriangle s j P.Ring adj (DerivedCategory.Q.obj K.obj) δ,
          DerivedCategory.Q.map r.map ≫ e.hom.hom₂ = 𝟙 _) := by
  letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType
    (X ↘ Spec (.of P.field.k))
  refine ⟨purSupportLocalizationTriangleMeaningCore P.Ring s j hcomp,
    purSupportLocalizationTriangleBoundedBelowCore P s j hcomp, ?_⟩
  exact purSupportLocalizationTriangleDistinguishedCore P.Ring s j hcomp hS a0 adj

/-- The finite exceptional comparison and its uniqueness on etale-origin inputs, for any
derived adjunction between closed direct image and the support functor.

Source: blueprint `lem-pur-support-localization-triangle`, proof paragraph 2
(DAG steps 6--9) (blueprint: lem-pur-support-localization-triangle-exceptional).

Proof:
1. Uniqueness of adjoints writes adj.counit as s_*(theta) followed by the counit of the
normalized adjunction of `purSupportLocalizationTriangleCore`, for a unique automorphism
theta; so it suffices to treat the normalized adjunction.
2. For K=nu_X^*B, transport the ordinary etale support triangle by exact nu_X^*. The closed
finite adjoint counit transport identifies its first arrow with the finite exceptional
counit, and bounded-below comparison direct-image isomorphisms identify its open term
with Rj_*j^*K.
3. Normalize this open comparison by transposing the inverse of the restriction of its
second arrow; open full faithfulness makes it invertible and the second arrow becomes the
open adjunction unit.
4. Rotate, apply triangle-morphism extension with identities on the middle and third terms
and rotate back; two-of-three and closed full faithfulness give the isomorphism on Z.
5. Hom(s_*P,Rj_*N[r])=0 by open restriction, so triangle Hom exactness makes maps from s_*P
into the support term unique given their composite with the counit. This gives
uniqueness, naturality on the bounded-below etale derived category, and the triangle
isomorphism for any distinguished completions δS, δE.
-/
theorem purSupportLocalizationTriangleExceptional
    (P : PurityFiniteSetting.{u}) {Z X U : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (s : Z ⟶ X) [IsClosedImmersion s] [s.IsOver (Spec (.of P.field.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
    (adj : (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor ⊣
      (sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor) :
∃! α :
            (DerivedCategory.Plus.ι ⋙
              ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring ⋙
              (sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor) ≅
            (DerivedCategory.Plus.ι ⋙
              ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring ⋙
              P.exceptionalInverseImage s),
          (∀ B : DerivedCategory.Plus
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
            (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.map (α.hom.app B) ≫
                purSupportFiniteExceptionalCounit P s j
                  (by rw [hcomp]; exact isCompl_compl.symm)
                  ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj B.obj) =
              adj.counit.app
                ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj B.obj)) ∧
          (∀ (B : DerivedCategory.Plus
                (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
              (δS : (sfConstantModuleDirectImage j P.Ring).rightDerivedFunctor.obj
                  ((sfConstantModulePullback j P.Ring).mapDerivedCategory.obj
                    ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj B.obj)) ⟶
                ((sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.obj
                  ((sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor.obj
                    ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj
                      B.obj)))⟦(1 : ℤ)⟧)
              (δE : (sfConstantModuleDirectImage j P.Ring).rightDerivedFunctor.obj
                  ((sfConstantModulePullback j P.Ring).mapDerivedCategory.obj
                    ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj B.obj)) ⟶
                ((sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.obj
                  ((P.exceptionalInverseImage s).obj
                    ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj
                      B.obj)))⟦(1 : ℤ)⟧),
            purSupportAdjunctionTriangle s j P.Ring adj
                ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj B.obj) δS ∈
              distTriang (proEtaleDerivedCategory X P.Ring) →
            purSupportExceptionalTriangle P s j hcomp
                ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj B.obj) δE ∈
              distTriang (proEtaleDerivedCategory X P.Ring) →
            ∃ e : purSupportAdjunctionTriangle s j P.Ring adj
                  ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj B.obj) δS ≅
                purSupportExceptionalTriangle P s j hcomp
                  ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj B.obj) δE,
              e.hom.hom₁ =
                  (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.map (α.hom.app B) ∧
                e.hom.hom₂ = 𝟙 _ ∧ e.hom.hom₃ = 𝟙 _ ) := by
  obtain ⟨α, hα⟩ :=
    purSupportLocalizationTriangleExceptionalCounitCore P s j hcomp adj
  refine ⟨α, ⟨hα, ?_⟩, ?_⟩
  · exact purSupportLocalizationTriangleExceptionalTriangleCore P s j hcomp adj α hα
  · intro α' hα'
    exact purSupportLocalizationTriangleExceptionalUniqueCore P s j hcomp adj α α' hα hα'.1

end AlgebraicGeometry.Scheme
end
