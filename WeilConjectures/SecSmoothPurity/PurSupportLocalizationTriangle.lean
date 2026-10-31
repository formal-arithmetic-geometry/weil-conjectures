/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.PurSupportTriangle
public import WeilConjectures.SecSmoothPurity.PurTriangleMeaning
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ClosedFiniteAdjointCounitTransport
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.AlgebraicGeometry.ProEtaleRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.ClosedLocalization
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.SupportComparisonPullbackCoherence

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

/-- Identify the two recorded direct-image presentations using the actual adjunction
transpose of the constant-section map. No new scalar map is chosen.
Source: Stacks 03D6 and the canonical coefficient convention
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportDirectImageIso {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    sfConstantModuleDirectImage f A ≅ proEtaleConstantModuleDirectImage f A := by
  apply eqToIso
  unfold sfConstantModuleDirectImage proEtaleRingModuleDirectImage
    proEtaleConstantModuleDirectImage
  have h : proEtaleRingDirectImageMap f (proEtaleConstantRing T A)
      (proEtaleConstantRing Y A) (sfConstantCoefficientIso f A) =
        proEtaleCoefficientDirectImageMap f A :=
    ((proEtaleSheafAdjunction f CommRingCat).homEquiv _ _).apply_symm_apply _
  rw [h]

/-- The direct-image realization comparison, obtained by deriving the preceding
coefficient identification and the recorded section-normalized realization comparison.
Source: Stacks 00YV and 07A5 (blueprint: lem-pur-support-localization-triangle). -/
def purSupportDerivedDirectImageIso {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    (sfConstantModuleDirectImage f A).rightDerivedFunctor ≅
      (sfIntrinsicDerivedEquivalence Y A).inverse ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence T A).functor :=
  Functor.rightDerivedFunctorNatIso (purSupportDirectImageIso f A) ≪≫
    (Functor.leftUnitor (proEtaleConstantDerivedDirectImage f A)).symm ≪≫
    Functor.isoWhiskerRight (sfIntrinsicDerivedEquivalence Y A).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison f A)

/-- The ordinary etale exceptional adjunction with proper compact support identified
with closed direct image by the canonical proper comparison.
Source: blueprint proof paragraph 2; Stacks 04CA and 0G2C
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportEtaleExceptionalAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s] [HasCompactification s] :
    (Etale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor ⊣
      Etale.rightDerivedUpperShriek A s :=
  (Etale.rightDerivedUpperShriekAdjunction A s).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) s)

/-- The fixed-scalar finite exceptional counit for a closed immersion. Its three factors
are the inverse closed comparison, the transported etale counit, and the comparison
adjunction counit. This is defined without an ambient exceptional adjunction.
Source: blueprint proof paragraph 2 and the closed finite counit transport
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportFixedExceptionalCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X U : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s] [HasCompactification s]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range s.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.obj
      ((ProEtale.rightDerivedUpperShriek A s).obj K) ⟶ K := by
  letI := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl (R := A) s j hPair
  exact
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctorIsoMapDerivedCategory.hom.app
        ((ProEtale.rightDerivedUpperShriek A s).obj K) ≫
      (ProEtale.ClosedFiniteTransport.closedComparison A s j hPair).inv.app _ ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((purSupportEtaleExceptionalAdjunction A s).counit.app _) ≫
      (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app K

/-- The actual closed-support inclusion, obtained by inverting the canonical supported
unit comparison and then taking the kernel inclusion.
Source: blueprint proof paragraph 2; Stacks 09AH
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportSheafCounit {Z X U : Scheme.{u}}
    (s : Z ⟶ X) [IsClosedImmersion s] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range s.base) (Set.range j.base))
    (A : Type u) [CommRing A] [Finite A] :
    sfIntrinsicClosedUpperShriek s j A ⋙ sfConstantModuleDirectImage s A ⟶ 𝟭 _ := by
  letI : IsIso (sfIntrinsicSupportedComparison s j A) :=
    (sfIntrinsicFlasqueSupport A s j hPair).2.2.2.2.1
  exact (asIso (sfIntrinsicSupportedComparison s j A)).inv ≫
    { app M := kernel.ι ((sfConstantModuleAdjunction j A).unit.app M)
      naturality M N f := by simp [sfIntrinsicSectionsWithSupport] }

/-- Right derivation of a sheaf support adjunction, with exact closed direct image
identified with its termwise descent. This fixes the derived counit normalization.
Source: Stacks 07A6; blueprint proof paragraph 2
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportDerivedAdjunction {Z X U : Scheme.{u}}
    (s : Z ⟶ X) (j : U ⟶ X) (A : Type u) [CommRing A] [Finite A]
    (hS : PreservesFiniteColimits (sfConstantModuleDirectImage s A))
    (a0 : sfConstantModuleDirectImage s A ⊣ sfIntrinsicClosedUpperShriek s j A) :
    (sfConstantModuleDirectImage s A).rightDerivedFunctor ⊣
      (sfIntrinsicClosedUpperShriek s j A).rightDerivedFunctor := by
  letI := hS
  letI := (sfConstantModuleAdjunction s A).rightAdjoint_preservesLimits
  exact a0.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
    (sfConstantModuleDirectImage s A).rightDerivedFunctorIsoMapDerivedCategory.symm

/-- The ambient support-adjunction triangle with its prescribed counit and open unit.
The argument is its connecting arrow, not a choice of either adjunction map.
Source: blueprint displayed support triangle, proof paragraphs 1--2
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportAdjunctionTriangle {Z X U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
    (A : Type u) [CommRing A] [Finite A]
    (adj : (sfConstantModuleDirectImage s A).rightDerivedFunctor ⊣
      (sfIntrinsicClosedUpperShriek s j A).rightDerivedFunctor)
    (K : proEtaleDerivedCategory X A)
    (δ : (sfConstantModuleDirectImage j A).rightDerivedFunctor.obj
        ((sfConstantModulePullback j A).mapDerivedCategory.obj K) ⟶
      ((sfConstantModuleDirectImage s A).rightDerivedFunctor.obj
        ((sfIntrinsicClosedUpperShriek s j A).rightDerivedFunctor.obj K))⟦(1 : ℤ)⟧) :
    Triangle (proEtaleDerivedCategory X A) :=
  Triangle.mk (adj.counit.app K)
    ((sfConstantModuleAdjunction j A).mapDerivedCategoryRightDerivedAdjunction.unit.app K) δ

variable (P : PurityFiniteSetting.{u})
variable {Z X : Scheme.{u}}
  [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable (s : Z ⟶ X) [IsClosedImmersion s]

/-- The recorded finite exceptional functor, expressed using the canonical realization
and the existing fixed-scalar finite functor. This only separates the comparison from
module realization; the underlying etale adjoint is unchanged.
Source: def-weil-exceptional-inverse-image, its finite displayed formula
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportFiniteExceptionalModelIso :
    P.exceptionalInverseImage s ≅
      (sfIntrinsicDerivedEquivalence X P.Ring).inverse ⋙
        ProEtale.rightDerivedUpperShriek P.Coefficient s ⋙
          (sfIntrinsicDerivedEquivalence Z P.Ring).functor := by
  letI := (ProEtale.finiteCoefficientIntrinsicRealization_exact Z P.Ring).2.1
  letI := (ProEtale.finiteCoefficientIntrinsicRealization_exact Z P.Ring).2.2.1
  letI := (ProEtale.finiteCoefficientIntrinsicRealization_exact Z P.Ring).2.2.2
  exact Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence X P.Ring).inverse
    (Functor.isoWhiskerLeft
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) X).rightDerivedFunctor
      (Functor.isoWhiskerLeft (Etale.rightDerivedUpperShriek P.Coefficient s)
        (Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z)
          (ProEtale.finiteCoefficientIntrinsicRealization Z P.Ring)))) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence X P.Ring).inverse
      (Functor.isoWhiskerLeft
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) X).rightDerivedFunctor
        (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm)

/-- The canonical finite transported exceptional counit, in the intrinsic coefficient
category of the node. All identifications are the recorded coefficient realization,
closed direct-image comparison, proper comparison and adjunction counits.
Source: blueprint proof paragraph 2, closed finite adjoint counit transport
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportFiniteExceptionalCounit {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range s.base) (Set.range j.base))
    (K : proEtaleDerivedCategory X P.Ring) :
    (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.obj
      ((P.exceptionalInverseImage s).obj K) ⟶ K :=
  (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.map
      ((purSupportFiniteExceptionalModelIso P s).hom.app K) ≫
    (purSupportDerivedDirectImageIso s P.Ring).hom.app _ ≫
    (sfIntrinsicDerivedEquivalence X P.Ring).functor.map
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s).rightDerivedFunctor.map
          ((sfIntrinsicDerivedEquivalence Z P.Ring).unitIso.inv.app _) ≫
        purSupportFixedExceptionalCounit P.Coefficient s j hPair
          ((sfIntrinsicDerivedEquivalence X P.Ring).inverse.obj K)) ≫
    (sfIntrinsicDerivedEquivalence X P.Ring).counitIso.hom.app K

/-- The finite exceptional-adjunction triangle with the actual transported counit
and open unit. Its boundary is supplied explicitly for comparison with the cone model.
Source: blueprint proof paragraph 2, finite etale-origin identification
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportExceptionalTriangle {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
    (K : proEtaleDerivedCategory X P.Ring)
    (δ : (sfConstantModuleDirectImage j P.Ring).rightDerivedFunctor.obj
        ((sfConstantModulePullback j P.Ring).mapDerivedCategory.obj K) ⟶
      ((sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.obj
        ((P.exceptionalInverseImage s).obj K))⟦(1 : ℤ)⟧) :
    Triangle (proEtaleDerivedCategory X P.Ring) :=
  Triangle.mk
    (purSupportFiniteExceptionalCounit P s j
      (by rw [hcomp]; exact isCompl_compl.symm) K)
    ((sfConstantModuleAdjunction j P.Ring).mapDerivedCategoryRightDerivedAdjunction.unit.app K) δ

/-- The etale comparison on exceptional triangles induced by the specified support
construction. The support comparison is extracted from the recorded base-change
predicate; it is not an arbitrary triangle isomorphism. Conjugation by the full-triangle
identifications retains the connecting-arrow square. For the finite triangles these
identifications are the unique counit-compatible ones in `purSupportLocalizationTriangle`.
Source: blueprint proof paragraph 3 and the reviewed finite-domain correction
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportExceptionalEtaleBaseChangeIso
    (A : Type u) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
    (hBC : supportTriangleEtaleBaseChange (s := s) (j := j) (hcomp := hcomp) A)
    {X' Z' U' : Scheme.{u}} (v : X' ⟶ X) (vZ : Z' ⟶ Z) (vU : U' ⟶ U)
    (s' : Z' ⟶ X') (j' : U' ⟶ X') [Etale v] [Etale vU]
    [IsClosedImmersion s'] [IsOpenImmersion j'] [QuasiCompact j']
    (hcomp' : Set.range s'.base = (Set.range j'.base)ᶜ)
    (hs : IsPullback vZ s' s v) (hj : IsPullback vU j' j v)
    (K : CochainComplex.Plus (proEtaleRingModules X (proEtaleConstantRing X A)))
    (r : CochainComplex.KInjectiveResolutionChoice K.obj)
    (hI : ∀ n : ℤ, Injective (r.complex.X n))
    (r' : CochainComplex.KInjectiveResolutionChoice
      ((sfConstantModulePullback v A).mapCochainComplexPlus.obj K).obj)
    (hI' : ∀ n : ℤ, Injective (r'.complex.X n))
    (T : Triangle (proEtaleDerivedCategory X A))
    (T' : Triangle (proEtaleDerivedCategory X' A))
    (e : supportTriangle s j hcomp A K r hI ≅ T)
    (e' : supportTriangle s' j' hcomp' A
      ((sfConstantModulePullback v A).mapCochainComplexPlus.obj K) r' hI' ≅ T') :
    (sfConstantModulePullback v A).mapDerivedCategory.mapTriangle.obj T ≅ T' :=
  ((sfConstantModulePullback v A).mapDerivedCategory.mapTriangle.mapIso e).symm ≪≫
    (hBC v vZ vU s' j' hcomp' hs hj K r hI r' hI').choose_spec.2.choose ≪≫ e'

/-- The ambient support-localization data: the normalized sheaf adjunction, its derived
adjunction, the meaning of the support triangle, bounded-below preservation, and the
specified distinguished support triangles with their counit-compatible comparison.

Source: blueprint `lem-pur-support-localization-triangle`, proof paragraphs 1--3
(DAG steps 1--5) (blueprint: lem-pur-support-localization-triangle-core).

Proof:
1. Grothendieckness gives a K-injective resolution I with injective terms. The intrinsic
support sequence ker(I -> j_*j^*I) -> I -> j_*j^*I is termwise short exact.
2. Ringed closed localization, with the canonical constant-coefficient isomorphisms,
identifies the supported kernel with s_*s_0^!I; closed pushforward is exact and factoring
maps through this kernel gives s_* left adjoint to s_0^! with the support counit. Deriving
on K-injectives gives the normalized derived adjunction and keeps D^+ inputs in D^+. Open
restriction is an exact localization preserving K-injectives, so j_*j^*I computes Rj_*j^*K.
3. The cone quotient (b,a) -> q(b) has kernel Cone(id), contracted by h(x,a)=(0,x), so it is
a quasi-isomorphism; transporting the cone triangle gives the specified distinguished
triangle, identified with the adjunction triangle with middle comparison inverse to r.map.
4. Derived maps are unique homotopy classes between K-injective models; the three additive
functors preserve homotopies, which gives canonicality and functoriality.
5. Etale inverse image is exact restriction to a localized site preserving (K-)injectives
and commuting with the supported kernel and the closed and open direct images, which
gives etale base change, hence `supportTriangleMeaning`.
-/
theorem purSupportLocalizationTriangleCore
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
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ) :
    ∃ hS : PreservesFiniteColimits (sfConstantModuleDirectImage s P.Ring),
      ∃ a0 : sfConstantModuleDirectImage s P.Ring ⊣
          sfIntrinsicClosedUpperShriek s j P.Ring,
        a0.counit = purSupportSheafCounit s j
          (by rw [hcomp]; exact isCompl_compl.symm) P.Ring ∧
      ∃ adj : (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor ⊣
          (sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor,
        adj = purSupportDerivedAdjunction s j P.Ring hS a0 ∧
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
          ∃ δ : (sfConstantModuleDirectImage j P.Ring).rightDerivedFunctor.obj
                ((sfConstantModulePullback j P.Ring).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K.obj)) ⟶
              ((sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.obj
                ((sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor.obj
                  (DerivedCategory.Q.obj K.obj)))⟦(1 : ℤ)⟧,
            ∃ e : supportTriangle s j hcomp P.Ring K r hI ≅
                purSupportAdjunctionTriangle s j P.Ring adj (DerivedCategory.Q.obj K.obj) δ,
              DerivedCategory.Q.map r.map ≫ e.hom.hom₂ = 𝟙 _) := by
  sorry

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
  sorry

/-- The specified intrinsic support triangle is the ambient adjunction triangle. The
finite exceptional identification is a unique natural counit-compatible comparison on
etale-origin inputs, and identifies every distinguished exceptional-adjunction triangle,
including its connecting arrow. Its etale base change is therefore the one induced by
`supportTriangleMeaning`, independent of both resolutions and triangle completions.

Source: blueprint `lem-pur-support-localization-triangle`, proof paragraphs 1--3,
with the finite-domain correction in the reviewed DAG
(blueprint: lem-pur-support-localization-triangle).

Proof:
1. Grothendieckness gives a K-injective resolution I with injective terms. The intrinsic
support sequence has terms ker(I -> j_*j^*I), I, and j_*j^*I and is termwise short exact.
2. Ringed closed localization, with the canonical constant-coefficient isomorphisms,
identifies the supported kernel with s_*s_0^!I. The complement is quasi-compact. Closed
pushforward is exact; factoring maps through this kernel gives s_* left adjoint to
s_0^!. Deriving on K-injectives gives the displayed ambient adjunction. Open restriction
is an exact localization preserving K-injectives, so the third term computes Rj_*j^*K.
The two chain maps induce the actual counit and open adjunction unit.
3. The cone quotient sends (b,a) to q(b). Its kernel is Cone(id_A), with contraction
h(x,a)=(0,x). Thus it is a quasi-isomorphism. Transport the cone triangle by it, with
its fixed signed projection, to obtain precisely the specified distinguished triangle.
4. Every derived map is represented by a unique homotopy class between K-injective
models. Applying the support, identity and open functors gives the three components.
Their naturality and the cone quotient give all three squares, including the boundary.
Additive functors preserve homotopies. Hence this descends, preserves composition, and
compares any two resolutions by inverse derived comparisons.
5. Etale inverse image is exact restriction to a localized site, preserving injectives
and K-injectives. It commutes with the supported kernel and with closed and open direct
image by the canonical localization comparisons, compatibly with their adjunctions.
It also commutes with the cone quotient and signed projection. Comparison with the
new chosen resolution proves the full triangle base-change assertion.
6. For K=nu_X^*B, transport the ordinary etale support triangle by exact nu_X^*. The
closed finite adjoint counit transport identifies its first arrow with the finite
transported exceptional counit defined above. Bounded-below comparison direct-image
isomorphisms identify its open term with Rj_*j^*K.
7. Normalize the latter comparison by transposing the inverse of the restriction of
its second arrow. Open full faithfulness makes it invertible, and the triangle identity
makes the normalized second arrow exactly the open adjunction unit.
8. Rotate, apply triangle-morphism extension with identities on the middle and third
terms, and rotate back. Two-of-three makes the first component invertible. Closed
full faithfulness recovers the isomorphism Rs_supp^!K -> Rs^!K on Z. All triangle
squares hold, including the boundary square; this works for any distinguished triangle
with those fixed exceptional counit and open unit arrows.
9. Hom(s_*P,Rj_*N[r])=0 in every degree by open restriction and its adjunction. Triangle
Hom exactness therefore makes maps from s_*P into the support term uniquely determined
by composition with its counit. The comparison in step 8 is thus unique, natural on
the full bounded-below etale derived category, and independent of all completions.
Etale pullback preserves etale origin and the counit comparisons in step 5, so the same
uniqueness identifies its pullback with the comparison for the base-changed pair.
-/
theorem purSupportLocalizationTriangle
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
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ) :
    ∃ hS : PreservesFiniteColimits (sfConstantModuleDirectImage s P.Ring),
      ∃ a0 : sfConstantModuleDirectImage s P.Ring ⊣
          sfIntrinsicClosedUpperShriek s j P.Ring,
        a0.counit = purSupportSheafCounit s j
          (by rw [hcomp]; exact isCompl_compl.symm) P.Ring ∧
      ∃ adj : (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor ⊣
          (sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor,
        adj = purSupportDerivedAdjunction s j P.Ring hS a0 ∧
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
          ∃ δ : (sfConstantModuleDirectImage j P.Ring).rightDerivedFunctor.obj
                ((sfConstantModulePullback j P.Ring).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K.obj)) ⟶
              ((sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.obj
                ((sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor.obj
                  (DerivedCategory.Q.obj K.obj)))⟦(1 : ℤ)⟧,
            ∃ e : supportTriangle s j hcomp P.Ring K r hI ≅
                purSupportAdjunctionTriangle s j P.Ring adj (DerivedCategory.Q.obj K.obj) δ,
              DerivedCategory.Q.map r.map ≫ e.hom.hom₂ = 𝟙 _) ∧
        (∃! α :
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
                e.hom.hom₂ = 𝟙 _ ∧ e.hom.hom₃ = 𝟙 _)) := by
  obtain ⟨hS, a0, hc, adj, hadj, hmeaning, hplus, hmodels⟩ :=
    purSupportLocalizationTriangleCore P s j hcomp
  exact ⟨hS, a0, hc, adj, hadj, hmeaning, hplus, hmodels,
    purSupportLocalizationTriangleExceptional P s j hcomp adj⟩

end AlgebraicGeometry.Scheme
end
