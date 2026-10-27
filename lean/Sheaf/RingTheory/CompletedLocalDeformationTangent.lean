module

public import Sheaf.RingTheory.CompletedLocalDeformationObjects
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.AdicCompletionFlatDeformationFunctor
import Sheaf.RingTheory.CompletedPolynomialLiftCalculus
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.FiniteModuleComplete
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! # Completion and continuous first-order deformation classes

Source: Stacks Project, examples-defos.tex, Tag 0DYV; defos.tex, Tags 0GPU and 0GPW;
restricted.tex, Tags 0AJR and 0GAE, with the continuous localized-presentation argument
in the node (blueprint: lem-sfb-completed-local-deformation-tangent).

The comparison is specified on all relation maps. In particular its tangent arrow
is the extension of scalars characterized by the natural two-term boundary, rather
than an unspecified linear map between isomorphic vector spaces.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.ArtinDeformation
open scoped ChangeOfRings TensorProduct ModuleCat

namespace Algebra.FlatDeformation

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
variable [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u + 1} (ModuleCat.{u} (localCompletion A))]

/-- The continuous conormal model of a completed localized-polynomial presentation.
The conormal identification and the differential identification are fixed on generators.
The completed derivation is continuous and agrees with the polynomial derivation on
all dense representatives. Its induced conormal boundary is exactly the tensor boundary.
Source: Stacks, Tags 0AJR, 0GAE, 00MA and 0GPU
(blueprint: lem-sfb-completed-local-deformation-tangent). -/
structure ContinuousPresentationModel
    (P : CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) where
  quotient : completedPresentationRing (k := k) P →ₐ[k] localCompletion A
  surjective : Function.Surjective quotient
  canonical : IsCompletionMap
    ((IsLocalRing.maximalIdeal A).comap P.augmentation.hom) (IsLocalRing.maximalIdeal A)
    P.augmentation.hom quotient.toRingHom
  conormalIso : (ModuleCat.extendScalars (algebraMap A (localCompletion A))).obj
    (CotangentResolution.Naive.conormal P) ≅
      ModuleCat.of (localCompletion A) (Extension.ofSurjective quotient surjective).Cotangent
  differentialIso : (ModuleCat.extendScalars (algebraMap A (localCompletion A))).obj
    (CotangentResolution.Naive.differentials P) ≅
      (ModuleCat.extendScalars quotient.toRingHom).obj (completedPresentationDifferentials (k
      := k) P)
  derivation : Derivation k (completedPresentationRing (k := k) P)
      (completedPresentationDifferentials (k := k) P)
  derivation_dense : ∀ x : P.ring,
    derivation (algebraMap P.ring (completedPresentationRing (k := k) P) x) = completedDx (k :=
      k) P x
  derivation_continuous : ∀ n : ℕ, ∃ N : ℕ,
    ∀ x ∈ (((IsLocalRing.maximalIdeal A).comap P.augmentation.hom).map
      (algebraMap P.ring (completedPresentationRing (k := k) P))) ^ N,
      derivation x ∈
        ((((IsLocalRing.maximalIdeal A).comap P.augmentation.hom).map
          (algebraMap P.ring (completedPresentationRing (k := k) P))) ^ n •
            (⊤ : Submodule (completedPresentationRing (k := k) P)
      (completedPresentationDifferentials (k := k) P)))
  conormal_dense : ∀ (j : RingHom.ker P.augmentation.hom)
    (j' : (Extension.ofSurjective quotient surjective).ker),
    (j'.val : completedPresentationRing (k := k) P) = algebraMap P.ring
      (completedPresentationRing (k := k) P) j →
      conormalIso.hom ((1 : localCompletion A) ⊗ₜ[A,algebraMap A (localCompletion A)]
        CotangentResolution.Naive.kernelClass P j) = Extension.Cotangent.mk j'
  differential_dense : ∀ (b : localCompletion A) (a : A) (x : P.ring),
    differentialIso.hom
      (b ⊗ₜ[A,algebraMap A (localCompletion A)]
        CotangentResolution.Naive.tensorGenerator P a x) =
      (b * algebraMap A (localCompletion A) a) ⊗ₜ[completedPresentationRing (k := k)
      P,quotient.toRingHom]
        completedDx (k := k) P x
  boundary_formula : ∀ j : (Extension.ofSurjective quotient surjective).ker,
    (conormalIso.inv ≫ completedDifferential P ≫ differentialIso.hom)
      (Extension.Cotangent.mk j) =
        (1 : localCompletion A) ⊗ₜ[completedPresentationRing (k := k) P,quotient.toRingHom]
      derivation j.val

/-- All clauses of the local completion and tangent comparison. The functor is
canonical on every finite quotient, is compatible with all Artinian base changes,
and takes values in the complete Noetherian local deformation groupoid. Presentation
comparisons obey identity and cocycle coherence and agree with every presentation lift.
The relation-map normalization fixes both tangent identifications and their origins.
Source: Stacks, Tags 0DYV, 0GPU, 0GPW, 0AJR and 0GAE
(blueprint: lem-sfb-completed-local-deformation-tangent). -/
structure CompletedLocalComparison where
  completion : ∀ R : TestCategory k k,
    Groupoid A R ⥤ ContinuousGroupoid (localCompletion A) R
  completionIso : ∀ (R : TestCategory k k) (Q : Groupoid A R),
    algebra ((completion R).obj Q).obj ≃ₐ[k]
      AdicCompletion (ideal (IsLocalRing.maximalIdeal A) Q) (algebra Q)
  completion_scalar : ∀ (R : TestCategory k k) (Q : Groupoid A R) (r : ring R),
    completionIso R Q (scalar ((completion R).obj Q).obj r) =
      algebraMap (algebra Q) _ (scalar Q r)
  completion_marking : ∀ (R : TestCategory k k) (Q : Groupoid A R),
    IsCompletionMap (ideal (IsLocalRing.maximalIdeal A) Q) (IsLocalRing.maximalIdeal A)
      (marking Q).toRingHom
      ((marking ((completion R).obj Q).obj).toRingHom.comp
        (completionIso R Q).symm.toRingHom)
  completion_arrow : ∀ (R : TestCategory k k) (Q Q' : Groupoid A R) (f : Q ⟶ Q'),
    IsCompletionMap (ideal (IsLocalRing.maximalIdeal A) Q)
      (ideal (IsLocalRing.maximalIdeal A) Q') (hom f).toRingHom
      ((completionIso R Q').toRingHom.comp
        ((hom ((completion R).map f).hom).toRingHom.comp (completionIso R Q).symm.toRingHom))
  completion_flat : ∀ (R : TestCategory k k) (Q : Groupoid A R),
    ((algebraMap (algebra Q)
      (AdicCompletion (ideal (IsLocalRing.maximalIdeal A) Q) (algebra Q))).comp
        (scalar Q).toRingHom).Flat
  base_change_exists : ∀ (R R' : TestCategory k k) (f : R ⟶ R') (Q : Groupoid A R),
    ∃ (Q' : Groupoid A R') (i : algebra Q →ₐ[k] algebra Q'), IsBaseChange f Q Q' i
  base_change : ∀ (R R' : TestCategory k k) (f : R ⟶ R')
    (Q : Groupoid A R) (Q' : Groupoid A R') (i : algebra Q →ₐ[k] algebra Q'),
    IsBaseChange f Q Q' i →
      ∃! j : algebra ((completion R).obj Q).obj →ₐ[k]
        algebra ((completion R').obj Q').obj,
        IsBaseChange f ((completion R).obj Q).obj ((completion R').obj Q').obj j ∧
        IsCompletionMap (ideal (IsLocalRing.maximalIdeal A) Q)
          (ideal (IsLocalRing.maximalIdeal A) Q') i.toRingHom
          ((completionIso R' Q').toRingHom.comp
            (j.toRingHom.comp (completionIso R Q).symm.toRingHom))
  algebraicAdd : AddCommGroup (FirstOrderClasses (k := k) A)
  algebraicModule : Module k (FirstOrderClasses (k := k) A)
  continuousAdd : AddCommGroup (ContinuousClasses (k := k) (localCompletion A))
  continuousModule : Module k (ContinuousClasses (k := k) (localCompletion A))
  algebraicTangent : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))), IsFinitePolynomial P →
      FirstOrderClasses (k := k) A ≃ₗ[k] TangentHom P
  continuousTangent : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))), IsFinitePolynomial P →
      ContinuousClasses (k := k) (localCompletion A) ≃ₗ[k] CompletedTangentHom P
  algebraic_relations : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))), IsFinitePolynomial P →
      ∀ Q : Groupoid A (dualTest k),
        ∃ φ : CotangentResolution.Naive.conormal P ⟶ ModuleCat.of A A, IsRelationMap P Q φ
  continuous_relations : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))), IsFinitePolynomial P →
      ∀ Q : ContinuousGroupoid (localCompletion A) (dualTest k),
        ∃ φ : (ModuleCat.extendScalars (algebraMap A (localCompletion A))).obj
          (CotangentResolution.Naive.conormal P) ⟶
            ModuleCat.of (localCompletion A) (localCompletion A),
          IsCompletedRelationMap P Q.obj φ
  algebraic_normalization : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) (hP : IsFinitePolynomial P)
    (Q : Groupoid A (dualTest k))
    (φ : CotangentResolution.Naive.conormal P ⟶ ModuleCat.of A A),
    IsRelationMap P Q φ → algebraicTangent P hP (Quotient.mk _ Q) =
      DerivedCategory.twoTermBoundary (A := ModuleCat.{u} A)
        (CotangentResolution.Naive.differential P)
        (ModuleCat.of A A) φ
  continuous_normalization : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) (hP : IsFinitePolynomial P)
    (Q : ContinuousGroupoid (localCompletion A) (dualTest k))
    (φ : (ModuleCat.extendScalars (algebraMap A (localCompletion A))).obj
      (CotangentResolution.Naive.conormal P) ⟶
        ModuleCat.of (localCompletion A) (localCompletion A)),
    IsCompletedRelationMap P Q.obj φ → continuousTangent P hP (Quotient.mk _ Q) =
      DerivedCategory.twoTermBoundary (completedDifferential P)
        (ModuleCat.of (localCompletion A) (localCompletion A)) φ
  algebraic_origin : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) (hP : IsFinitePolynomial P)
    (Q : Groupoid A (dualTest k)),
    (∃ s : A →ₐ[k] algebra Q, (marking Q).comp s = AlgHom.id k A) →
      algebraicTangent P hP (Quotient.mk _ Q) = 0
  continuous_origin : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) (hP : IsFinitePolynomial P)
    (Q : ContinuousGroupoid (localCompletion A) (dualTest k)),
    (∃ s : localCompletion A →ₐ[k] algebra Q.obj,
      (marking Q.obj).comp s = AlgHom.id k (localCompletion A)) →
        continuousTangent P hP (Quotient.mk _ Q) = 0
  scalarExtension : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))), IsFinitePolynomial P →
      TangentHom P →ₗ[k] CompletedTangentHom P
  extended_relations : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A))))
    (φ : CotangentResolution.Naive.conormal P ⟶ ModuleCat.of A A),
    ∃ ψ : (ModuleCat.extendScalars (algebraMap A (localCompletion A))).obj
      (CotangentResolution.Naive.conormal P) ⟶
        ModuleCat.of (localCompletion A) (localCompletion A), IsExtendedRelationMap P φ ψ
  scalarExtension_boundary : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) (hP : IsFinitePolynomial P)
    (φ : CotangentResolution.Naive.conormal P ⟶ ModuleCat.of A A)
    (ψ : (ModuleCat.extendScalars (algebraMap A (localCompletion A))).obj
      (CotangentResolution.Naive.conormal P) ⟶
        ModuleCat.of (localCompletion A) (localCompletion A)),
    IsExtendedRelationMap P φ ψ →
      scalarExtension P hP (DerivedCategory.twoTermBoundary (A := ModuleCat.{u} A)
        (CotangentResolution.Naive.differential P) (ModuleCat.of A A) φ) =
      DerivedCategory.twoTermBoundary (completedDifferential P)
        (ModuleCat.of (localCompletion A) (localCompletion A)) ψ
  completion_tangent : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) (hP : IsFinitePolynomial P)
    (Q : Groupoid A (dualTest k)),
    continuousTangent P hP (Quotient.mk _ ((completion (dualTest k)).obj Q)) =
      scalarExtension P hP (algebraicTangent P hP (Quotient.mk _ Q))
  continuous_presentation : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))), IsFinitePolynomial P →
      Nonempty (ContinuousPresentationModel P)
  algebraicIndependence : ∀ (P P' : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))),
    IsFinitePolynomial P → IsFinitePolynomial P' →
      ((DerivedCategory.Q (C := ModuleCat.{u} A)).obj (conormalComplex P) ≅
        (DerivedCategory.Q (C := ModuleCat.{u} A)).obj (conormalComplex P'))
  completedIndependence : ∀ (P P' : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))),
    IsFinitePolynomial P → IsFinitePolynomial P' →
      (DerivedCategory.Q.obj (completedConormalComplex P) ≅
        DerivedCategory.Q.obj (completedConormalComplex P'))
  independence_normalization : ∀ (P P' : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A))))
    (hP : IsFinitePolynomial P) (hP' : IsFinitePolynomial P')
    (h : CotangentResolution.Naive.PresentationMap (𝟙 _) P P'),
    Nonempty (ConormalSquare h) ∧ ∀ s : ConormalSquare h,
      (algebraicIndependence P P' hP hP').hom = (DerivedCategory.Q (C := ModuleCat.{u} A)).map
      s.chainMap ∧
      (completedIndependence P P' hP hP').hom = DerivedCategory.Q.map s.completedChainMap
  independence_identity : ∀ (P : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A)))) (hP : IsFinitePolynomial P),
    algebraicIndependence P P hP hP = Iso.refl _ ∧
      completedIndependence P P hP hP = Iso.refl _
  independence_cocycle : ∀ (P P' P'' : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A))))
    (hP : IsFinitePolynomial P) (hP' : IsFinitePolynomial P') (hP'' : IsFinitePolynomial P''),
    algebraicIndependence P P'' hP hP'' =
      algebraicIndependence P P' hP hP' ≪≫ algebraicIndependence P' P'' hP' hP'' ∧
    completedIndependence P P'' hP hP'' =
      completedIndependence P P' hP hP' ≪≫ completedIndependence P' P'' hP' hP''
  algebraic_presentation_compatibility : ∀ (P P' : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A))))
    (hP : IsFinitePolynomial P) (hP' : IsFinitePolynomial P')
    (Q : Groupoid A (dualTest k)),
    algebraicTangent P hP (Quotient.mk _ Q) =
      (algebraicIndependence P P' hP hP').hom ≫ algebraicTangent P' hP' (Quotient.mk _ Q)
  continuous_presentation_compatibility : ∀ (P P' : CotangentResolution.Naive.Presentation
    (Arrow.mk (CommRingCat.ofHom (algebraMap k A))))
    (hP : IsFinitePolynomial P) (hP' : IsFinitePolynomial P')
    (Q : ContinuousGroupoid (localCompletion A) (dualTest k)),
    continuousTangent P hP (Quotient.mk _ Q) =
      (completedIndependence P P' hP hP').hom ≫ continuousTangent P' hP' (Quotient.mk _ Q)

/-- Completion is natural on local algebra deformations; continuous tangent classes
are computed by the completed conormal complex, and its tangent map is scalar extension.
No restriction is made on the residue extension of A over k.
Source: Stacks, Tags 0DYV, 0GPU, 0GPW, 0AJR and 0GAE, and Tag 00MB
(blueprint: lem-sfb-completed-local-deformation-tangent).

Proof:
1. Finite type and localization imply Noetherianity. The Artinian maximal ideal is
nilpotent, so a deformation Q is local, with maximal ideal the inverse image of m.
Apply lem-sfb-adic-completion-flat-deformation-functor and the local-completion theorem
to obtain the functor, its flatness, marked reduction, and every base-change comparison.
2. Use lem-trf-lci-naive-cotangent-model to compare all localized presentations with
truncation of the cotangent complex. Complete finite-module exact sequences for J and
J squared. The finite-module tensor comparison identifies completed conormal modules
and differentials, and lem-sfb-completed-polynomial-lift-calculus extends the derivation.
Flatness of completion preserves the presentation quasi-isomorphisms and their coherence.
3. For a flat dual-number deformation, multiplication by epsilon identifies its kernel
with the special fibre. Conversely a square-zero self-extension is a flat dual-number
algebra: lift a basis of the special fibre and use it and its epsilon multiples to
prove freeness. For complete special fibre, the adic deformation theorem implies the
extension is already complete Noetherian local, and marked isomorphisms are continuous.
4. Apply lem-sfb-two-term-derived-hom-boundary. The boundary from conormal Hom is onto
because the differential term is finite free, so its positive Ext groups vanish.
Its kernel consists precisely of maps factoring through the conormal differential.
5. Lift the polynomial variables to a deformation, and extend continuously in the
completed case, by the polynomial-lift calculus. Restrict a lift to J to obtain a
relation map. Differences of lifts are derivations and change the relation map by a
map factoring through differentials. Conversely quotient the split square-zero algebra
P plus A by the graph (j,-phi(j)). Its kernel is A and its relation map is phi.
Changing phi by a derivation gives an isomorphic extension and accounts for all marked
isomorphisms. These constructions give the normalized tangent bijections.
6. Fibre product of extensions followed by pushout along addition adds relation maps;
pushout along multiplication by a scalar scales them. The split extension has zero
relation map. Thus the normalized identifications are k-linear with the stated origin.
7. Complete the finite-module extension sequence. The completed relation map sends
b tensor [j] to b phi([j]). The two-term boundary is natural in these maps. Since
completion is flat, termwise tensor induces the derived extension-of-scalars functor;
it sends the quotient map q and phi[1] to their completed counterparts. Hence the
boundary characterization gives exactly that functor's tangent map and the displayed
compatibility. This uses no residue-field section or separability assumption. -/
theorem completedLocal_deformation_tangent
    (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (m : Ideal B) [m.IsMaximal] [Algebra B A] [IsScalarTower k B A]
    [IsLocalization.AtPrime A m] :
    ∃ _ : IsNoetherianRing A, Nonempty (CompletedLocalComparison (k := k) (A := A)) := by
  sorry

end Algebra.FlatDeformation
