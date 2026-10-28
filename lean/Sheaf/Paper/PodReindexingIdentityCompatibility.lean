/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.PodCompletionReindexCoherence

/-! # Compatibility of normalized ordinary reindexing

Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The identity relabelling commutes with reduction, total limit and completed tensor.
Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941
(blueprint: lem-pod-reindexing-identity-compatibility).

Proof: first evaluate the section-normalized identity on complexes degree by degree.
For each positive coefficient quotient the identity comparison and its inverse are
restriction along the identity site isomorphism. The quotient-generator formula
therefore makes the quotient chain map the identity under these identifications.
For a whole strict system of complexes the restricted-generator formula identifies
its comparison with the identity-system comparison, including every transition.
The product comparison is fixed by its projections. Both Roos-coordinate formulas
then identify the Roos comparison with the identity on the complete cone of 1-s;
this is an equality of chain maps, not merely of their cohomology or projections.
The K-injective normalization of sourceRoos and targetRoos identifies their
comparisons on resolutions; naturality extends this identification to every system.
Substitute these equalities into LimitModel and cancel the model isomorphisms.
Localization of the section identity and the strict-system identity yields the
limit equation in A.Identity on every system. Under the reduction/limit adjunction,
Unit and Counit identify the reduction map as the mate of this limit map. The
triangle identities give the reduction equation, on all ambient derived objects.
Finally apply the tensor Model equality to flat-term K-flat representatives of both
constructible inputs. Generators identifies the strict tensor map with the identity
on each homogeneous pure tensor; these generate each summand before sheafification.
Both Roos coordinates and the normalized comparison then give the tensor identity
after localization. Naturality transports it along the representative isomorphisms
to the original inputs. This includes zero complexes and the empty site. -/
theorem podReindexingIdentityCompatibility
    (A : PodReindexFamily l E)
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (A.completion f))
    (htensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (A.completion f) (A.tensor f))
    (hidentity : ∀ (W : Scheme.{u}) (M : scalarReductionSource l E W) (U : W.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))),
      ((A.identity W).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
          (𝟙 W) rfl).hom.app U).op x) :
    A.Identity l E := by sorry

end WeilConjectures
