/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.CoefficientHeartFiltration
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Topology.KrullDimension
import Sheaf.Paper.CoefficientHeartSmall
import Sheaf.Paper.CompletedCondensedCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.Paper.CondensedSurjectiveClosedEquivalence
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CoefficientHeartClosure
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!
# The constructible coefficient heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart,
_section.md and sk-lem-coefficient-heart.proof.md (blueprint: sk-lem-coefficient-heart).

All module categories use the actual condensed coefficient ring pulled back from the point.
Constructibility is the finite constant scalar model predicate, and locally closed extension
is the previously constructed open extension into the scheme-theoretic closure followed by
closed direct image. The assertion predicates below spell out the clauses of the node.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The curve specialization: the actual open counit and complementary closed unit give
its short exact sequence. The closed term restricts to zero on the dense lisse open.
Source: blueprint sk-lem-coefficient-heart, final paragraph
(blueprint: sk-lem-coefficient-heart). -/
def CoefficientHeartCurveAssertions (X : Scheme.{u}) : Prop :=
  topologicalKrullDim X ≤ 1 →
  ∀ F : ConstantModelConstructible Λ X,
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ U.ι).obj F.obj) ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
        Set.range i = (U : Set X)ᶜ ∧
        ((U : Set X)ᶜ).Finite ∧
        (∀ x ∈ (U : Set X)ᶜ, IsClosed ({x} : Set X)) ∧
        Mono ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app
          F.obj) ∧
        Epi ((CondensedRing.upperStarLowerStarAdjunction Λ i).unit.app F.obj) ∧
        (ComposableArrows.mk₂
          ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app F.obj)
          ((CondensedRing.upperStarLowerStarAdjunction Λ i).unit.app F.obj)).Exact ∧
        IsZero ((CondensedRing.upperStar Λ U.ι).obj
          ((CondensedRing.lowerStar Λ i).obj ((CondensedRing.upperStar Λ i).obj F.obj)))

/-- A finite, non-strict filtration of each constructible sheaf by subsheaves, with the
specified locally closed extensions as successive quotients. Zero and empty filtrations
are allowed. Source: blueprint sk-lem-coefficient-heart, clause (3)
(blueprint: sk-lem-coefficient-heart). -/
def CoefficientHeartFiltrationAssertions (X : Scheme.{u}) [IsNoetherian X] : Prop :=
  ∀ F : ConstantModelConstructible Λ X,
    ∃ (m : ℕ) (T : Fin (m + 1) → Subobject F.obj), T 0 = ⊥ ∧ T (Fin.last m) = ⊤ ∧
      ∃ h : ∀ a : Fin m, T a.castSucc ≤ T a.succ,
        ∀ a : Fin m, ∃ (S : Scheme.{u}) (j : S ⟶ X) (hj : IsImmersion j)
          (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
          IsLisseCoefficientModule Λ L ∧
          Nonempty (cokernel (Subobject.ofLE (T a.castSucc) (T a.succ) (h a)) ≅
            (coefficientHeartLocallyClosedExtension Λ j hj).obj L)

/-- Exactness of both factors in extension through the scheme-theoretic closure, exactness
of their composite, and descent by applying this composite termwise to complexes.
Source: blueprint sk-lem-coefficient-heart, introductory locally closed extension paragraph
(blueprint: sk-lem-coefficient-heart). -/
def CoefficientHeartExtensionAssertions (X : Scheme.{u}) [IsNoetherian X] : Prop :=
  ∀ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a),
    letI : IsImmersion a := ha
    letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
    PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ a.toImage) ∧
    PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ a.toImage) ∧
    PreservesFiniteLimits (CondensedRing.lowerStar Λ a.imageι) ∧
    PreservesFiniteColimits (CondensedRing.lowerStar Λ a.imageι) ∧
    PreservesFiniteLimits (coefficientHeartLocallyClosedExtension Λ a ha) ∧
    PreservesFiniteColimits (coefficientHeartLocallyClosedExtension Λ a ha) ∧
    Exists fun [_hadd : (coefficientHeartLocallyClosedExtension Λ a ha).Additive] ↦
    ∃ D : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) ⥤
          DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      Nonempty (DerivedCategory.Q ⋙ D ≅
        (coefficientHeartLocallyClosedExtension Λ a ha).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q)

/-- Every assertion of the constructible-heart node, including its introductory derived
and locally closed extension clauses. Exact descent is characterized by the localization
square with the termwise functor, so no arbitrary derived map is substituted.
Source: blueprint sk-lem-coefficient-heart, introduction, clauses (1)--(3), final paragraph
(blueprint: sk-lem-coefficient-heart). -/
def CoefficientHeartAssertions (X : Scheme.{u}) [IsNoetherian X] : Prop :=
  ((constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _) =
    constantModelBoundedConstructible Λ X) ∧
  (∀ (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) (n : ℤ),
    constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ X ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      constantModelBoundedConstructible Λ X ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
  (∀ F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    IsConstantModelConstructible Λ X F ↔
      ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
        IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (R.immersion a)).obj F)) ∧
  CoefficientHeartExtensionAssertions Λ X ∧
  (∀ (F G : ConstantModelConstructible Λ X) (f : F.obj ⟶ G.obj),
    IsConstantModelConstructible Λ X (kernel f) ∧
      IsConstantModelConstructible Λ X (cokernel f)) ∧
  (∀ (F G : ConstantModelConstructible Λ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : F.obj ⟶ M) (g : M ⟶ G.obj),
    Mono f → Epi g → (ComposableArrows.mk₂ f g).Exact →
      IsConstantModelConstructible Λ X M) ∧
  Nonempty (Abelian (ConstantModelConstructible Λ X)) ∧
  PreservesFiniteLimits (ObjectProperty.ι (IsConstantModelConstructible Λ X)) ∧
  PreservesFiniteColimits (ObjectProperty.ι (IsConstantModelConstructible Λ X)) ∧
  EssentiallySmall.{u + 1} (ConstantModelConstructible Λ X) ∧
  CoefficientHeartFiltrationAssertions Λ X ∧ CoefficientHeartCurveAssertions Λ X

/-- Constructible sheaves over E or Qbar_l form an essentially small abelian heart, with
finite locally closed lisse filtrations and the stated curve localization sequence.
The Noetherian structure used to state the assertion is constructed from the standing
finite-type-over-a-field hypotheses, rather than imposed as an additional assumption.

Source: blueprint sk-lem-coefficient-heart and its proof, all ten steps
(blueprint: sk-lem-coefficient-heart).

Proof plan:
1. The standing finite-type scheme is Noetherian (lem-weil-pbc-finite-type-over-noetherian).
Its open, closed and locally closed subschemes are Noetherian, all opens quasi-compact,
and X quasi-separated. Identify the actual condensed coefficients using
sk-prop-sfb-qlbar-colimit-x; these are not discrete constant field sheaves.
2. The scalar ring is a field. A finite constant presentation is therefore finite free,
and conversely. This gives the finite-stratification lisse criterion. The field case of
det-def-localizing-closure-ctf-equals-bc gives Dctf = Dbc. Truncation only removes cohomology
sheaves or replaces them by zero, so preserves bounded constructibility.
3. Factor an immersion through its scheme-theoretic image using def-nagata-scheme-image-factor.
Restriction to an open in which it is closed identifies this image with S; thus the map to
its image is open (lemma-nagata-scheme-image-restrict-open and -of-closed-immersion).
Use def-sfb-module-open-lower-shriek and lem-weil-pbc-proetale-ringed-open-closed for exactness
of both factors. Their composite preserves quasi-isomorphisms and induces the localization
functor with the displayed termwise comparison, without resolutions.
4. Use det-lem-coefficient-heart-common-stratification for a common adapted stratification
and exact restriction. On each stratum kernels and cokernels are lisse by
det-lem-coefficient-heart-closure, so the criterion in step 2 makes them constructible.
5. Restrict an extension to the same common stratification. Locally lift finitely many basis
sections of its free quotient to split it. Its middle term is finite free. Thus extensions
are constructible. Zero has rank zero; split extensions give finite sums. The ambient kernels
and cokernels now give an abelian full subcategory and exact inclusion, as in the closure node.
6. det-lem-coefficient-heart-small supplies a set of representatives, including the control
of gluing between strata by embeddings into the product of stratum direct images.
7. Order and refine an adapted stratification by det-lem-coefficient-heart-common-stratification.
Apply det-lem-coefficient-heart-filtration to its open prefixes: their counit image subobjects
start at zero and end at F, are nested, and their quotients are the specified a_! of the
lisse restrictions. Equality between successive subobjects is permitted, including F = 0.
8. On a curve choose a generic point of each of its finitely many irreducible components
(lem-weil-pbc-noetherian-finitely-many-components, lem-sc-scheme-sober). Its adapted stratum
contains a neighborhood after other components are removed. Base change this neighborhood
with that stratum. The projection is a surjective immersion, hence closed; this follows from
lem-weil-pbc-immersion-base-change-lft and lem-weil-pbc-fibre-product-points. The other projection
is open, so the pulled-back sheaf is lisse. No factorization through a nonreduced stratum is
inferred just from containment of underlying point sets.
9. Lift the trivializing cover through this surjective closed immersion by
new-lem-weil-pbc-proetale-surjective-closed-cover-refinement. Each base change is a universal
homeomorphism (lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism), and its
coefficient pullback is an equivalence (new-lem-weil-pbc-condensed-surjective-closed-equivalence).
Cartesian coefficients identify free modules. Fullness lifts a trivialization and its inverse;
faithfulness gives their inverse identities. These neighborhoods give a dense lisse open U.
10. Give its complement the reduced induced closed scheme structure
(lem-weil-pbc-reduced-induced-closed-subscheme). It misses every component's generic point,
so a chain of length one in the complement would give length two in X. The complement has
dimension at most zero, is Noetherian and T0, hence consists of finitely many closed points
(lem-sc-zero-dim-noetherian-closed-finite). Apply lem-weil-pbc-proetale-ringed-open-closed with
sk-prop-sfb-cartesian-coefficients. Its actual counit and unit give the short exact sequence;
open restriction of the closed term is zero, giving its support. The argument allows
reducible and nonreduced curves, the empty complement, the zero sheaf and empty X. -/
theorem coefficientHeart (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    @CoefficientHeartAssertions (coefficientHeartRingObj L) _ _ X
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) } := by
  sorry

end AlgebraicGeometry.ProEtale
