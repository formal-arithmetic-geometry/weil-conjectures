/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Injective representatives of resolution roofs and their canonical transposes

Source: blueprint, direct-image stability, paragraph (3), internal bar normalization;
Stacks Project, Tags 070I, 070J, 070Y, 08BJ, 09T5, 0FND and 0A8D.
(blueprint: lem-sfb-resolution-roof-injective-transpose).

The constructions below use the fixed termwise adjunction, exact-localization comparison,
K-injective right-derived unit and canonical shift comparisons. No projectivity is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uB vB uE vE wB wE g u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.ResolutionRoof

variable {B : Type uB} {E : Type uE} [Category.{vB} B] [Category.{vE} E]
  [Abelian B] [Abelian E]
  {L : B ⥤ E} {R : E ⥤ B} [L.Additive] [R.Additive]

/-- The ordinary termwise transpose, identifying L(X[0]) with (LX)[0] by the canonical
single-complex comparison. Source: Stacks Tag 08BJ; blueprint paragraph (3)
(blueprint: lem-sfb-resolution-roof-injective-transpose). -/
def termwiseTranspose (adj : L ⊣ R) (X : B) (I : CochainComplex E ℤ) (q : ℤ)
    (h : (CochainComplex.singleFunctor E 0).obj (L.obj X) ⟶ I⟦q⟧) :
    (CochainComplex.singleFunctor B 0).obj X ⟶ (R.mapHomologicalComplex (.up ℤ)).obj (I⟦q⟧) :=
  (adj.mapHomologicalComplex (.up ℤ)).homEquiv _ _
    ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app X ≫ h)

/-- Shift the termwise transpose back by q and cancel the two target shifts. In degree q
this is the original degree-zero transpose; shifts of morphisms add no sign.
Source: Stacks Tag 08BJ and the canonical shift convention, blueprint paragraph (3)
(blueprint: lem-sfb-resolution-roof-injective-transpose). -/
def transposeFlat (adj : L ⊣ R) (X : B) (I : CochainComplex E ℤ) (q : ℤ)
    (h : (CochainComplex.singleFunctor E 0).obj (L.obj X) ⟶ I⟦q⟧) :
    ((CochainComplex.singleFunctor B 0).obj X)⟦-q⟧ ⟶
      (R.mapHomologicalComplex (.up ℤ)).obj I :=
  (termwiseTranspose adj X I q h)⟦-q⟧' ≫
    (((R.mapHomologicalComplex (.up ℤ)).commShiftIso q).hom.app I)⟦-q⟧' ≫
      (shiftShiftNeg ((R.mapHomologicalComplex (.up ℤ)).obj I) q).hom

variable [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wE} E]
  [IsGrothendieckAbelian.{g} E]

/-- The roof Q(e) inverse followed by Q(u).
Source: Stacks Tag 070I, blueprint paragraph (3)
(blueprint: lem-sfb-resolution-roof-injective-transpose). -/
def roof {P T N : CochainComplex E ℤ} (e : P ⟶ T) [QuasiIso e] (f : P ⟶ N) :
    DerivedCategory.Q.obj T ⟶ DerivedCategory.Q.obj N :=
  inv (DerivedCategory.Q.map e) ≫ DerivedCategory.Q.map f

/-- The augmentation-normalized comparison beta_a: Q(RI) to RR(QN).
Source: Stacks Tag 070Y, blueprint paragraph (3)
(blueprint: lem-sfb-resolution-roof-injective-transpose). -/
def resolutionComparison (R : E ⥤ B) [R.Additive]
    {N I : CochainComplex E ℤ} (a : N ⟶ I) [QuasiIso a] :
    DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      R.rightDerivedFunctor.obj (DerivedCategory.Q.obj N) :=
  R.rightDerivedFunctorUnitQ I ≫ inv (R.rightDerivedFunctor.map (DerivedCategory.Q.map a))

variable [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- Phi_q is the canonical derived Hom adjunction followed by its fixed shift comparison.
The comparison for L first identifies D(L)(Q(X[0])) with Q((LX)[0]).
Source: Stacks Tags 09T5, 0FND and 0A8D, blueprint paragraph (3)
(blueprint: lem-sfb-resolution-roof-injective-transpose). -/
def shiftedDerivedTranspose (adj : L ⊣ R) (X : B) (N : E) (q : ℤ)
    (f : DerivedCategory.Q.obj ((CochainComplex.singleFunctor E 0).obj (L.obj X)) ⟶
      DerivedCategory.Q.obj (((CochainComplex.singleFunctor E 0).obj N)⟦q⟧)) :
    DerivedCategory.Q.obj (((CochainComplex.singleFunctor B 0).obj X)⟦-q⟧) ⟶
      R.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor E 0).obj N)) :=
  (DerivedCategory.Q.commShiftIso (-q)).hom.app _ ≫
    ((adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
      (L.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app X) ≫ f)) ≫
      R.rightDerivedFunctor.map ((DerivedCategory.Q.commShiftIso q).hom.app _) ≫
      (R.rightDerivedFunctor.commShiftIso q).hom.app _)⟦-q⟧' ≫
    (shiftShiftNeg (R.rightDerivedFunctor.obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor E 0).obj N))) q).hom

/-- A roof into N[q] has an injective representative, and every representative has the
canonical shifted derived transpose, for every specified injective resolution.
Source: Stacks Tags 070I, 070J, 070Y, 08BJ, 09T5, 0FND and 0A8D; blueprint paragraph (3)
(blueprint: lem-sfb-resolution-roof-injective-transpose).

Proof: (1) I[q] is bounded below and termwise injective, hence K-injective by
lem-weil-pbc-bounded-below-injectives-kinjective. The surjective Hom comparison of
lem-weil-pbc-kinjective-hom-derived supplies h representing Q(a[q]) Q(u) Q(e) inverse.
Its injectivity with arbitrary source P gives the required homotopy; no P term is assumed
projective. (2) Transpose h by lem-weil-pbc-termwise-adjunction-homotopy. Its degree-zero
component is R(h^0) eta_X; the chain condition and cancellation of the shift sign give the
same component as a map X[-q] to RI. (3) Grothendieck K-injective resolutions and exactness
of L give the canonical derived adjunction. The normalized adjunction theorem
lem-sfb-resolving-derived-adjunction-normalization identifies its value on Qh with the
localized termwise transpose followed by the right-derived comparison. (4) Naturality
in the augmentation and inversion of RR(Qa[q]) give the specified resolution comparison.
(5) lem-sp-canonical-right-derived-adjunction-shift identifies this equality after shifting
back by q with the displayed equality, using the fixed K-injective shift and no scalar.
(6) The internal-action specialization uses exact trivial inflation and its normalized
invariants adjunction from lem-sfb-condensed-derived-restriction-calculus. Its transpose is
exactly the unique factorization through the invariant inclusion, as stated below. -/
theorem injectiveTranspose (adj : L ⊣ R) (X : B) (N : E)
    (P : CochainComplex E ℤ) [P.IsStrictlyLE 0]
    (e : P ⟶ (CochainComplex.singleFunctor E 0).obj (L.obj X)) [QuasiIso e]
    (I : InjectiveResolution N) (q : ℤ) (hq : 0 ≤ q)
    (f : P ⟶ ((CochainComplex.singleFunctor E 0).obj N)⟦q⟧) :
    (∃ h : (CochainComplex.singleFunctor E 0).obj (L.obj X) ⟶ I.cochainComplex⟦q⟧,
      Nonempty (Homotopy (e ≫ h) (f ≫ I.ι'⟦q⟧')) ∧
      DerivedCategory.Q.map h = roof e f ≫ DerivedCategory.Q.map (I.ι'⟦q⟧')) ∧
    (∀ h : (CochainComplex.singleFunctor E 0).obj (L.obj X) ⟶ I.cochainComplex⟦q⟧,
      Nonempty (Homotopy (e ≫ h) (f ≫ I.ι'⟦q⟧')) →
      DerivedCategory.Q.map (transposeFlat adj X I.cochainComplex q h) ≫
          resolutionComparison R I.ι' = shiftedDerivedTranspose adj X N q (roof e f)) := by
  sorry

end CategoryTheory.ResolutionRoof

namespace CategoryTheory.ResolutionRoof

open CategoryTheory.CondensedBar
open CategoryTheory.CondensedDerivedRestriction

/-- For internal actions the termwise transpose is the unique factorization through the
invariant inclusion, in every degree of the specified shifted injective resolution.
Source: blueprint direct-image stability paragraph (3), normalized invariants adjunction
(blueprint: lem-sfb-resolution-roof-injective-transpose).

Proof: step 6 of the node. Evaluate the termwise adjunction in each degree and use
Invariants.transpose to identify composition with the inclusion with the underlying h.
Any other factorization has the same section maps since the inclusion is injective on
all sections. Faithfulness of the internal-module/section-module equivalence gives equality
of components, and componentwise extensionality gives equality of cochain maps. This
requires no projectivity and applies to every h from the preceding theorem. -/
theorem internalTransposeFactorization
    (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : CondensedBar.Modules A) (N : Equivariant A G)
    (I : InjectiveResolution N) (q : ℤ) (hq : 0 ≤ q)
    (h : (CochainComplex.singleFunctor (Equivariant A G) 0).obj
      ((Profinite.CondensedAction.trivial (R := A.toMon) (P := G)).obj X) ⟶
        I.cochainComplex⟦q⟧) :
    (∀ i : ℤ,
      (termwiseTranspose (invariants A G).adjunction X I.cochainComplex q h).f i ≫
          (invariants A G).inclusion.app ((I.cochainComplex⟦q⟧).X i) =
        (((HomologicalComplex.singleMapHomologicalComplex
          (Profinite.CondensedAction.trivial (R := A.toMon) (P := G)) (.up ℤ) 0).hom.app X ≫
          h).f i).val) ∧
    (∀ k : (CochainComplex.singleFunctor (CondensedBar.Modules A) 0).obj X ⟶
        ((invariants A G).functor.mapHomologicalComplex (.up ℤ)).obj (I.cochainComplex⟦q⟧),
      (∀ i : ℤ, k.f i ≫ (invariants A G).inclusion.app ((I.cochainComplex⟦q⟧).X i) =
        (((HomologicalComplex.singleMapHomologicalComplex
          (Profinite.CondensedAction.trivial (R := A.toMon) (P := G)) (.up ℤ) 0).hom.app X ≫
          h).f i).val) →
      k = termwiseTranspose (invariants A G).adjunction X I.cochainComplex q h) := by
  sorry

end CategoryTheory.ResolutionRoof
