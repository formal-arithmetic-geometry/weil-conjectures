/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartIIStatement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.HomColimitExtension
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.ProperBaseChange.CondensedFiniteFreeTensorExact
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenExtensionProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructureAux
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedComplexDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCouple
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Continuity of Ext from constructible complexes

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-ext-continuity/
`sk-lem-constructible-ext-continuity/_section.md`, entire statement including clauses (1) and (2).
(blueprint: sk-lem-constructible-ext-continuity)

The theorem below records the full natural comparison for a filtered diagram of complexes,
together with the field-coefficient constructible and integral finite-extension clauses.
The comparison is expressed by `extContinuityComparison`, whose colimit cocone is the
termwise colimit cocone and whose legs are postcomposition by the shifted cocone maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Continuity of Ext out of a constructible complex.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-ext-continuity/
`sk-lem-constructible-ext-continuity/_section.md`, entire unit statement and clauses (1)--(2).
(blueprint: sk-lem-constructible-ext-continuity)

The first conjunct is the displayed comparison for a complex obtained by finite extensions
and shifts of locally closed lisse finite locally free sheaves. The second supplies the generator
hypothesis for every bounded constructible field-coefficient complex and states the degree-zero
Ext specialization. The third is the integral finite-extension-of-sheaves clause.

Proof, following the eight steps of the node:
1. Fix the filtered diagram. Hom out of a distinguished triangle gives long exact sequences.
   Filtered colimits in abelian groups are exact, so the five lemma gives extension closure
   of the all-degree comparison locus. A source shift reindexes the target degree; source
   isomorphisms preserve the comparison. Reduce to a locally closed extension of a lisse L.
2. Finite type over the field makes X Noetherian. Locally closed strata, the closed image Z,
   its open stratum S and the complementary open V are qcqs; the open immersions are qcqs.
3. In the factorization a = i u, put F = L-dual tensor u* i*. Finite local freeness makes
   the dual finite locally free and its tensor functor exact and colimit preserving.
   Both restrictions are exact left adjoints. Hence F preserves colimits and the common
   lower bound, and induces a triangulated functor commuting with cohomology.
4. The closed-support stratum formula identifies derived Hom with derived sections on S
   of L-dual tensor u* R-support(K). Apply F and then derived sections to the natural
   fibre triangle of K -> Rj*j*K. The cohomology long exact sequence, exact filtered
   colimits and five lemma reduce the support comparison to the other two terms.
5. Bounded continuity on the qcqs S handles the first term F(K), retaining the same
   termwise bound and the actual colimit cocone.
6. For the second term F(Rj*j*K), bounded-below injective resolutions and exactness of F
   give the natural hypercohomology spectral sequence with entries
   H^a(S,F(H^r(Rj*j*K))). The common lower bound is retained.
7. Bounded continuity for j and then for S identifies the E2 entries under filtered
   colimit. Exactness transports kernels, images, later pages and their finite filtrations.
   In total degree n only 0 <= a <= n-b occurs. Uniform stabilization and induction on
   the finite abutment filtration give the second-term comparison. Steps 4 and 1 finish.
8. For field coefficients use coefficientHeartIIStatement and rotate each cone triangle
   to turn finite cone constructions into finite extensions of shifted generators.
   Apply the main assertion to diagrams of degree-zero sheaves with lower bound zero;
   their colimit remains in degree zero and gives the displayed Ext comparison.
   For integral coefficients each short exact sequence of the finite sheaf extension
   becomes a triangle of degree-zero complexes. Its finite extension expression uses
   only shift zero, which is included among all integer shifts. The explicit subobject
   filtration in the third conjunct has zero initial term, total final term and lisse
   locally closed extension quotients, including the length-zero filtration of zero.
-/
theorem constructible_ext_continuity_statement
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (k : Type u) [Field k] (_hchar : ringChar k ≠ ell)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (_hR : R = Profinite.padicSubfieldCondensedRing ell E ∨
      R = Profinite.padicAlgClCondensedRing ell ∨
      R = Profinite.padicIntegersCondensedRing ell E) :
    (∀ (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj R) X))),
      IsExtContinuityGenerated (coefficientHeartRingObj R) X Set.univ M →
      ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
        (K : I ⥤ CochainComplex
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (coefficientHeartRingObj R) X)) ℤ) (b : ℤ),
        (∀ (i : I) (r : ℤ), r < b → IsZero ((K.obj i).X r)) →
        ∀ n : ℤ, IsIso (extContinuityComparison M K (colimit.cocone K) n)) ∧
    ((R = Profinite.padicSubfieldCondensedRing ell E ∨
        R = Profinite.padicAlgClCondensedRing ell) →
      (∀ (M : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (coefficientHeartRingObj R) X))),
        constantModelBoundedConstructible (coefficientHeartRingObj R) X M →
          IsExtContinuityGenerated (coefficientHeartRingObj R) X Set.univ M) ∧
      (∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj R) X)),
        IsConstantModelConstructible (coefficientHeartRingObj R) X M →
        ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
          (K : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (coefficientHeartRingObj R) X)),
          ∀ n : ℤ,
            IsIso (colimit.desc _
              ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ n ⋙
                preadditiveCoyoneda.obj
                  (op ((DerivedCategory.singleFunctor _ 0).obj M))).mapCocone
                    (colimit.cocone K))))) ∧
    (R = Profinite.padicIntegersCondensedRing ell E →
      ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj R) X)),
        (∃ (m : ℕ) (F : Fin (m + 1) → Subobject M)
          (hF : ∀ i : Fin m, F i.castSucc ≤ F i.succ),
          F 0 = ⊥ ∧ F (Fin.last m) = ⊤ ∧
            ∀ i : Fin m, IsExtContinuityStratum (coefficientHeartRingObj R) X
              (cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hF i)))) →
        IsExtContinuityGenerated (coefficientHeartRingObj R) X Set.univ
          ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale
