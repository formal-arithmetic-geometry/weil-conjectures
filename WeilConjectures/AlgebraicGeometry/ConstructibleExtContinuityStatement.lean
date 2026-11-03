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
public import Mathlib.FieldTheory.IsAlgClosed.Basic

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

The standing field is finite or algebraically closed, as fixed in
`literature/blueprint/latest/blueprint/part-six-operations/prose-P1-01.md` (paragraph
"Throughout this part the base field is finite or algebraically closed") and
`literature/blueprint/latest/blueprint/sec-introduction/sec-conventions/prose-01-09.md`.

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
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (_hchar : ringChar k ≠ ell)
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
  -- The standing finite-or-algebraically-closed setting supplies the permitted inputs.
  -- The reused closed-support and bounded-continuity argument needs only finite type here.
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  refine ⟨?_, ?_, ?_⟩
  · intro M hM I _ _ K b hb n
    exact constructible_ext_continuity ell E R _hR X M hM K b hb
      (colimit.cocone K) (colimit.isColimit K) n
  · intro hfield
    constructor
    · intro M hM
      exact bounded_constructible_ext_generated ell E R hfield X M hM
    · intro M hM I _ _ K n
      exact constructible_sheaf_ext_continuity ell E R hfield X M hM K
        (colimit.cocone K) (colimit.isColimit K) n
  · intro _ M hM
    let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)
    let G := extContinuityShiftedStrata (coefficientHeartRingObj R) X Set.univ
    let P : ObjectProperty (DerivedCategory A) := fun D ↦ ∃ n : ℕ, G.extensionProductIter n D
    have : G.IsClosedUnderIsomorphisms := ⟨by
      rintro D D' e ⟨N, hN, t, ht, ⟨eN⟩⟩
      exact ⟨N, hN, t, ht, ⟨e.symm ≪≫ eN⟩⟩⟩
    have hGn (n : ℕ) : (G.extensionProductIter n).IsClosedUnderIsomorphisms := by
      cases n with
      | zero => change G.IsClosedUnderIsomorphisms; infer_instance
      | succ n => rw [ObjectProperty.extensionProductIter_succ]; infer_instance
    have : P.IsClosedUnderIsomorphisms := ⟨by
      rintro D D' e ⟨n, hn⟩
      have := hGn n
      exact ⟨n, (G.extensionProductIter n).prop_of_iso e hn⟩⟩
    have hsingle (N : A) (hN : IsExtContinuityStratum (coefficientHeartRingObj R) X N) :
        G ((DerivedCategory.singleFunctor A 0).obj N) := by
      exact ⟨N, hN, 0, Set.mem_univ _,
        ⟨((shiftFunctorZero (DerivedCategory A) ℤ).app _).symm⟩⟩
    have hzero (N : A) (hN : IsZero N) :
        IsExtContinuityStratum (coefficientHeartRingObj R) X N := by
      have hfree (Y : Scheme.{u}) :
          IsZero (Mod.finiteFree (condensedRingObj (coefficientHeartRingObj R) Y) 0) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 i
      have hL : IsLisseCoefficientModule (coefficientHeartRingObj R) (0 : A) := by
        refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
        exact ⟨0, ⟨((CondensedRing.upperStar (coefficientHeartRingObj R) _).map_isZero
          (isZero_zero A)).iso (hfree _)⟩⟩
      refine ⟨X, X, 𝟙 X, 𝟙 X, inferInstance, inferInstance, 0, hL, ⟨?_⟩⟩
      exact hN.iso ((CondensedRing.lowerStar (coefficientHeartRingObj R) (𝟙 X)).map_isZero
        ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj R) (𝟙 X)).map_isZero
          (isZero_zero A)))
    obtain ⟨m, F, hF, hbot, htop, hquot⟩ := hM
    have hPF (r : Fin (m + 1)) : P ((DerivedCategory.singleFunctor A 0).obj (F r)) := by
      induction r using Fin.induction with
      | zero =>
        refine ⟨0, hsingle _ (hzero _ ?_)⟩
        rw [hbot]
        exact (isZero_zero A).of_iso Subobject.botCoeIsoZero
      | succ i ih =>
        let f := Subobject.ofLE (F i.castSucc) (F i.succ) (hF i)
        let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
        obtain ⟨n, hn⟩ := ih
        refine ⟨n + 1, ?_⟩
        rw [ObjectProperty.extensionProductIter_succ']
        exact ⟨_, _, _, _, _, hS.singleTriangle_distinguished, hn, hsingle _ (hquot i)⟩
    have e : (F (Fin.last m) : A) ≅ M :=
      eqToIso (congrArg (fun S : Subobject M ↦ (S : A)) htop) ≪≫
        Subobject.underlyingIso (𝟙 M)
    exact P.prop_of_iso ((DerivedCategory.singleFunctor A 0).mapIso e) (hPF (Fin.last m))

end AlgebraicGeometry.ProEtale
