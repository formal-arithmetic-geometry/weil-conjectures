/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleFilteredColimits
public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartKernelsCokernels
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartCanonicalPresentation
public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleExtensions
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedTriangulated
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedSums

/-!
# The ind-constructible derived category

Source: blueprint latest, `part-six-operations/sec-six-functors-basics/sec-compactness/`
`sec-ind-constructible-sheaves/sk-cor-ambient-ind-derived/_section.md`
and `sk-cor-ambient-ind-derived.proof.md` (blueprint: sk-cor-ambient-ind-derived).

The ordinary unbounded derived category and the filtered-colimit constructibility
predicate are the existing ambient constructions. Both canonical coefficient cases
are stated together, with no derived-completeness or finite-Tor restriction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 800000 in
-- The final conjunction unfolds large derived-category predicates during assembly.
/--
The ind-constructible derived category for either canonical condensed coefficient.

Source: blueprint latest,
`part-six-operations/sec-six-functors-basics/sec-compactness/`
`sec-ind-constructible-sheaves/sk-cor-ambient-ind-derived/_section.md`
and `sk-cor-ambient-ind-derived.proof.md`.

The first conjunct gives the triangulated, direct-sum, truncation and localizing-closure
claims for a finite intermediate extension `E` of `ℚ_ℓ`; the second gives the same
claims for the condensed algebraic closure.  In each case `P` is the predicate that
all cohomology objects are filtered colimits of constructible module objects.  The
bounded constructible predicate and the localizing closure are the ambient definitions
from `sk-def-sfb-bounded-constructible` and `sk-def-localizing-closure`.

Proof, following the two DAG steps in each coefficient case:
1. The long exact cohomology sequence expresses each third cohomology sheaf as an
   extension of a cokernel by a kernel. The ambient kernel, cokernel and extension
   closure of IndCons from `sk-prop-ind-heart` therefore gives triangle closure.
   Shifts reindex cohomology and zero has zero cohomology. Apply the packaged result
   `det-ambient-ind-derived-triangulated` to obtain the triangulated predicate.
2. Exactness of direct sums makes cohomology commute with sums, so the sum closure
   of IndCons applies degree by degree, including the empty sum. Canonical truncations
   retain the old cohomology in the retained degrees and put zero elsewhere. Each
   constructible module belongs to IndCons via a one-object filtered presentation.
   Thus Dic contains Dbc and is localizing, and the intersection defining Loc(Dbc)
   lies in Dic. These are the clauses of `det-ambient-ind-derived-sums`.
(blueprint: sk-cor-ambient-ind-derived).
-/
theorem ambientIndConstructibleDerived
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (let PE : ObjectProperty
        (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (padicSubfieldRingObj X ℓ E))) :=
      fun K ↦ ∀ n : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ n).obj K)
     let PQ : ObjectProperty
        (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (padicAlgClRingObj X ℓ))) :=
      fun K ↦ ∀ n : ℤ, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ n).obj K)
    (PE.IsTriangulated ∧
      (∀ (S : Type (u + 1))
        (K : S → DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (padicSubfieldRingObj X ℓ E)))
        (c : Cofan K), IsColimit c → (∀ s, PE (K s)) → PE c.pt) ∧
      (∀ (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (padicSubfieldRingObj X ℓ E))) (n : ℤ), PE K →
        PE ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        PE ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ≤ PE ∧
      (localizingClosure (constantModelBoundedConstructible
        (Profinite.continuousMapRingObj E) X) ≤ PE)) ∧
    (PQ.IsTriangulated ∧
      (∀ (S : Type (u + 1))
        (K : S → DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (padicAlgClRingObj X ℓ)))
        (c : Cofan K), IsColimit c → (∀ s, PQ (K s)) → PQ c.pt) ∧
      (∀ (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (padicAlgClRingObj X ℓ))) (n : ℤ), PQ K →
        PQ ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        PQ ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ≤ PQ ∧
      (localizingClosure (constantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ℓ) X) ≤ PQ))) := by
  dsimp only
  obtain ⟨htriE, htriQ⟩ :=
    indConstructibleDerived_isTriangulated ℓ E k p hp hpl X
  obtain ⟨hcompE, hsumE', htruncE', hdbcE', hlocE'⟩ :=
    indConstructibleDerived_sums_and_truncations ℓ E k p hp hpl X
  obtain ⟨hcompQ, hsumQ', htruncQ', hdbcQ', hlocQ'⟩ :=
    indConstructibleDerived_sums_and_truncations_padicAlgCl ℓ k p hp hpl X
  constructor
  · refine ⟨htriE, ?_, ?_, hdbcE', hlocE'⟩
    · intro S K c hc hK
      exact hsumE' S K c hc (fun s m ↦ hK s m)
    · intro K n hK
      exact htruncE' K n hK
  · refine ⟨htriQ, ?_, ?_, hdbcQ', hlocQ'⟩
    · intro S K c hc hK
      exact hsumQ' S K c hc (fun s m ↦ hK s m)
    · intro K n hK
      exact htruncQ' K n hK

end AlgebraicGeometry.ProEtale
