/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Uniform RHom bounds for a bounded injective target

Source: Stacks Project, More on Algebra, Tag 0A5S; Dualizing Complexes, Tag 0A7C;
Cohomology on Sites, Tags 08J7, 0A95 and 0A8X.
(blueprint: lem-trf-bounded-injective-rhom-amplitude).

The one-object ringed-site presentation is used through its existing ordinary-module
RHom presentation. The total Hom complex retains the R-module structure and the
standard differential, rather than just its underlying complex of abelian groups.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A fixed injective target supported in [a,b] reverses each cohomological bound of
an arbitrary source, with strict models and comparisons in D(R).
Source: Stacks 0A5S, 0A7C, 08J7, 0A95 and 0A8X
(blueprint: lem-trf-bounded-injective-rhom-amplitude).

Proof:
1. The lower support bound and termwise injectivity make J K-injective, by
   lem-weil-pbc-bounded-below-injectives-kinjective (Stacks 070J). In the Hom-complex
   characterization def-pur-kinjective-complex, degree-zero cocycles are chain maps
   and boundaries are null homotopies.
2. Represent K by C. If its cohomology vanishes above c, use the good truncation
   P = tau_le_c C, with cycles in degree c and zero terms above c. The map P to C is
   a quasi-isomorphism by lem-weil-pbc-truncation-cohomology. If cohomology vanishes
   below c, use Q = tau_ge_c C, with opcycles in degree c and zero below c, as in
   def-kun-truncations. The quotient C to Q is a quasi-isomorphism. Localization
   (def-weil-abstract-derived-category) gives the asserted model isomorphisms.
3. The arbitrary-K-injective-model clause of def-pur-derived-internal-hom and
   lem-pur-rhom-well-defined identify each total Hom into J with RHom(K,L).
   On the one-object site these are ordinary module-valued complexes and derived
   objects, with the ordinary-module presentation of that same RHom.
4. The product formula of def-pur-hom-complex, in its ordinary-module form
   def-sc-module-total-hom-complex, has factors Hom(P^p,J^(p+n)). For n < a-c,
   either p > c and P^p is zero, or p <= c and p+n < a, so J^(p+n) is zero.
   Every factor and hence the product term is zero. Its cohomology is zero too.
5. For n > b-c, each factor Hom(Q^p,J^(p+n)) is zero: p < c kills Q^p,
   while p >= c implies p+n > b and kills J^(p+n). The same argument and the
   comparison give the upper cohomological bound. Only P and Q depend on K,c;
   a,b remain fixed. No Noetherianity or finite generation is used. -/
theorem boundedInjective_rhom_amplitude
    (R : Type u) [CommRing R]
    (a b : ℤ) (hab : a ≤ b) (J : CochainComplex (ModuleCat.{u} R) ℤ)
    (hinj : ∀ i : ℤ, Injective (J.X i))
    (hlo : ∀ i : ℤ, i < a → IsZero (J.X i))
    (hhi : ∀ i : ℤ, b < i → IsZero (J.X i))
    (L : DerivedCategory (ModuleCat.{u} R)) (eJ : DerivedCategory.Q.obj J ≅ L) :
    ∀ (K : DerivedCategory (ModuleCat.{u} R)) (c : ℤ),
      ((∀ i : ℤ, c < i →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) →
        (∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
          (∀ p : ℤ, c < p → IsZero (P.X p)) ∧
          Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
          Nonempty (DerivedCategory.Q.obj (CochainComplex.moduleHomComplex P J) ≅
            (ordinaryModuleDerivedInternalHom R).obj (op K, L)) ∧
          (∀ n : ℤ, n < a - c →
            IsZero ((CochainComplex.moduleHomComplex P J).X n))) ∧
        (∀ n : ℤ, n < a - c →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
            ((ordinaryModuleDerivedInternalHom R).obj (op K, L))))) ∧
      ((∀ i : ℤ, i < c →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) →
        (∃ Q : CochainComplex (ModuleCat.{u} R) ℤ,
          (∀ p : ℤ, p < c → IsZero (Q.X p)) ∧
          Nonempty (DerivedCategory.Q.obj Q ≅ K) ∧
          Nonempty (DerivedCategory.Q.obj (CochainComplex.moduleHomComplex Q J) ≅
            (ordinaryModuleDerivedInternalHom R).obj (op K, L)) ∧
          (∀ n : ℤ, b - c < n →
            IsZero ((CochainComplex.moduleHomComplex Q J).X n))) ∧
        (∀ n : ℤ, b - c < n →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
            ((ordinaryModuleDerivedInternalHom R).obj (op K, L))))) := by
  sorry

end CategoryTheory
