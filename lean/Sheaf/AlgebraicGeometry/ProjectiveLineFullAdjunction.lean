/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ProperStability
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition
import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals

/-!
# The full projective-line adjunction

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-amb-p1-adjunction.md
(blueprint: thm-amb-p1-adjunction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- On the entire ordinary etale derived categories, projective-line direct image
is left adjoint to inverse image followed by tensor with the shifted finite Tate line.
Its counit is exactly the normalized inverse-projection trace composite.
Source: blueprint thm-amb-p1-adjunction (blueprint: thm-amb-p1-adjunction).

Proof:
1. For `M` on P, put W = P times_S P with projections p1,p2 and diagonal Delta.
   Derived direct-image composition identifies M with Rp2_* Delta_* M.
   Properness of projective space, stability under base change, and separatedness
   make the projections and diagonal proper. Finite type over a Noetherian base
   makes P and W Noetherian. The proper projection formula identifies Delta_* M
   with Delta_* A_P tensor p1^-1 M. Apply Rp2_* to the diagonal class tensor M,
   then proper base change and projection give a natural unit M -> G F M.
   The proper-base-change theorem applies to all unbounded objects because N A = 0.
2. Use `projectiveLineTraceEpsilon` as counit. Its components are inverse ordered
   projection followed by tensor with the normalized trace and the unit constraint.
3. Expand epsilon_(F M) after F eta_M. Derived direct-image composition and
   exchange/tensor coherence turn it into Rq_* of identity on M tensored with
   t_p1 after Rp1_* delta. The projective-line decomposition and its base-change
   compatibility identify t_p1 with the pulled-back trace.
4. The a=1 diagonal-integral identity makes this factor identity, proving the
   first triangle.
5. For the second triangle put M=G K. The two pullbacks of q^-1 K agree, so the
   proper projection formula takes out this common coefficient. Tensor/exchange
   coherence identifies G epsilon_K with this coefficient tensored with t_p2.
   Eta_(G K) contributes Rp2_* delta. Every shift crossing a term is by two,
   hence its Koszul sign is one.
6. The a=2 diagonal-integral identity makes the remaining factor identity,
   proving G epsilon_K after eta_(G K) is identity.
7. The unit/counit Hom bijections from these two triangles give the adjunction,
   with precisely the prescribed natural transformation as its counit. -/
theorem exists_projectiveLineFullAdjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ∃ adj : (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)) ⊣
      ordinaryFiniteP1Right A N hA S,
      ∀ K : DerivedCategoryModule A S,
        adj.counit.app K = projectiveLineTraceEpsilon N hN A hA S hS K := by
  sorry

end AlgebraicGeometry.Etale
