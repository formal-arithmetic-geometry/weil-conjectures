/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Local equational criterion for flat module sheaves

Source: Stacks Project, Modules on Sites, Tag 08FC, equivalence (1) and (2)
(blueprint: lem-weil-pbc-site-flat-equational-criterion).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace SheafOfModules

/-- A module sheaf is flat exactly when each finite relation between its sections locally
factors through a finite free module with zero coefficient relation.
Source: Stacks Project, Modules on Sites, Tag 08FC, (1) iff (2)
(blueprint: lem-weil-pbc-site-flat-equational-criterion).

Proof: First use the sectionwise cokernel followed by sheafification to identify local
lifting in exact sequences. Sheafification also makes every tensor section locally a finite
sum of pure tensors, and detects a zero presheaf tensor locally.
For the forward implication restrict the flat sheaf to C/U and tensor the exact complex
K → A^n → A, where K is the kernel of the row of coefficients. Locally lift the vector of
sections to K tensor M and express that lift as a finite sum k_q tensor t_q. The coordinates
b_pq of k_q give both displayed equations. For n = 0 use the identity cover and l = 0.
For the converse first induct on the number of columns to obtain the finite-matrix version:
factor the last column, then factor the remaining columns over a refinement and compose.
Given a monomorphism N → N', represent a tensor in its kernel locally by a finite sum and
make its image zero already in the presheaf tensor. Present M(U) as a quotient of the free
module on its elements. Right exactness of tensor gives finitely many kernel vectors
witnessing this zero; choose a finite set containing their supports and the given elements.
This yields a finite presentation P and a lift of the tensor to N(U) tensor P that dies in
N'(U) tensor P. Apply the finite-matrix criterion to that presentation: locally P → M
factors through a finite free module. Tensoring N → N' with that free module is injective,
so the original tensor vanishes locally and therefore globally. Finally tensor sheaves are
right exact: balanced pairings killing N tensor M descend uniquely through the sheaf
cokernel by local lifting and gluing. Preservation of monomorphisms together with this
cokernel property proves exactness of tensorRight M, hence flatness. -/
theorem isFlat_iff_local_equationalCriterion
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (A : Sheaf J.toGrothendieck CommRingCat.{u})
    (M : ringedSiteModules.{u}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) :
    IsFlat M ↔
      ∀ (U : C) (n : ℕ) (a : Fin n → A.obj.obj (op U))
        (s : Fin n → M.val.obj (op U)),
        (∑ p : Fin n, a p • s p) = 0 →
        ∃ S : Presieve U, S ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), S f →
            ∃ (l : ℕ) (b : Fin n → Fin l → A.obj.obj (op V))
              (t : Fin l → M.val.obj (op V)),
              (∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q) ∧
              (∀ q : Fin l, (∑ p : Fin n, A.obj.map f.op (a p) * b p q) = 0) := by
  sorry

end SheafOfModules
