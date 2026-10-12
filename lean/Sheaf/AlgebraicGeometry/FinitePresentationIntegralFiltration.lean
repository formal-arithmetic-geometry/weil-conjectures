/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Integral-ideal filtrations in the finite-presentation interface

Source: Stacks Project, Tag 01YF.
(blueprint: lem-pc-e2-finite-presentation-integral-filtration)
 -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A finitely presented module on a Noetherian scheme has a finite filtration whose
quotients are pushforwards of ideals on integral closed subschemes.

Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.3, Tag 01YF.
(blueprint: lem-pc-e2-finite-presentation-integral-filtration)

Proof: On a Noetherian scheme finite presentation is equivalent to coherence. Apply
Noetherian induction to the closed support of a coherent module. Split a reducible support
into two proper closed supports using the support-union exact sequence. For irreducible
support, give it its reduced integral closed-subscheme structure with ideal J. A power of
J kills the module. The J-adic filtration reduces to modules killed by J. At the generic
point such a module is a finite-dimensional vector space. Clear denominators to embed a
finite sum of a nonzero coherent ideal of the integral subscheme, isomorphically near the
generic point. Its cokernel has strictly smaller closed support, so induction applies.
Filter the finite sum by its summands and concatenate with the cokernel filtration.
The zero module has the length-zero filtration. Represent all inclusions by subobjects
and their quotients by cokernels. This is the usual coherent filtration with its coherence
clauses forgotten; no higher-direct-image theorem is used. -/
theorem exists_finitePresentation_integral_filtration
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c),
      c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
      ∀ j : Fin m, ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
        IsClosedImmersion i ∧ IsIntegral Z ∧
        ∃ I : Z.IdealSheafData,
          Nonempty (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
            (hc j.castSucc_le_succ)) ≅ (pushforward i).obj I.toModules) := by sorry

end AlgebraicGeometry.Scheme.Modules
