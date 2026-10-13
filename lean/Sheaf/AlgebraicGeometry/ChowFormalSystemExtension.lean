/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Extension of pulled formal systems across a proper compactification

Source: Stacks Project, Theorem 088E, proof, paragraph after Chow's lemma.
(blueprint: lem-weil-pbc-chow-formal-system-extension)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Extend the pulled formal system to a fixed proper compactification. This assertion
uses neither adic completeness nor an algebraization theorem.

Source: Stacks Project, Theorem 088E, proof, paragraph after Chow's lemma.
(blueprint: lem-weil-pbc-chow-formal-system-extension)

Proof:
1. Pull G back along q. Finite-type module support pulls back to the inverse image of
   its support. All levels have the same support: at a stalk, a zero quotient gives
   M = I^k M = I^(2*k) M = 0 by nilpotent annihilation. Properness of q makes this
   inverse-image support proper over S.
2. Its image under j is closed in X: the source support is proper over S and X is
   separated over S. Each pulled level therefore extends by zero to a coherent module
   on X, equivalently its direct image under j (Stacks Lemma 0CYJ).
3. Apply direct image to every transition. On j(Y), ideal products and quotients have
   the original adic identities, since J.comap p pulls back to Q.comap q by hQ and hj.
   On the complement of the closed support every level is zero. These two opens cover
   X, so annihilation and quotient-transition isomorphisms hold globally. The extended
   levels and transitions form H in Coh(X,J.comap p).
4. The open-immersion restriction/direct-image counit is an isomorphism at every level.
   Its naturality with transitions gives the required isomorphism of systems. -/
theorem exists_chow_formal_system_extension
    {S Z Y X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] [IsNoetherian X]
    (f : Z ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (J : S.IdealSheafData) (Q : Z.IdealSheafData) (hQ : Q = J.comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (q : Y ⟶ Z) [IsProper q] (p : X ⟶ S) [IsProper p]
    (j : Y ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q ≫ f) :
    ∃ H : CoherentFormalModule X (J.comap p),
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        H.obj ⋙ Scheme.Modules.tensorPullback j) := by sorry

end AlgebraicGeometry
