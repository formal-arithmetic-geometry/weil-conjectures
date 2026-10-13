/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.LocalizedModule.Exact

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- The maximal ideal is not associated to a boundary localization of a submodule
of restriction sections.

Source: Stacks Project, Tag 0AVN, finite basic-open cover argument; Tags 01LC and 05AM.
(blueprint: stage3-boundary-maximal-not-associated)

Proof: Put R = O(V) and P = (j_*(N|U))(V). Since V is Noetherian,
U intersect V is covered by finitely many basic opens D(f_i) contained in U.
The boundary hypothesis implies f_i belongs to p for every i. The open immersion
is quasi-compact and quasi-separated, so its pushforward is quasi-coherent
(Tag 01LC). Thus its basic-open section maps are module localizations at f_i.
Sheaf separatedness on U intersect V makes P inject into the finite product of
these localized section modules. Localization at p preserves this injection
and the finite product. The inclusion S into P also remains injective.
If the maximal ideal of R_p were associated to S_p, there would be a nonzero
z in S_p annihilated by that ideal. The image of each f_i lies in the maximal
ideal and kills z, but is invertible in the i-th localized section module.
Every component of z therefore vanishes, contradicting injectivity. An empty
cover makes P, and hence S, zero, which has no associated primes. This argument
also covers S = 0 and does not require N to be finite. -/
theorem boundary_maximal_not_associated
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens) (N : L.Modules)
    (hqc : N.IsQuasicoherent) (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (hS : S.FG) (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime]
    (hy : hV.fromSpec ⟨p, inferInstance⟩ ∉ U) :
    IsLocalRing.maximalIdeal (Localization.AtPrime p) ∉
      associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p S) := by sorry


end AlgebraicGeometry.Scheme
