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
import Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.LocalizedModule.Exact

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- Finite localized restriction maps detect sections of a boundary submodule.

Source: Stacks Project, Tag 0AVN, finite basic-open argument, and Tag 01LC.
(blueprint: stage3-boundary-localized-finite-detector)

Proof: Write R = O(V) and P = (j_*(N|U))(V). The Noetherian affine V has
Noetherian underlying space, so U intersect V has a finite cover by basic opens
D(f_i) contained in U. Since the point of p is outside U, every f_i lies in p.
The restricted module N|U is quasi-coherent. The open immersion is qcqs over
V, and its pushforward is quasi-coherent by Tag 01LC. Thus restrictions from
P to the section modules on D(f_i) are the module localizations P[1/f_i].
Sheaf separatedness on U intersect V makes the map into their finite product
injective. Localize this map at p: localization preserves injections and finite
products. Compose it with the localized inclusion of S into P. Take Q_i to be
(P[1/f_i])_p, take a_i to be the image of f_i in the maximal ideal of R_p,
and take phi_i to be the component maps of this composite. Multiplication by
a_i is invertible on Q_i, hence injective. Injectivity of the composite gives
the zero-detection assertion. If the cover is empty, the sheaf axiom says P
is zero, so the same assertion holds for S_p. Neither finite generation of S
nor finite type of N is used. This is the restriction-map construction, before
the separate associated-prime argument. -/
theorem boundary_localized_finite_detector
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens) (N : L.Modules)
    (hqc : N.IsQuasicoherent) (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime]
    (hy : hV.fromSpec ⟨p, inferInstance⟩ ∉ U) :
    ∃ (n : ℕ) (Q : Fin n → ModuleCat.{u} (Localization.AtPrime p))
      (a : Fin n → IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (φ : (i : Fin n) → LocalizedModule.AtPrime p S →ₗ[Localization.AtPrime p] Q i),
      (∀ i, Function.Injective (fun x : Q i ↦ (a i : Localization.AtPrime p) • x)) ∧
      (∀ z, (∀ i, φ i z = 0) → z = 0) := by sorry

end AlgebraicGeometry.Scheme
