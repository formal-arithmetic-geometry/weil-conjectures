/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Sheafifying an actual affine ring resolution -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Sheafification transfers an actual finite-free ring resolution to an affine scheme.
Source: Stacks Project, Tag 01IB (affine equivalence), and Tag 01HV (exactness of tilde).
(blueprint: lem-pc-affine-sheaf-resolution-from-ring-model).

Proof: Identify the affine scheme with the spectrum of its global section ring via its
canonical affine isomorphism. Transport the tilde/global-sections adjunction across this
isomorphism. Apply tilde termwise to P and to f. Localization of modules is exact, so
sheafification is exact and sends f to a quasi-isomorphism. Since every term of C is
quasi-coherent, the counit from the sheafified global-sections complex to C is a termwise
isomorphism; its naturality makes it an isomorphism of complexes. Compose with that
counit to obtain the required map. The zero-preserving tilde functor preserves the
termwise upper bound. For each term of P choose a finite basis, enumerate it by Fin r,
and lift its index universe by ULift. Tilde carries the resulting free-module isomorphism
to an isomorphism with the free sheaf on ULift (Fin r). These choices occur only within
this existential proof, not in a definition. The zero ring and empty affine scheme
produce zero sheaves, so rank zero works in those cases. -/
theorem exists_affine_sheaf_resolution_of_ring_model
    {T : Scheme.{u}} (U : T.Opens) [IsAffine U.toScheme]
    (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (P : CochainComplex (ModuleCat.{u}
        (U.toScheme.ringCatSheaf.obj.obj (.op ⊤))) ℤ)
    (hP : P.IsStrictlyLE d)
    (hfree : ∀ i : ℤ, Module.Free (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) (P.X i) ∧
      Module.Finite (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) (P.X i))
    (f : P ⟶ ((SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf
      (.op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
    [QuasiIso f] :
    ∃ Q : CochainComplex U.toScheme.Modules ℤ, Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ, Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      ∃ e : Q ⟶ C, QuasiIso e := by sorry

end AlgebraicGeometry.Scheme.Modules
