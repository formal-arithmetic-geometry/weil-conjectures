/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel

/-! # Bounded flat complexes computing proper cohomology -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- An affine quasi-coherent complex with pseudo-coherent global sections admits an
actual finite-free resolution at its termwise upper bound.
Source: Stacks Project, Tag 064U, and Tag 08E7.
Proof: Exactness of global sections on quasi-coherent modules on an affine scheme
identifies C with the associated sheaf complex of its global sections. Pseudo-coherence
and the vanishing above d give a bounded-above finite-free ring model with upper bound d
by Tag 064U. A bounded-above projective complex is K-projective; lift the derived
isomorphism into the global-sections complex to an actual chain map, whose cone is acyclic.
The exact tilde functor sends this map to a quasi-isomorphism. Compose with the affine
counit to obtain Q → C; tilde sends finite free modules to free sheaves of the same rank.
Zero complexes, including the empty base, give rank zero. No flatness is needed.
(blueprint: lem-pc-proper-cohomology-finite-free-resolution). -/
theorem exists_proper_cohomology_finite_free_resolution {T : Scheme.{u}}
    (U : T.Opens) [IsAffine U.toScheme]
    (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCle : C.IsStrictlyLE d)
    (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hpc : (letI : CommRing (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(U.toScheme, ⊤));
        letI := HasDerivedCategory.standard
          (ModuleCat.{u} (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)));
        DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
          (((SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf (.op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C)))) :
    ∃ Q : CochainComplex U.toScheme.Modules ℤ, Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (Q.X n ≅ SheafOfModules.free
          (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      ∃ e : Q ⟶ C, QuasiIso e := by sorry

end AlgebraicGeometry.Scheme.Modules
