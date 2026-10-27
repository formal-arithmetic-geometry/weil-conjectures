/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Sheaf.Algebra.Homology.CompleteLocalCoherentDuality
import Sheaf.SecTraceFormula.LocalDerivedTensorNonvanishing
import Sheaf.Algebra.Homology.DerivedBimoduleTensorHom

/-! # Derived Hom detection over a complete local ring

Source: Stacks Project, dualizing.tex, Tags 0BFR(2) and 0A7C;
more-algebra.tex, Tags 0A65 and 0DJE, and the local tensor nonvanishing corollary
(blueprint: lem-trf-complete-local-nonzero-rhom-detection).

D(R) is realized on the existing one-object bottom-topology ringed site.
The derived internal Hom is the recorded K-injective ringed-site construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- Derived Hom from any nonzero bounded coherent complex over a complete Noetherian
local ring detects zero bounded coherent complexes. No scalar-action, projective-dimension,
or injective-dimension hypothesis on the source is required. D(R) is realized by
RingSiteModules R, and finite generation is evaluated at the unique site object.

Source: Stacks Project, dualizing.tex, Tags 0BFR(2), lemma-ubiquity-dualizing,
and 0A7C, lemma-dualizing; more-algebra.tex, Tags 0A65, lemma-internal-hom,
and 0DJE, lemma-tensor-pseudo-coherent
(blueprint: lem-trf-complete-local-nonzero-rhom-detection).

Proof:
1. Apply lem-trf-complete-local-coherent-duality to choose Omega. Write
   D(K) = RHom(K,Omega) and W = D(Z). Boundedness preservation puts W in Db_fg(R),
   and canonical biduality gives Z isomorphic to D(W).
2. By the closure clause of lem-trf-local-derived-tensor-nonvanishing,
   T = C tensor^L W lies in D-_fg(R), hence in D_fg(R). It may be unbounded below.
3. Specialize lem-trf-derived-bimodule-tensor-hom to the identity R to R and
   (X,E,V) = (C,W,Omega). The precomposition action agrees with the ordinary R-action.
   Currying identifies D(T) with RHom(C,D(W)), hence with RHom(C,Z) by functoriality
   of def-pur-derived-internal-hom. The hypothesis therefore makes D(T) zero.
4. Unbounded coherent biduality from lem-trf-complete-local-coherent-duality gives
   T isomorphic to D(D(T)) = D(0) = 0; Hom from the zero complex computes the last zero.
   The zero-detection clause of lem-trf-local-derived-tensor-nonvanishing then gives
   C = 0 or W = 0. Since C is nonzero, W = 0, and Z isomorphic to D(W) is zero. -/
theorem complete_local_nonzero_rhom_detection
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [HasDerivedCategory.{u} (RingSiteModules R)]
    (C Z : DerivedCategory (RingSiteModules R))
    (hCfin : ∀ i : ℤ, Module.Finite R
      (((homologyFunctor (RingSiteModules R) i).obj C).val.obj (op ⟨PUnit.unit⟩)))
    (hCbdd : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((homologyFunctor (RingSiteModules R) i).obj C))
    (hC : ¬ IsZero C)
    (hZfin : ∀ i : ℤ, Module.Finite R
      (((homologyFunctor (RingSiteModules R) i).obj Z).val.obj (op ⟨PUnit.unit⟩)))
    (hZbdd : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((homologyFunctor (RingSiteModules R) i).obj Z))
    (hHom : IsZero ((derivedInternalHomOfUniverses.{u, u, u, u}
      ⊥ (CochainComplex.onePointRingSheaf R)).obj (op C, Z))) :
    IsZero Z := by
  sorry

end DerivedCategory
