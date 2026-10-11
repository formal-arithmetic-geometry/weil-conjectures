/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite global generators on an affine scheme

Source: Stacks Project, Properties, Tag 01PB, and Schemes, Tags 01IA and 01HV
(blueprint: lem-weil-pbc-affine-finite-type-generating-sections).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite type quasi-coherent module on an affine scheme has finitely generated global
sections and a finite family of global generators. Every finite family spanning its module
of global sections generates the sheaf. A section in `G.sections` is a compatible family
on opens, determined by its value at `⊤`; `freeHomEquiv.symm` is the map sending the free
basis to the specified sections. Its being epi means surjectivity as a map of sheaves.

Source: Stacks Project, Properties, Tag 01PB; Schemes, Tags 01IA and 01HV
(blueprint: lem-weil-pbc-affine-finite-type-generating-sections).

Proof:
1. Transport along an affine isomorphism to `Spec R`, with `R = Γ(U, ⊤)`
   (`def-pc-scheme`). By `lem-weil-pbc-quasi-coherent-finite-type-affine` (a), finite type
   (`pqf-def-coherent`) implies that `M = Γ(G, ⊤)` is a finite R-module. Choose a finite
   generating family; existence of sheaf generators follows from the assertion for any
   such family proved below (`def-weil-pbc-generating-sections`).
2. By `lem-weil-pbc-spec-module-tilde-sections` and the counit isomorphism of
   `lem-weil-pbc-affine-tilde-gamma-adjunction` (3), `G ≅ M~`, compatibly with global
   sections and their germs.
3. At a prime p, the local ring is the localization of R
   (`lem-weil-pbc-spec-domain-stalks-function-field` (1)), and the stalk is the localization
   of M (`lem-weil-pbc-spec-tilde-stalk-localization`). Every stalk element is m/s.
   Express m in the chosen generators h_j, so m/s is the sum of their germs with
   coefficients r_j/s. Thus the free-sheaf map is surjective on every stalk.
4. By `lem-weil-pbc-locally-surjective-iff-stalks`, stalkwise surjectivity is surjectivity
   as a map of sheaves, hence the family generates (`def-weil-pbc-generating-sections`). -/
theorem affine_finiteType_generatingSections (U : Scheme.{u}) [IsAffine U]
    (G : U.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    Module.Finite Γ(U, ⊤) Γ(G, ⊤) ∧
      (∃ σ : SheafOfModules.GeneratingSections G, Finite σ.I) ∧
      (∀ (k : ℕ) (s : ULift.{u} (Fin k) → G.sections),
        Submodule.span (M := Γ(G, ⊤)) Γ(U, ⊤)
          (Set.range (fun i => (s i).1 (.op ⊤))) = ⊤ →
          Epi (G.freeHomEquiv.symm s)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
