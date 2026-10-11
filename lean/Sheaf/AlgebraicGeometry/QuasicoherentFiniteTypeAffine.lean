/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.Coherent
import Mathlib.Algebra.Module.FinitePresentation

/-! # Affine criteria for finite type and finite presentation of modules

Source: Stacks Project, Modules, Tags 01BN and 01BO; Properties, Tags 01PB and 01PC
(blueprint: lem-weil-pbc-quasi-coherent-finite-type-affine).
-/

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite presentation implies quasi-coherence. For a quasi-coherent module, finite type
and finite presentation on an affine open are equivalent to the corresponding finiteness
of its sections. Finite generation on an affine open cover gives finite type globally
and finite generation on every affine open; global finite presentation gives finitely
presented sections on every affine open.
Source: Stacks Project, Modules, Tags 01BN, 01BO; Properties, Tags 01PB, 01PC
(blueprint: lem-weil-pbc-quasi-coherent-finite-type-affine).

Proof (the nine steps of the node):
1. Identify an affine open `U` with `Spec O_X(U)` (def-pc-scheme,
   def-weil-affine-spectrum). Restriction transports the module and its sections
   (lem-weil-pbc-module-restriction-open-immersion-colimits). The free module has
   sections `R^n` (lem-weil-pbc-spec-tilde-free-module). Maps from it correspond to
   tuples of sections, and epimorphisms mean these sections generate locally
   (def-weil-sheaf-of-modules-category, def-weil-pbc-generating-sections,
   pqf-def-coherent).
2. The tilde-Gamma counit identifies quasi-coherent modules on an affine with tilde
   of their sections. Thus a map bijective on sections is an isomorphism, and a
   quasi-coherent module with zero sections is zero
   (lem-weil-pbc-affine-tilde-gamma-adjunction).
3. For the map from a finite free module given by sections, its image on an affine
   is their span, and its cokernel sections are the quotient by this span
   (lem-weil-pbc-quasi-coherent-module-cokernel-image,
   def-weil-pbc-generating-sections). Step 2 detects a zero cokernel. Therefore
   the sections generate the sheaf exactly when they generate its affine sections.
4. A local finite presentation is a cokernel of finite free quasi-coherent modules.
   Restrict to affine neighbourhoods, preserving cokernels, and apply the cokernel
   lemma to obtain quasi-coherence (lem-weil-pbc-module-restriction-open-immersion-colimits,
   def-weil-pbc-category-colimit, lem-weil-pbc-spec-tilde-free-module,
   lem-weil-pbc-quasi-coherent-module-cokernel-image, pqf-def-coherent).
5. Finite generators of the affine sections generate the sheaf by Step 3, proving
   finite type (def-weil-finitely-generated-module, pqf-def-coherent).
6. Conversely shrink local finite generating families to principal opens. Tilde
   sections there are localized modules (lem-weil-pbc-affine-tilde-gamma-adjunction,
   lem-weil-pbc-principal-localization-open-immersion,
   lem-weil-pbc-spec-module-tilde-sections, def-weil-pbc-module-localization-away).
   Step 3 gives finite generation there. Quasi-compactness gives finitely many such
   opens whose defining elements span the unit ideal
   (lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact). Descend finite generation
   by lem-weil-pbc-module-finite-of-localization-span.
7. A finite presentation of sections gives maps of finite free sheaves by Step 1.
   Their cokernel is quasi-coherent and has the prescribed sections by
   lem-weil-pbc-quasi-coherent-module-cokernel-image; Step 2 identifies it with the
   original module. This is a finite presentation of the sheaf.
8. Conversely choose a finite free surjection using Steps 5 and 6. Its kernel is
   quasi-coherent (lem-weil-pbc-quasi-coherent-module-kernel) and finite type
   (lem-weil-pbc-finite-presentation-kernel-surjection-finite-type). Step 6 makes
   its affine sections finitely generated. Sections of the kernel are the kernel
   of the section map, giving a finitely presented module of sections.
9. Finite type on a cover implies finite type at every point. Restriction of local
   generators and presentations preserves these properties (pqf-def-coherent,
   lem-weil-pbc-module-restriction-open-immersion-colimits). Apply the affine criteria
   to every affine open for both final assertions. -/
theorem quasicoherent_finite_type_affine (X : Scheme.{u}) :
    (∀ G : X.Modules, G.IsFinitePresentation → G.IsQuasicoherent) ∧
    (∀ F : X.Modules, F.IsQuasicoherent →
      (∀ U : X.Opens, IsAffineOpen U →
        ((F.over U).IsFiniteType ↔ Module.Finite Γ(X, U) Γ(F, U)) ∧
        ((F.over U).IsFinitePresentation ↔ Module.FinitePresentation Γ(X, U) Γ(F, U))) ∧
      (∀ (I : Type v) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ → (∀ i, IsAffineOpen (U i)) →
        (∀ i, Module.Finite Γ(X, U i) Γ(F, U i)) →
        F.IsFiniteType ∧ ∀ V : X.Opens, IsAffineOpen V → Module.Finite Γ(X, V) Γ(F, V)) ∧
      (F.IsFinitePresentation →
        ∀ U : X.Opens, IsAffineOpen U → Module.FinitePresentation Γ(X, U) Γ(F, U))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
