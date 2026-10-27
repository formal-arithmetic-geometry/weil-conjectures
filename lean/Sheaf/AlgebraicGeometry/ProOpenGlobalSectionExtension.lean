/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.Constructible
import Mathlib.Topology.Spectral.Basic
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Topology.InverseImageStalk
import WeilConjectures.Topology.ProconstructibleClosureSpecialization
import Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection

/-!
# Extending global functions from a quasi-compact flat monomorphism

Source: Raynaud, Un critère d'effectivité de descente, Propositions 1.1, 1.2(i)
and 2.3(i), printed pp. 1–5
(blueprint: lem-sfb-proopen-global-section-extension).
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The image of a quasi-compact flat monomorphism is stable under generalization;
if its source is quasi-compact and its target quasi-separated, every global function
extends to a quasi-compact open neighbourhood of the image.
Source: Raynaud, Un critère d'effectivité de descente, Propositions 1.1, 1.2(i)
and 2.3(i), printed pp. 1–5
(blueprint: lem-sfb-proopen-global-section-extension).

The containment witness uses `Set.range V.ι`, which equals the open subset `V`
by `Scheme.Opens.range_ι`. Thus `IsOpenImmersion.lift V.ι j hV` is exactly the
canonical factorization through that open, and `appTop` is its pullback on functions.

Proof:
1. By lem-sfb-qc-flat-monomorphism-ringed-image, identify Z with the induced ringed
   subspace on E = j(Z). Its image is generalization-stable and retrocompact, and E
   is quasi-compact. Transfer the given section to that ringed subspace. If E is empty,
   take the empty open and its unique section.
2. Use lem-weil-pbc-topological-inverse-image-stalk and def-weil-pbc-module-stalk to
   represent the section locally by sections on Y. Refine to affine opens using
   lem-weil-pbc-affine-opens-basis and select a finite cover of E. Their union U₀ is
   quasi-compact by lem-weil-pbc-affine-scheme-qcqs, and quasi-separated as an open of Y;
   hence it is spectral by lem-weil-pbc-qcqs-scheme-spectral.
3. Each pairwise overlap A_ab is quasi-compact by pqf-lem-qs-intersection-qc, and its
   trace on E is quasi-compact by retrocompactness. The local sections have equal germs
   there by the inverse-image stalk isomorphism. The stalk description, affine basis,
   and finite subcovers yield a quasi-compact open W_ab inside A_ab, containing that
   trace, on which the two sections agree. For an empty trace use the empty open.
4. Each A_ab minus W_ab is constructible in U₀ by
   lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact and
   def-weil-constructible-subset. Their finite union F is constructible and misses E.
5. By lem-weil-pbc-spectral-proconstructible-closure-specialization, every point in
   the closure of F specializes from a point of F. Generalization stability of E
   therefore implies that this closure misses E. Choose finitely many affine opens
   covering E inside its open complement; their union V is quasi-compact.
6. On V the local sections agree on every overlap, since V avoids every A_ab minus
   W_ab. Glue them by the structure-sheaf axiom. Factor j through V using
   lem-weil-pbc-morphism-factors-through-open-subscheme. Its pullback is the original
   section on each member of the covering of Z, hence globally by sheaf uniqueness
   (def-weil-locally-ringed-space-morphism). -/
theorem exists_globalSection_extension_of_quasiCompact_flat_mono
    {Z Y : Scheme.{u}} (j : Z ⟶ Y) [QuasiCompact j] [Flat j] [Mono j]
    [CompactSpace Z] [QuasiSeparatedSpace Y] :
    (∀ (e y : Y), e ∈ Set.range j → e ∈ closure ({y} : Set Y) → y ∈ Set.range j) ∧
      ∀ s : Γ(Z, ⊤), ∃ (V : Y.Opens) (_ : IsCompact (V : Set Y))
        (hV : Set.range j ⊆ Set.range V.ι) (t : Γ(V.toScheme, ⊤)),
        (IsOpenImmersion.lift V.ι j hV).appTop t = s := by
  sorry

end AlgebraicGeometry
