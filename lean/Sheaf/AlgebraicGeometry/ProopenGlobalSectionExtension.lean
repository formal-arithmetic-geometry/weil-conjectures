/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Constructible
import Mathlib.Topology.Spectral.Basic
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Topology.InverseImageStalk
import WeilConjectures.Topology.ProconstructibleClosureSpecialization
import Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection

/-!
# Extending functions from a quasi-compact flat monomorphism

Source: Raynaud, Un critère d'effectivité de descente, Propositions 1.1, 1.2(i)
and 2.3(i), printed pp. 1–2 and 4–5
(blueprint: lem-sfb-proopen-global-section-extension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The image of a quasi-compact flat monomorphism is stable under generalization.
If its source is quasi-compact and its target quasi-separated, every global function
on its source extends to a quasi-compact open neighbourhood of that image.
The equation `jV ≫ V.ι = j` specifies the unique factorization through this open.

Source: Raynaud, Un critère d'effectivité de descente, Propositions 1.1, 1.2(i)
and 2.3(i), printed pp. 1–2 and 4–5
(blueprint: lem-sfb-proopen-global-section-extension).

Proof:
1. By lem-sfb-qc-flat-monomorphism-ringed-image, identify Z with the ringed subspace
   E = j(Z) carrying the inverse-image structure sheaf. Its image is retrocompact
   and stable under generalization. It is quasi-compact because Z is. If E is empty,
   use the empty open and its unique section.
2. Represent the germ of the given section at each point of E by a section on an
   ambient neighbourhood, using lem-weil-pbc-topological-inverse-image-stalk and
   def-weil-pbc-module-stalk. Shrink using germ equality and the affine-open basis
   lem-weil-pbc-affine-opens-basis, so the representative agrees on the whole trace
   in E. Choose finitely many such affine opens U_a covering E. Their union U_0
   is quasi-compact and quasi-separated, hence spectral, by
   lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-qcqs-scheme-spectral.
3. Each overlap A_ab = U_a ∩ U_b is quasi-compact by pqf-lem-qs-intersection-qc.
   Retrocompactness makes E ∩ A_ab quasi-compact. The representatives have equal
   germs there, by the inverse-image stalk isomorphism. Finitely many affine
   neighbourhoods of germ equality give a quasi-compact open W_ab inside A_ab,
   containing E ∩ A_ab, on which the sections agree. Use the empty open when the
   trace is empty. This uses the same stalk and affine-open results as step 2.
4. In U_0, A_ab and W_ab are retrocompact by
   lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact. Thus A_ab minus W_ab
   is constructible by def-weil-constructible-subset. Their finite union F is
   constructible and disjoint from E.
5. If the closure of F met E, apply
   lem-weil-pbc-spectral-proconstructible-closure-specialization to the singleton
   family F. It gives a point of F generalizing a point of E, contradicting
   generalization stability. Inside U_0 minus this closure, choose finitely many
   affine neighbourhoods covering E and let V be their union. It is a
   quasi-compact open containing E and missing every A_ab minus W_ab.
6. The representatives agree on overlaps inside V and glue by the structure-sheaf
   axiom to a section t. Factor j through V by
   lem-weil-pbc-morphism-factors-through-open-subscheme. On each inverse image of
   U_a the pullback of t equals the original section, by the ringed-image
   identification and def-weil-locally-ringed-space-morphism. Sheaf uniqueness
   gives the equality globally.
-/
theorem proopen_global_section_extension {Z Y : Scheme.{u}} (j : Z ⟶ Y)
    [QuasiCompact j] [Flat j] [Mono j] [CompactSpace Z] [QuasiSeparatedSpace Y] :
    StableUnderGeneralization (Set.range j) ∧
      ∀ s : Γ(Z, ⊤), ∃ V : Y.Opens,
        IsCompact (V : Set Y) ∧ Set.range j ⊆ (V : Set Y) ∧
          ∃ (jV : Z ⟶ V.toScheme) (t : Γ(V.toScheme, ⊤)),
            jV ≫ V.ι = j ∧ jV.appTop t = s := by
  sorry

end AlgebraicGeometry
