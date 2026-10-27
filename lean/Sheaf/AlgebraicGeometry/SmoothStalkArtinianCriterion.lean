/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.AlgebraicGeometry.Stalk
import WeilConjectures.AlgebraicGeometry.SmoothArtinianLiftingAtPoint

/-! # Smoothness from Artinian lifting of stalk homomorphisms

Source: Stacks Project, More on Morphisms, Tag 02HX, (3) implies (1), with Algebra,
Definition 02HS, Schemes Tag 01J6 and Sheaves Tag 008M
(blueprint: lem-trf-smooth-stalk-artinian-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The actual stalk rings at `z` and `f z` are Noetherian; lifting compatible local
homomorphisms from these stalks through all small Artinian extensions implies smoothness
on an open neighbourhood of `z`. Scheme stalks and `IsLocalRing` are already nonzero local
rings. The kernel isomorphism with the residue field is an isomorphism of `C'`-modules:
it expresses dimension one over the residue field without choosing a coefficient field
or adding a residue-field action as extra input.

Source: Stacks Project, More on Morphisms, Tag 02HX, (3) implies (1), with Algebra,
Definition 02HS, Schemes Tag 01J6 and Sheaves Tag 008M
(blueprint: lem-trf-smooth-stalk-artinian-criterion).

Proof following the five steps of the node:
1. Choose a Noetherian affine neighbourhood `Spec R` of `f z` using
   pqf-def-locnoeth, and an affine `Spec S` containing `z` over it with `S` finite
   type over `R` using def-weil-finite-type-morphism. By
   lem-weil-pbc-finite-type-algebra-noetherian, `S` is Noetherian. Identify both
   stalks with localizations by lem-weil-pbc-affine-open-stalk-localization and
   apply lem-weil-pbc-localization-noetherian. Their local, nonzero structures
   and the locality of `f.stalkMap z` come from def-weil-locally-ringed-space-morphism.
2. A length-one kernel over a local ring is isomorphic to its residue field.
   Conversely, the displayed annihilation and kernel isomorphism make its submodules
   exactly the vector subspaces of a one-dimensional residue-field vector space,
   so it has length one. A surjective map of nonzero local rings is local, hence
   its spectrum map sends closed point to closed point
   (lem-weil-pbc-spec-map-stalk-localization).
3. For any centred test square of lem-weil-pbc-smooth-artinian-lifting-at-point,
   apply lem-weil-pbc-morphism-from-spec-local-ring to obtain local maps `a` and `b`.
   By lem-weil-pbc-spec-map-stalk-localization and
   lem-weil-pbc-scheme-stalk-map-composition, commutativity is precisely
   `q.comp a = b.comp (f.stalkMap z).hom`.
4. The hypothesis gives the local lift `c`. The bijection of
   lem-weil-pbc-morphism-from-spec-local-ring turns it into a scheme lift centred
   at `z`. Both triangular equalities follow from the two ring-map equalities,
   the same stalk composition formula and the Spec stalk localization formula.
5. Apply (2) implies (1) of lem-weil-pbc-smooth-artinian-lifting-at-point to the
   original locally finite type morphism over the locally Noetherian target.
   This produces the required smooth restriction containing `z`.
-/
theorem noetherian_stalks_and_smooth_near_of_artinian_local_lifting
    {Z T : Scheme.{u}} (f : Z ⟶ T) [LocallyOfFiniteType f]
    [IsLocallyNoetherian T] (z : Z) :
    IsNoetherianRing (T.presheaf.stalk (f z)) ∧
      IsNoetherianRing (Z.presheaf.stalk z) ∧
      ((∀ (C' C : Type u) [CommRing C'] [CommRing C]
          [IsArtinianRing C'] [IsArtinianRing C] [IsLocalRing C'] [IsLocalRing C]
          (q : C' →+* C), Function.Surjective q →
          (∀ r ∈ IsLocalRing.maximalIdeal C', ∀ x ∈ RingHom.ker q, r * x = 0) →
          Nonempty ((RingHom.ker q) ≃ₗ[C'] IsLocalRing.ResidueField C') →
          ∀ (a : T.presheaf.stalk (f z) →+* C') (b : Z.presheaf.stalk z →+* C),
            IsLocalHom a → IsLocalHom b → q.comp a = b.comp (f.stalkMap z).hom →
            ∃ c : Z.presheaf.stalk z →+* C',
              IsLocalHom c ∧ q.comp c = b ∧ c.comp (f.stalkMap z).hom = a) →
        ∃ U : Z.Opens, z ∈ U ∧ Smooth (U.ι ≫ f)) := by
  sorry

end AlgebraicGeometry
