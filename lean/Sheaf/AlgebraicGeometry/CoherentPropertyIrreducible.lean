/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Property devissage on an irreducible closed support

Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.5, Tag 01YH,
label `lemma-property-irreducible` (blueprint: lem-pc-coherent-property-irreducible).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A two-out-of-three property of coherent modules supported in an irreducible closed set
holds for all of them if it holds for ideals on strictly smaller integral closed subschemes
and for one module with a one-dimensional residue-field stalk at the generic point.
A quasi-coherent ideal sheaf of `O_Z` is a `Z.IdealSheafData`, with module `I.toModules`.
The existential residue-field module structure is required to induce the original stalk-ring
scalar action through the residue map, so it is precisely the quotient action.

Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.5, Tag 01YH,
label `lemma-property-irreducible` (blueprint: lem-pc-coherent-property-irreducible).

Proof (the six steps of the node):
1. Two-out-of-three and the distinguished module give the property for zero by the exact
   sequence G → G → 0. They then give invariance under isomorphism and preservation under
   finite filtrations by induction. The sequence 0 → 0 → 0 alone does not give the base case.
2. If a coherent module misses the generic point, filter it using
   lem-weil-pbc-coherent-filtration-integral-subschemes. Stalk exactness puts the supports of
   the quotients inside its support. By lem-weil-pbc-integral-scheme-ideal-generic-stalk each
   nonzero ideal quotient has support equal to the image of its integral closed subscheme.
   These images are strictly contained in T; hypothesis (2) and step 1 give the property.
3. Give T its reduced induced closed subscheme structure using
   lem-weil-pbc-reduced-induced-closed-subscheme. It is integral. Apply
   lem-weil-pbc-coherent-generic-point-ideal-inclusion to G. The generic stalk comparison,
   using lem-weil-pbc-integral-scheme-ideal-generic-stalk and dimension one, forces one
   summand and a nonzero ideal I. The cokernel misses the generic point and has the property
   by step 2; two-out-of-three gives the property for the pushforward of I.
4. For every nonzero quasi-coherent ideal I' contained in I, its pushforward injects into G.
   The generic stalk map is an isomorphism by lem-weil-pbc-integral-scheme-ideal-generic-stalk.
   Its coherent cokernel misses the generic point, so step 2 and two-out-of-three give the
   property for the pushforward of I'.
5. For an arbitrary nonzero ideal I'', the intersection with I has full generic stalk and
   is nonzero by lem-weil-pbc-integral-scheme-ideal-generic-stalk. Step 4 applies to it.
   The quotient of I'' by the intersection misses the generic point; step 2 and
   two-out-of-three give the property for its pushforward. The zero ideal uses step 1.
6. Filter an arbitrary coherent module supported in T by
   lem-weil-pbc-coherent-filtration-integral-subschemes. Proper-support quotients use (2).
   For full-support quotients, uniqueness in lem-weil-pbc-reduced-induced-closed-subscheme
   identifies their integral closed subscheme with the reduced structure on T, so step 5
   and isomorphism invariance apply. Step 1 finishes the filtration. -/
theorem coherent_property_irreducible
    (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hTclosed : IsClosed T) (hTirreducible : IsIrreducible T)
    (ξ : X) (hξ : IsGenericPoint ξ T) (P : X.Modules → Prop)
    (hshort : ∀ S : ShortComplex X.Modules, S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      {x : X | ¬ Subsingleton (S.X₁.presheaf.stalk x)} ⊆ T →
      {x : X | ¬ Subsingleton (S.X₂.presheaf.stalk x)} ⊆ T →
      {x : X | ¬ Subsingleton (S.X₃.presheaf.stalk x)} ⊆ T →
      ((P S.X₁ ∧ P S.X₂) → P S.X₃) ∧
      ((P S.X₁ ∧ P S.X₃) → P S.X₂) ∧
      ((P S.X₂ ∧ P S.X₃) → P S.X₁))
    (hsmaller : ∀ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      Set.range i.base ⊂ T →
      ∀ I : Z.IdealSheafData, P ((pushforward i).obj I.toModules))
    (hG : ∃ G : X.Modules, RingedSpace.IsCoherent X.toRingedSpace G ∧
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = T ∧
      (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
        ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G, a • v = 0) ∧
      (∃ inst : Module (X.residueField ξ)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G),
        (∀ (a : X.presheaf.stalk ξ)
          (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G),
          a • v = (X.residue ξ) a • v) ∧
        Module.finrank (X.residueField ξ)
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G) = 1) ∧
      P G) :
    ∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F →
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆ T → P F := by
  sorry

end AlgebraicGeometry.Scheme.Modules
