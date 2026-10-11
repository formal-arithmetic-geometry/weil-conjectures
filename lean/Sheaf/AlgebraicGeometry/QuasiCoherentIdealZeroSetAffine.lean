/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Zero sets of quasi-coherent ideal sheaves on affine opens

Source: Stacks Project, Schemes, Example 01HM and Lemma 01IN
(blueprint: lem-weil-pbc-quasi-coherent-ideal-zero-set-affine).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The stalk inclusion of a quasi-coherent ideal is injective. On an affine open it is
surjective exactly when the ideal of sections is not contained in the prime of the point.
Thus the set of points where the stalk ideal is proper is locally the ordinary zero locus,
is closed, and equals the image of every closed immersion with this kernel ideal sheaf.
Here `K : X.IdealSheafData` is the compatible affine-local encoding of a quasi-coherent
ideal sheaf, whose actual submodule sheaf and inclusion are `K.toModules` and `K.toModulesι`.
Surjectivity means that the image ideal is the whole stalk ring, without choosing an
identification of the module stalk of the structure sheaf with its ring stalk.

Source: Stacks Project, Schemes, Example 01HM, Lemmas 01HP and 01IN
(blueprint: lem-weil-pbc-quasi-coherent-ideal-zero-set-affine).

Proof:
1. Transport the ideal to `Spec Γ(X,U)` by lem-weil-pbc-affine-open-spec-points and
   lem-weil-pbc-module-restriction-open-immersion-colimits. Quasi-coherence is preserved,
   and cofinality of neighbourhoods identifies the stalks (def-weil-pbc-module-stalk).
2. The inclusion is injective on stalks by lem-weil-pbc-module-stalk-exact; its linear
   image is an ideal in the local ring.
3. By lem-weil-pbc-affine-tilde-gamma-adjunction and lem-weil-pbc-spec-module-tilde-sections,
   the ideal is the tilde of its sections. By lem-weil-pbc-spec-tilde-stalk-localization,
   its stalk image consists of fractions a/s with a in the ideal and s outside the prime;
   the ring germ is a localization by lem-weil-pbc-spec-domain-stalks-function-field.
4. An ideal section outside the prime becomes a unit, so the stalk ideal is the whole
   ring. Conversely, if 1 = a/s, the localization equality gives t outside the prime
   with ta = ts; primality shows ta is an ideal section outside the prime. This gives
   the equivalence and the affine zero-locus equality.
5. A closed immersion with this ideal exists by
   lem-weil-pbc-quasi-coherent-ideal-closed-subscheme. Its image on every affine open is
   the same zero locus by lem-weil-pbc-closed-immersion-image-zero-locus. Affine opens
   cover the scheme, hence its closed image equals the set of proper stalk ideals. -/
theorem quasi_coherent_ideal_zero_set_affine (X : Scheme.{u}) (K : X.IdealSheafData) :
    (∀ x : X, Function.Injective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom) ∧
    (∀ (U : X.affineOpens) (x : U.1),
      Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x.1).map K.toModulesι).hom ↔
      ¬ K.ideal U ≤ (U.2.primeIdealOf x).asIdeal) ∧
    (∀ U : X.affineOpens,
      {x : X | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} ∩ U.1 =
      U.2.fromSpec '' {p : PrimeSpectrum Γ(X, U.1) | K.ideal U ≤ p.asIdeal}) ∧
    IsClosed {x : X | ¬ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} ∧
    (∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i], i.ker = K →
      Set.range i = {x : X | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom}) := by
  sorry

end AlgebraicGeometry.Scheme
