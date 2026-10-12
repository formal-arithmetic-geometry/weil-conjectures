/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import Sheaf.RingTheory.QuasiFiniteAtPrime
import Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen

/-!
# A quasi-finite affine morphism embeds in a finite affine morphism

Source: Stacks Project, Morphisms of Schemes, Lemma Tag 03GU, via Algebra, Lemma Tag 00QB
(blueprint: lem-weil-pbc-quasi-finite-affine-open-in-finite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-finite morphism between affine schemes factors as an open immersion into an
 affine scheme finite over the target. Source: Stacks Project, Morphisms of Schemes,
 Lemma Tag 03GU (blueprint: lem-weil-pbc-quasi-finite-affine-open-in-finite).

Proof (the node's five steps):
1. Set R = Γ(X, ⊤), S = Γ(Y, ⊤), and let φ : R → S be induced by f. The affine-chart
   isomorphisms identify f with Spec φ, by `lem-weil-pbc-affine-open-spec-points` and
   `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`.
2. Quasi-finiteness supplies finite type and isolation of every point in its fibre.
   Apply `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs` to the full affine
   opens: φ is of finite type and quasi-finite at every prime of S. The set-theoretic and
   scheme-theoretic fibres agree topologically, by `def-pc-scheme-fibre`.
3. Apply `lem-weil-pbc-quasi-finite-ring-map-integral-closure-open`, clause (3), to φ.
   It gives an R-subalgebra S'' of the integral closure of R in S, finite as an R-module,
   with Spec S → Spec S'' an open immersion. Write e : S'' → S for the inclusion and
   ψ : R → S'' for the corestriction, so φ = e ∘ ψ.
4. Set Z = Spec S''. Transport Spec e and Spec ψ along the affine-chart isomorphisms
   to obtain j : Y → Z and π : Z → X. Z is affine, j is an open immersion, and
   functoriality of Spec gives j ≫ π = f.
5. By `lem-weil-pbc-spec-finite-ring-map-finite`, Spec ψ is finite. The map π is its
   base change along the affine-chart isomorphism X → Spec R. Finiteness is preserved
   by base change (`lem-weil-pbc-finite-morphism-permanence`, clause (a)) and by the
   resulting source isomorphism, using `def-weil-finite-integral-morphism`. -/
theorem Scheme.Hom.exists_isOpenImmersion_isFinite_of_isQuasiFinite_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (hf : f.IsQuasiFinite) :
    ∃ (Z : Scheme.{u}) (j : Y ⟶ Z) (π : Z ⟶ X),
      IsAffine Z ∧ IsOpenImmersion j ∧ IsFinite π ∧ f = j ≫ π := by
  sorry

end AlgebraicGeometry
