/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-! # Finite-free preparation of the affine module Hom complex

Source: Stacks Project, Tags 064U and 0A6H, proof of clause (3)(a).
(blueprint: lem-sc-affine-finite-projective-hom-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory

/-- Prepare the ordinary module Hom complex for the finite-free sheaf Hom computation.
Source: Stacks Project, Tag 064U, proof of (3) implies (1); Tag 0A6H, clause (3)(a),
and Tag 08I5 (the Hom-complex calculation cited by Tag 0A6H).
(blueprint: lem-sc-affine-finite-projective-hom-model).

Proof:
1. Starting at the upper bound b, choose finite projective complements C^i so that
   F^b = p^b ⊕ C^b and F^(i-1) = p^(i-1) ⊕ C^i ⊕ C^(i-1) are finite free.
   Use d_p on p, identity on the repeated C^i, and zero on the last complement.
   Projection F → p has contractible kernel, giving a homotopy equivalence.
2. The good truncation l' = truncGE l a is strictly bounded below, and l → l'
   is a quasi-isomorphism because l has no cohomology below a. The bounded-above
   projective complex p is K-projective, so Hom(p,l) → Hom(p,l') is a
   quasi-isomorphism. This follows by applying Hom(p,-) to the acyclic cone:
   cocycles are maps to shifts of the cone and are nullhomotopic by K-projectivity.
   Precomposition with F → p is a homotopy equivalence on Hom complexes.
3. Set E = tilde(F), G = tilde(l'), and f = tilde(F → p). Additivity transports
   the homotopy equivalence, and exactness of tilde transports the truncation
   quasi-isomorphism; hence f is a quasi-isomorphism and Q(G) ≅ Q(tilde(l)).
4. For each degree n, only a-n ≤ i ≤ b contributes to Hom(F,l')^n. Finite-free
   Hom identifies Hom(tilde(F^i),tilde(l'^(i+n))) with the associated module Hom,
   and finite products commute with tilde. The formula d_l' h - (-1)^n h d_F
   makes these identifications a complex isomorphism. Combine it with step 2,
   exact termwise tilde, and the given e and hc to identify Q(Hom(E,G)) with
   Q(tilde(c)). No derived internal Hom computation is asserted here.

Edge cases: empty spectra and zero complexes satisfy the same product formulas;
rank-zero free terms are permitted. The coefficient representative l can be unbounded:
truncation occurs before replacing infinite Hom products by finite ones. -/
theorem affineFiniteProjectiveHomModel
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))]
    (p l : CochainComplex (ModuleCat.{u} R) ℤ)
    (b a : ℤ) (hp : p.IsStrictlyLE b) (hl : l.IsGE a)
    (hfinite : ∀ i : ℤ, Module.Finite R (p.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (p.X i))
    (c : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : ∀ n : ℤ, c.X n ≅ ModuleCat.of R (CochainComplex.HomComplex.Cochain p l n))
    (hc : ∀ n m : ℤ, c.d n m ≫ (e m).hom =
      (e n).hom ≫ ModuleCat.ofHom (CochainComplex.HomComplex.δ_hom R p l n m)) :
    let T := (@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} R)
      (SheafOfModules.{u} (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
      _ _ _ _ (tilde.functor (CommRingCat.of R))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ))
    ∃ (E G : CochainComplex (SheafOfModules.{u}
        (moduleRings (Spec (CommRingCat.of R)).toRingedSpace)) ℤ)
      (f : E ⟶ T.obj p),
      QuasiIso f ∧ E.IsStrictlyLE b ∧ G.IsStrictlyGE a ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅
        SheafOfModules.free
          (R := moduleRings (Spec (CommRingCat.of R)).toRingedSpace)
          (ULift.{u} (Fin r)))) ∧
      Nonempty (DerivedCategory.Q.obj G ≅ DerivedCategory.Q.obj (T.obj l)) ∧
      Nonempty (DerivedCategory.Q.obj
        (homComplex (R := (Spec (CommRingCat.of R)).sheaf) E G) ≅
        DerivedCategory.Q.obj (T.obj c)) := by sorry

end CategoryTheory
