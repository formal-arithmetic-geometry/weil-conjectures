/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.CategoryTheory.Groupoid
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.AlgebraicGeometry.FiniteLocallyFreeNormCharts
import Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm

/-!
# Polynomial source norms are invariant under an affine groupoid

Source: Stacks Project, Groupoids, Tag 03BH, `lemma-determinant-trick`, applied after
adjoining a polynomial coordinate as in `lemma-integral-over-invariants`; Exercises,
Tag 02DV(1),(3) (blueprint: lem-a1-affine-groupoid-polynomial-norm-invariant).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The source norm of the target image of a polynomial has invariant coefficients.
The hypothesis `hgroupoid` says precisely that the indicated scheme maps define a
functorial groupoid on test points: its hom sets are identified with the arrows having
the specified source and target, and identity, inverse and composition are the given
scheme maps. Naturality follows because all these operations are induced by scheme maps.
The variable `Q` is the norm section, specified by its finite free affine chart formula
`hQ`. This characterizes the glued norm uniquely, rather than using `Algebra.norm` on
a possibly nonfree global module. Existence is supplied by the norm-charts dependency
applied to the polynomial-coordinate source morphism. Thus quantifying over `Q` and
its chart formula asserts invariance of the specified norm, with no choice of a norm map.

Source: Stacks Project, Tag 03BH and `lemma-integral-over-invariants`, second paragraph;
Tag 02DV(1),(3) (blueprint: lem-a1-affine-groupoid-polynomial-norm-invariant).

Proof plan:
1. Adjoin one common polynomial coordinate to the affine object and arrow schemes.
   All groupoid operations extend with that coordinate fixed. Finite local freeness
   survives base change, and the rank may vary on the original local charts.
2. Apply `lem-a1-affine-groupoid-invariant-norm` to this groupoid and to `F`.
   Its norm is the glued local determinant specified by `hQ`, by uniqueness of gluing.
   Hence the source and target images of `Q` are equal.
3. The two polynomial maps act coefficientwise. Their equality says exactly that
   every coefficient of `Q` lies in the equalizer of the original source and target
   ring maps, namely that `Q` belongs to `C[T]`.
-/
theorem affine_groupoid_polynomial_norm_invariant
    (A B : CommRingCat.{u}) (s t : Spec B ⟶ Spec A)
    (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]
    (hgroupoid : ∀ H : Scheme.{u},
      ∃ (G : Groupoid.{u} (H ⟶ Spec A))
        (φ : ∀ x y : H ⟶ Spec A,
          @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver x y ≃
            {r : H ⟶ Spec B // r ≫ s = x ∧ r ≫ t = y}),
        (∀ x : H ⟶ Spec A,
          (φ x x (@CategoryStruct.id _ G.toCategory.toCategoryStruct x)).val = x ≫ e) ∧
        (∀ (x y : H ⟶ Spec A)
          (f : @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver x y),
          (φ y x (@Groupoid.inv _ G x y f)).val = (φ x y f).val ≫ i) ∧
        (∀ (x y z : H ⟶ Spec A)
          (f : @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver x y)
          (g : @Quiver.Hom _ G.toCategory.toCategoryStruct.toQuiver y z),
          (φ x z (@CategoryStruct.comp _ G.toCategory.toCategoryStruct x y z f g)).val =
            pullback.lift (φ y z g).val (φ x y f).val
              ((φ y z g).property.1.trans (φ x y f).property.2.symm) ≫ c))
    (F Q : Polynomial A)
    (hQ : ∀ x : Spec (CommRingCat.of (Polynomial A)),
      ∃ V : (Spec (CommRingCat.of (Polynomial A))).Opens,
        x ∈ V ∧ IsAffineOpen V ∧
        @Module.Free Γ(Spec (CommRingCat.of (Polynomial A)), V)
          Γ(Spec (CommRingCat.of (Polynomial B)),
            Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (Spec.homEquiv s).hom)) ⁻¹ᵁ V)
          _ _ ((Spec.map (CommRingCat.ofHom
            (Polynomial.mapRingHom (Spec.homEquiv s).hom))).app V).hom.toAlgebra.toModule ∧
        @Module.Finite Γ(Spec (CommRingCat.of (Polynomial A)), V)
          Γ(Spec (CommRingCat.of (Polynomial B)),
            Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (Spec.homEquiv s).hom)) ⁻¹ᵁ V)
          _ _ ((Spec.map (CommRingCat.ofHom
            (Polynomial.mapRingHom (Spec.homEquiv s).hom))).app V).hom.toAlgebra.toModule ∧
        (Spec (CommRingCat.of (Polynomial A))).presheaf.map
            (homOfLE (le_top : V ≤ ⊤)).op
            ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).inv Q) =
          @Algebra.norm Γ(Spec (CommRingCat.of (Polynomial A)), V)
            Γ(Spec (CommRingCat.of (Polynomial B)),
              Spec.map (CommRingCat.ofHom
                (Polynomial.mapRingHom (Spec.homEquiv s).hom)) ⁻¹ᵁ V)
            _ _ ((Spec.map (CommRingCat.ofHom
              (Polynomial.mapRingHom (Spec.homEquiv s).hom))).app V).hom.toAlgebra
            ((Spec (CommRingCat.of (Polynomial B))).presheaf.map
              (homOfLE le_top).op
              ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial B))).inv
                (Polynomial.map (Spec.homEquiv t).hom F)))) :
    Polynomial.map (Spec.homEquiv s).hom Q = Polynomial.map (Spec.homEquiv t).hom Q := by
  sorry

end AlgebraicGeometry
