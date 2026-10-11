module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open AlgebraicGeometry

/-- For a finite extension `K` of the residue field at a point of a quasi-separated scheme `X`,
the composite `Spec K ⟶ X` is quasi-compact and quasi-separated and factors through an integral
morphism from an integral normal scheme whose generic point has residue field `K`.

Source: Stacks Project, Morphisms Lemmas 035H, 035I, 035L and Etale Cohomology Lemma 09Z6
(blueprint: lem-weil-pbc-normalization-in-residue-field-extension). The proof first shows that
the composite from the affine field scheme is quasi-compact and quasi-separated. It applies
relative normalization to obtain an integral factorization with dominant map and uses
integrality of the source to make the normalization integral. On affine opens through the
chosen point, the coordinate ring is the integral closure of the corresponding domain in K;
finite-extension normality gives a normal domain with fraction field K. The normalization
normal-stalks theorem gives integrally closed domain stalks. Dominance and sobriety identify
the image of the unique point with the generic point, and the affine residue-field
calculation identifies its residue field with K.
-/
theorem normalization_in_finite_residue_field_extension
    (X : Scheme.{u}) [QuasiSeparatedSpace X] (x : X) (K : Type u) [Field K]
    [Algebra (X.residueField x) K] [Module.Finite (X.residueField x) K] :
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
        X.fromSpecResidueField x) ∧
      QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
        X.fromSpecResidueField x) ∧
      ∃ (Y : Scheme.{u}) (ν : Y ⟶ X) (g : Spec (.of K) ⟶ Y),
        IsIntegralHom ν ∧
          Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
              X.fromSpecResidueField x = g ≫ ν ∧
          IsIntegral Y ∧
          (∀ y : Y,
            IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
          ∃ η : Y, IsGenericPoint η Set.univ ∧
            g (IsLocalRing.closedPoint K) = η ∧
            IsIso (g.residueFieldMap (IsLocalRing.closedPoint K)) := by
  sorry
