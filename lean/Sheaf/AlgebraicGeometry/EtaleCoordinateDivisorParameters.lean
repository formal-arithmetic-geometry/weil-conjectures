module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Marked coordinate divisor parameters under etale pullback

Source: Stacks Project, Tags 07QP, 0AH0, 00U4 and 00KU; ILO, Travaux de Gabber,
Expose VIII 4.1.6 and 4.1.8, pp. 118--119
(blueprint: lem-trf-etale-coordinate-divisor-parameters).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical map from affine functions to the stalk after the given morphism.
Source: Stacks 00U4, local maps of etale morphisms
(blueprint: lem-trf-etale-coordinate-divisor-parameters). -/
def etaleCoordinateGermMap {C : Type u} [CommRing C]
    {W : Scheme.{u}} (h : W ⟶ Spec (.of C)) (w : W) : C →+* W.presheaf.stalk w :=
  (h.stalkMap w).hom.comp (StructureSheaf.toStalk C (h w)).hom

open Classical in
/-- Products of marked local coordinate parameters define normal crossings Cartier divisors,
with the same parameter positions and geometric branches after every etale pullback.
The displayed ideal sheaf `D` is exactly `V(P)` with `P` the finite coordinate product.
The strict-local clause quantifies over every residue separable closure and every universal
pointed-etale colimit presentation, in any universe containing the stalk. Quotient by the
radical of the equation is the reduction of the strict-local divisor ring. The equivalence
with the finite vanishing index set states its exact finite number of minimal primes,
including zero when the equation is a unit.

Source: Stacks 07QP, 0AH0, 00U4, 00KU; ILO VIII 4.1.6, 4.1.8, pp. 118--119
(blueprint: lem-trf-etale-coordinate-divisor-parameters).

Proof:
1. Spec C is regular and locally Noetherian. Apply
   lem-trf-etale-coordinate-intersection-geometry to the list with a final unit appended.
   This works also for r=0. It gives regularity and local Noetherianity of W, transport
   of every full parameter system, and the same vanishing indices. A local map reflects
   units, so these are precisely the nonunit indices, with the same distinct positions.
2. Split the product into the vanishing indices and their complement. Every complementary
   factor is a unit, giving the displayed unit times the marked parameter product.
3. Permute each marked parameter to the first position. By
   lem-weil-pbc-regular-local-generators-regular-sequence and
   def-weil-pbc-regular-sequence its multiplication is injective. Composing these maps
   and multiplying by the complementary unit proves stalkwise injectivity.
4. This implies affine injectivity: if P*b=0 and b is nonzero, choose a maximal ideal
   containing Ann(b). Vanishing of b in that localization gives s outside the maximal
   ideal with s*b=0, a contradiction. The zero ring case is immediate.
5. Pullback replaces the principal equation by its image. The affine injectivity gives
   def-nagata-effective-cartier-ideal; the local products of distinct parameters give
   def-trf-normal-crossings-divisor using the identity neighbourhood.
6. Apply lem-trf-parameter-product-strict-local-branches to each stalk and its distinct
   marked parameters. The complementary unit does not change the equation ideal. The
   lemma identifies the reduced strict-local quotient's minimal primes with the marked
   parameters. Their number is the base vanishing count, at most r, independently of h.
   With no marked parameters the equation is a unit and the quotient is zero. If r=0,
   the global product is 1 and the divisor and all its pullbacks are empty.
-/
theorem etale_coordinate_divisor_parameters
    {C : Type u} [CommRing C] [IsRegularRing C]
    (r : ℕ) (z : Fin r → C)
    (hcoord : ∀ y : Spec (.of C),
      ∃ t : List ((Spec (.of C)).presheaf.stalk y),
        IsLocalRing.IsRegularSystemOfParameters t ∧
        ∃ f : {j : Fin r // ¬ IsUnit ((StructureSheaf.toStalk C y).hom (z j))} →
            Fin t.length,
          Function.Injective f ∧
          ∀ j, t.get (f j) = (StructureSheaf.toStalk C y).hom (z j))
    (D : (Spec (.of C)).IdealSheafData)
    (hD : D = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {∏ j : Fin r, z j}).map (Scheme.ΓSpecIso (.of C)).inv.hom)) :
    Function.Injective (fun a : C ↦ (∏ j : Fin r, z j) * a) ∧
    (∀ (W : Scheme.{u}) (h : W ⟶ Spec (.of C)), Etale h →
      IsRegularScheme W ∧
      (∀ w : W,
        ∃ hN : IsNoetherianRing (W.presheaf.stalk w),
          (∀ t : List ((Spec (.of C)).presheaf.stalk (h w)),
            IsLocalRing.IsRegularSystemOfParameters t →
            @IsLocalRing.IsRegularSystemOfParameters (W.presheaf.stalk w) _ _ hN
              (t.map (h.stalkMap w).hom)) ∧
          (∀ j : Fin r,
            (¬ IsUnit (etaleCoordinateGermMap h w (z j))) ↔
              ¬ IsUnit ((StructureSheaf.toStalk C (h w)).hom (z j))) ∧
          (∀ (t : List ((Spec (.of C)).presheaf.stalk (h w)))
              (f : {j : Fin r //
                ¬ IsUnit ((StructureSheaf.toStalk C (h w)).hom (z j))} → Fin t.length),
            IsLocalRing.IsRegularSystemOfParameters t → Function.Injective f →
            (∀ j, t.get (f j) = (StructureSheaf.toStalk C (h w)).hom (z j)) →
            ∀ j, (t.map (h.stalkMap w).hom).get
                (Fin.cast (List.length_map (h.stalkMap w).hom).symm (f j)) =
              etaleCoordinateGermMap h w (z j)) ∧
          (∃ v : (W.presheaf.stalk w)ˣ,
            etaleCoordinateGermMap h w (∏ j : Fin r, z j) =
              (v : W.presheaf.stalk w) *
                ∏ j : {j : Fin r //
                    ¬ IsUnit ((StructureSheaf.toStalk C (h w)).hom (z j))},
                  etaleCoordinateGermMap h w (z j)) ∧
          Function.Injective (fun a : W.presheaf.stalk w ↦
            etaleCoordinateGermMap h w (∏ j : Fin r, z j) * a)) ∧
      (D.comap h).IsInvertible ∧ (D.comap h).IsNormalCrossingsDivisor ∧
      (∀ (w : W) (K H : Type (max u v)) [Field K]
          [Algebra (IsLocalRing.ResidueField (W.presheaf.stalk w)) K]
          [IsSepClosure (IsLocalRing.ResidueField (W.presheaf.stalk w)) K]
          [Algebra (W.presheaf.stalk w) K]
          [IsScalarTower (W.presheaf.stalk w)
            (IsLocalRing.ResidueField (W.presheaf.stalk w)) K]
          [CommRing H] [Algebra (W.presheaf.stalk w) H],
        Algebra.StrictHenselizationPresentationIn.{u, v} (W.presheaf.stalk w) K H →
        Nonempty ((minimalPrimes (H ⧸
          (Ideal.span {algebraMap (W.presheaf.stalk w) H
            (etaleCoordinateGermMap h w (∏ j : Fin r, z j))}).radical)) ≃
          {j : Fin r // ¬ IsUnit ((StructureSheaf.toStalk C (h w)).hom (z j))})) ∧
      (∀ w : W,
        Nat.card {j : Fin r //
          ¬ IsUnit ((StructureSheaf.toStalk C (h w)).hom (z j))} ≤ r) ∧
      (r = 0 → (∏ j : Fin r, z j) = 1 ∧ IsEmpty (D.comap h).subscheme)) := by
  sorry

end AlgebraicGeometry
