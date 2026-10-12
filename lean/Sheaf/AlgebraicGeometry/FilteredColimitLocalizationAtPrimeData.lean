module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The localization colimit construction required for the filtered-colimit theorem.

The proof follows the fraction construction for Tag 037D: induced maps between the
localizations at contracted primes form a functor, and the canonical localization of
the colimit is its colimit.  The detailed fraction and filteredness argument is split
into this intermediate statement for independent formalization.
(blueprint: lem-weil-pbc-filtered-colimit-localization-at-prime-data)
The proof is the standard fraction construction: represent numerators and denominators
at a common filtered stage, lift equality witnesses to a later stage, and apply the
universal property of the filtered colimit. -/
theorem filteredColimitLocalizationAtPrime_data
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (p : Ideal ((colimit F : CommRingCat) : Type v)) [hp : p.IsPrime] :
    let ι : ∀ i : I, (F.obj i) ⟶ colimit F := fun i => colimit.ι F i
    let pᵢ : ∀ i : I, Ideal ((F.obj i : CommRingCat) : Type v) :=
      fun i => Ideal.comap (ι i).hom p
    ∃ (D : I ⥤ CommRingCat.{v})
      (hD : ∀ i : I, D.obj i = CommRingCat.of (Localization.AtPrime (pᵢ i))),
      (∀ (i j : I) (a : i ⟶ j),
        CommRingCat.ofHom (algebraMap (F.obj i) (Localization.AtPrime (pᵢ i))) ≫
            eqToHom (hD i).symm ≫ D.map a =
          F.map a ≫
            CommRingCat.ofHom (algebraMap (F.obj j) (Localization.AtPrime (pᵢ j))) ≫
            eqToHom (hD j).symm) ∧
      ∃ (c : Cocone D) (hc : c.pt = CommRingCat.of (Localization.AtPrime p)),
        (∀ i : I,
          CommRingCat.ofHom (algebraMap (F.obj i) (Localization.AtPrime (pᵢ i))) ≫
              eqToHom (hD i).symm ≫ c.ι.app i ≫ eqToHom hc =
            ι i ≫ CommRingCat.ofHom
              (algebraMap ((colimit F : CommRingCat) : Type v)
                (Localization.AtPrime p))) ∧
        Nonempty (IsColimit c) := by
  sorry

end AlgebraicGeometry
