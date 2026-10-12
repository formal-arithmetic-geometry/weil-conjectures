module

public import Sheaf.RingTheory.GRing
import Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange
import Sheaf.RingTheory.FlatPermanence
import Sheaf.RingTheory.GeometricallyRegularDescent

/-!
# Permanence of regular ring maps

Source: Stacks Project, More on Algebra, Lemma Tag 07NT
(blueprint: lem-weil-pbc-regular-permanence).
-/

@[expose] public section

universe u v w

namespace RingHom

/-- Regularity descends along a flat map inducing a surjection on spectra.
Source: Stacks Project, More on Algebra, Lemma Tag 07NT; proof via Algebra Lemmas 039V and 07NH
(blueprint: lem-weil-pbc-regular-permanence).

Proof: Since `B → C` is flat and its prime-spectrum map is surjective, it is faithfully flat.
Flat-permanence descends flatness of `A → B` from the regular composite. For each prime of `A`,
flat base change preserves flatness and spectrum-surjectivity, making the induced map on fibres
faithfully flat. Geometric regularity and Noetherianity descend along this map, so every fibre
of `A → B` is geometrically regular and Noetherian, hence `A → B` is regular.
-/
theorem isRegular_of_isRegular_comp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hcomp : (algebraMap A C).IsRegular)
    (hflat : (algebraMap B C).Flat)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B C))) :
    (algebraMap A B).IsRegular := by
  sorry

end RingHom
