module

public import Sheaf.Paper.OrgogozoInductionData
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Generic-point closure gives an alteration of an image stratum

Source: Orgogozo, Modifications et cycles proches sur une base générale, Lemma 3.2.1
proof, p. 8 (blueprint: lem-trf-closed-image-generic-alteration).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Orgogozo

/-- The closure of a point above the generic point of an integral closed image stratum
produces an integral alteration of that stratum.

Source: Orgogozo, Modifications et cycles proches sur une base générale, Lemma 3.2.1
proof, p. 8 (blueprint: lem-trf-closed-image-generic-alteration).

Proof:
1. Choose a closed point over the generic point of `Z` with finite residue extension,
   using properness of the fibre and the finite-type closed-point theorem.
2. Give its closure in `Y` the reduced induced closed subscheme structure. It is integral,
   and the reduced-source factorization lemma gives `a : W ⟶ Z` with `a ≫ i = j ≫ h`.
3. The composite `j ≫ h` is proper; the factorization square is Cartesian because `i` is
   a closed immersion, so `a` is proper by base change.
4. The generic fibre of `a` consists of the chosen point and is finite. Generic finiteness
   for a proper morphism gives a dense open `U` of `Z` over which `a` is finite.
5. The proper image of `a` is closed and contains the generic point of the integral scheme
   `Z`, hence `a` is surjective. These clauses imply `IsAlteration a`.
The argument uses the statement dependencies and the proof dependencies recorded by the DAG.
-/
theorem exists_closed_image_generic_alteration
    {X Y : Scheme.{u}} [IsReduced X] [IsNoetherian X]
    [IsReduced Y] [IsNoetherian Y]
    (h : Y ⟶ X) [IsProper h]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (himage : Set.range i.base ⊆ Set.range h.base) :
    ∃ (W : Scheme.{u}) (j : W ⟶ Y),
      IsClosedImmersion j ∧ IsIntegral W ∧
      ∃ (a : W ⟶ Z),
        a ≫ i = j ≫ h ∧
        IsProper a ∧
        Surjective a ∧
        (∃ U : Z.Opens, Dense (U : Set Z) ∧
          IsFinite (pullback.snd a U.ι)) ∧
        IsAlteration a := by
  sorry

end AlgebraicGeometry.Orgogozo

end
