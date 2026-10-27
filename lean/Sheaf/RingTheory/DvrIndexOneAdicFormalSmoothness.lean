module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
public import WeilConjectures.RingTheory.FormallySmoothAdic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiber

/-!
# Adic formal smoothness of index-one DVR extensions

Source: Stacks Project, More on Algebra, Tag 09E7,
`lemma-extension-dvrs-formally-smooth`, implication (2) to (1).
(blueprint: lem-sfb-dvr-index-one-adic-formal-smoothness)
-/

@[expose] public section

universe u v

namespace Algebra

/-- An injective local map of discrete valuation rings with ramification index one and separable
residue field extension is formally smooth for the target maximal-ideal-adic topology.
Separability is in the possibly transcendental sense; neither completeness nor finite generation
is required.

Source: Stacks Project, More on Algebra, Tag 09E7, implication (2) to (1).
(blueprint: lem-sfb-dvr-index-one-adic-formal-smoothness)

Proof plan:
1. Both DVRs are Noetherian, since every ideal is principal. Injectivity and the domain property
   of `S` make `S` torsion free over the PID `R`. Apply
   `lem-weil-pbc-pid-torsion-free-module-flat` to obtain flatness.
2. The closed fibre `S / (maximalIdeal R)S` is canonically the residue field of `S`, by the
   index-one equality, compatibly with the residue-field algebra of `R`. Its maximal ideal is
   zero. Apply `lem-sfb-separable-field-square-zero-lifting` to the separable residue extension:
   every algebra map into a square-zero quotient lifts. Thus this closed fibre is formally
   smooth for its zero-adic topology, using `def-weil-pbc-formally-smooth-adic`.
3. Apply `lem-weil-pbc-flat-formally-smooth-closed-fibre-adic` (Stacks Tag 07NQ) to the local flat
   map of Noetherian local rings and the closed-fibre formal smoothness from step 2. This yields
   the required maximal-ideal-adic formal smoothness, with no completeness or finiteness added. -/
theorem formallySmoothAdic_of_dvr_index_one
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hinj : Function.Injective (algebraMap R S))
    (hindex : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S)
    (hsep : IsSeparableExtension (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) :
    FormallySmoothAdic R S (IsLocalRing.maximalIdeal S) := by
  sorry

end Algebra
