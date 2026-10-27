module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Sheaf.RingTheory.GeometricallyRegularLocalFieldAdicSmooth
import WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiber
import WeilConjectures.RingTheory.FormallySmoothAdicCompleteSourceTarget
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.FormallySmoothCompleteLocalRegular
import WeilConjectures.RingTheory.RegularComposition
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.RegularPermanence

/-! # The local closed-fibre criterion for regularity

Source: Stacks Project, More on Algebra, Theorem Tag 0H7U (Andre), equivalence (1) and (2).
(blueprint: lem-per-g-ring-local-closed-fibre-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

/-- A local homomorphism of Noetherian local rings whose source completion map is regular
is regular exactly when it is flat with geometrically regular closed fibre.
The residue field at the maximal ideal canonically identifies with `R / maximalIdeal R`;
its `Ideal.Fiber S` canonically identifies with `S / (maximalIdeal R)S`, with the induced
residue-field action. Neither ring is assumed complete or of finite type.

Source: Stacks Project, More on Algebra, Theorem Tag 0H7U (Andre), (1) iff (2).
(blueprint: lem-per-g-ring-local-closed-fibre-criterion)

Proof:
1. Regularity gives flatness and geometric regularity of the fibre at the maximal ideal
   by `def-weil-pbc-g-ring`. Identify this fibre with `S / (maximalIdeal R)S` by
   sending `a mod m` tensored with `s` to `f(a)s mod mS`; the inverse sends the class
   of `s` to `1` tensored with `s`. These maps respect the residue-field action.
2. Conversely assume flatness and geometric regularity of the closed fibre. Locality
   puts `mS` inside the maximal ideal of `S`, so the quotient is a nonzero local ring
   by `lem-weil-pbc-quotient-local-structure`. Geometric regularity includes its
   Noetherianity. By `lem-sfb-geometrically-regular-local-field-adic-smooth`, the closed
   fibre is adically formally smooth over the residue field. Then
   `lem-weil-pbc-flat-formally-smooth-closed-fibre-adic` gives adic formal smoothness of `S/R`.
3. Pass to the canonical map between the maximal-ideal-adic completions using
   `lem-weil-pbc-fs-adic-complete-source-target`. Both completions are Noetherian
   (`lem-weil-pbc-adic-completion-noetherian`), local with maximal ideals extended
   from the original rings (`lem-weil-pbc-local-completion-local-ring`), and complete
   (`lem-weil-pbc-module-completion-complete`). The extended map is local, since it
   carries generators of the source maximal ideal into the target maximal ideal,
   and is formally smooth for the target maximal-ideal-adic topology.
4. Apply `lem-weil-pbc-formally-smooth-complete-local-regular` to obtain regularity
   of the map between the completions.
5. The source completion map is regular by hypothesis. Each fibre of the composite
   from `R` to the completion of `S` is a quotient of a localization of that
   Noetherian completion, hence Noetherian by `lem-weil-pbc-localization-noetherian`
   and `lem-weil-pbc-surjective-image-noetherian`. Thus
   `lem-weil-pbc-regular-composition` makes this composite regular.
6. On every quotient level, this composite equals the completion map of `S` after
   `f`. The latter completion map is flat and surjective on spectra by
   `lem-weil-pbc-local-completion-faithfully-flat`. Descend regularity along it using
   `lem-weil-pbc-regular-permanence` to conclude regularity of `f`.
-/
theorem isRegular_iff_flat_isGeometricallyRegular_closedFiber_of_completion
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hcompletion : (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)).IsRegular) :
    (algebraMap R S).IsRegular ↔
      (algebraMap R S).Flat ∧
        Algebra.IsGeometricallyRegular (IsLocalRing.maximalIdeal R).ResidueField
          ((IsLocalRing.maximalIdeal R).Fiber S) := by
  sorry

end RingHom
