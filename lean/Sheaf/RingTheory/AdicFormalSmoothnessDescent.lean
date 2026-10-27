module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.FormallySmoothAdicCompleteSourceTarget
import WeilConjectures.RingTheory.FormallySmoothCompleteLocalRegular
import WeilConjectures.RingTheory.FormallySmoothAdicFlat
import WeilConjectures.RingTheory.RegularPermanence
import WeilConjectures.RingTheory.GRing
import Sheaf.RingTheory.GeometricallyRegularLocalFieldAdicSmooth
import WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiber

/-!
# Adic formal smoothness through a smooth complete local map

Source: Stacks Project, More on Algebra, Tags 07PM, 07NT and 07ED; and
Geometry of Algebraic Stacks, Tag 0DZS.
(blueprint: lem-sfb-adic-formal-smoothness-descent)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- For local homomorphisms `R → C → H` of commutative Noetherian local rings,
with `C` and `H` complete for their maximal-ideal adic topologies, adic formal
smoothness of `R → C` is equivalent to adic formal smoothness of `R → H` when
`C → H` is itself adically formally smooth. No completeness of `R` or residue
field separability is assumed.

Source: Stacks Project, More on Algebra, Tags 07PM, 07NT and 07ED; and
Geometry of Algebraic Stacks, Tag 0DZS, second paragraph.
(blueprint: lem-sfb-adic-formal-smoothness-descent)

Proof, following the five steps of the node:
1. For ascent, let `alpha : R → D`, `J^2 = 0`, and `b : H → D/J` give a
   square-zero lifting problem, with `b` killing `m_H^n`. Locality of `g`
   implies that `b g` kills `m_C^n`. Apply
   def-weil-pbc-formally-smooth-adic to `C/R` to obtain `a : C → D` lifting
   `b g` and extending `alpha`. Give `D` its `C`-algebra structure by `a`.
   Applying the same definition to `H/C` lifts `b` to a `C`-algebra map,
   which extends `alpha`, proving the forward implication.
2. For descent, set `A` equal to the maximal-ideal completion of `R`.
   lem-weil-pbc-adic-completion-noetherian,
   lem-weil-pbc-local-completion-local-ring and
   lem-weil-pbc-adic-completion-mod-ideal make `A` complete Noetherian local
   with maximal ideal `m_R A`. Locality gives compatible quotient maps from
   `A` to the completions of `C` and `H`; completeness identifies these with
   `C` and `H`. This gives local maps `i : A → C` and `h : A → H` with
   `g i = h`, since their coordinates in every quotient of `H` agree.
   lem-weil-pbc-fs-adic-complete-source-target and the completion
   identification show that `h` is adically formally smooth.
3. By lem-weil-pbc-formally-smooth-complete-local-regular, `h` is regular.
   By lem-weil-pbc-fs-adic-local-flat, `g` is flat; by
   lem-weil-pbc-flat-local-hom-faithfully-flat, it is surjective on spectra.
   Apply lem-weil-pbc-regular-permanence to `A → C → H` to deduce that
   `i` is regular.
4. By def-weil-pbc-g-ring, the closed fibre `B = C/m_A C` is Noetherian
   and geometrically regular over `k = A/m_A`, and `i` is flat. Since
   `m_A C` is contained in `m_C`, `B` is local. Apply
   lem-sfb-geometrically-regular-local-field-adic-smooth to obtain adic
   formal smoothness of `B/k`, with no residue separability hypothesis.
   lem-weil-pbc-flat-formally-smooth-closed-fibre-adic now gives adic formal
   smoothness of `i : A → C`.
5. Return to a square-zero lifting problem `alpha : R → D`, `b : C → D/J`
   for `f`, where `b` kills `m_C^n`. Locality gives
   `alpha(m_R^n) ⊆ J`, hence `alpha(m_R^(2*n)) = 0`. Factor `alpha`
   through `R/m_R^(2*n)` and the corresponding coordinate of `A` to get
   `alphaHat : A → D` extending `alpha`. By
   lem-weil-pbc-adic-completion-mod-power it kills `m_A^(2*n)`.
   Also `b i` kills `m_A^n`. The maps `q alphaHat` and `b i` agree on `R`
   and factor through `A/m_A^(2*n) = R/m_R^(2*n)`, hence agree on `A`.
   The formal smoothness of `i` supplies an `A`-algebra lift `C → D`,
   whose restriction to `R` is `alpha`. This is the required lift by
   def-weil-pbc-formally-smooth-adic, and proves descent.
-/
theorem formallySmoothAdic_iff_of_smoothCompleteLocalMap
    (R : Type u) (C : Type v) (H : Type w)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    [CommRing H] [IsLocalRing H] [IsNoetherianRing H]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    [IsAdicComplete (IsLocalRing.maximalIdeal H) H]
    (f : R →+* C) [IsLocalHom f]
    (g : C →+* H) [IsLocalHom g] :
    @FormallySmoothAdic C H _ _ g.toAlgebra
        (IsLocalRing.maximalIdeal H) →
      (@FormallySmoothAdic R C _ _ f.toAlgebra
        (IsLocalRing.maximalIdeal C) ↔
        @FormallySmoothAdic R H _ _ (g.comp f).toAlgebra
          (IsLocalRing.maximalIdeal H)) := by
  sorry

end Algebra
