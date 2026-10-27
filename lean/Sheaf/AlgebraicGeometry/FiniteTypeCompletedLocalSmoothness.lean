module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.RingTheory.FormallySmoothAdic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.FormallySmoothAdicCompletion
import WeilConjectures.AlgebraicGeometry.SmoothAtPrimeArtinianLifting
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!+# Smoothness near a prime detected by the completed local ring

Source: Stacks Project, More on Algebra, Tags 07VH and 07ED, equivalence (1) and (2).
(blueprint: lem-sfb-finite-type-completed-local-smoothness)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Smoothness on an open neighbourhood of a prime over the closed point of a Noetherian
local base is equivalent to adic formal smoothness of its completed local ring.
The ideal on the right is the extension of the maximal ideal of `B_q`; it is precisely
the maximal ideal of its completion by `AdicCompletion.maximalIdeal_eq_map`.

Source: Stacks Project, More on Algebra, Tags 07VH and 07ED, equivalence (1) and (2).
(blueprint: lem-sfb-finite-type-completed-local-smoothness)

Proof:
1. Put `T = B_q` and `n = maximalIdeal T`. Localization at a prime makes `T` local
   with `n = qT` (def-weil-pbc-localization-at-prime). Finite type over Noetherian
   makes `B` Noetherian (lem-weil-pbc-finite-type-algebra-noetherian), and localization
   makes `T` Noetherian (lem-weil-pbc-localization-noetherian). Thus `n` is finitely
   generated (def-weil-pbc-noetherian-ring). Its completion `C` is local with
   maximal ideal `nC` (lem-weil-pbc-local-completion-local-ring).
2. Given a smooth open neighbourhood `W`, take a basic open `D(g)` containing `q`
   inside `W` (lem-weil-pbc-spec-localization-away-basic-open). Restrict smoothness
   to it (lem-weil-pbc-smooth-restrict-open-subschemes). The principal localization
   open immersion identifies `Spec B_g` with `D(g)`
   (lem-weil-pbc-principal-localization-open-immersion, def-weil-open-immersion).
   Functoriality of Spec (def-weil-affine-spectrum) and invariance of smoothness
   under isomorphisms identify its structural morphism with `Spec (R -> B_g)`.
   The affine comparison (lem-weil-pbc-smooth-ring-map-iff-smooth-affine) therefore
   makes `R -> B_g` a smooth ring map.
3. To lift an `R`-algebra map `T -> D/J` through a square-zero ideal `J`, restrict
   it to `B_g` and lift there (lem-weil-pbc-smooth-ring-map-square-zero-lifting).
   The ring `T` is obtained by subsequently inverting the images of `B \ q`.
   Localization lifts across square-zero ideals
   (lem-weil-pbc-localization-square-zero-lifting), giving the required lift from `T`.
   In particular this solves every continuous test (def-weil-pbc-formally-smooth-adic).
4. Completion preserves this adic lifting property for the finitely generated `n`
   (lem-weil-pbc-fs-adic-completion). Since `nC` is the maximal ideal, this proves
   the forward implication.
5. Conversely take a compatible Artinian small-extension test `A' -> A` at `q`
   (lem-weil-pbc-smooth-at-prime-artinian-lifting). The given map `B -> A` inverts
   every element outside `q`, so extends to `T -> A`. The maximal ideal of `A` is
   nilpotent (lem-weil-pbc-artinian-local-noetherian-nilpotent), so this map factors
   through `T/n^N` for some positive `N`. The completion projection onto `T/n^N`
   is surjective, has kernel `(nC)^N`, and restricts on `T` to the quotient map
   (lem-weil-pbc-adic-completion-mod-power). Its composite gives a continuous
   `R`-algebra map `C -> A` extending the map from `T`.
6. The length-one kernel `J` of `A' -> A` is killed by the maximal ideal of `A'`;
   it lies in that maximal ideal because `A` is nonzero, so `J^2 = 0`.
   Identify `A'/J` with `A` and apply adic formal smoothness of `C`
   (def-weil-pbc-formally-smooth-adic). Compose its lift `C -> A'` with `B -> T -> C`.
   This lifts the original test and respects the specified map from `R`.
   The Artinian lifting criterion (lem-weil-pbc-smooth-at-prime-artinian-lifting)
   supplies the smooth open neighbourhood, proving the reverse implication.
-/
theorem smooth_on_open_iff_formallySmoothAdic_completion
    {R B : Type u} [CommRing R] [CommRing B] [IsNoetherianRing R] [IsLocalRing R]
    [Algebra R B] [Algebra.FiniteType R B] (q : Ideal B) [q.IsPrime]
    (hq : Ideal.comap (algebraMap R B) q = IsLocalRing.maximalIdeal R) :
    (∃ W : (Spec (CommRingCat.of B)).Opens,
      (⟨q, inferInstance⟩ : PrimeSpectrum B) ∈ W ∧
        Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)))) ↔
    Algebra.FormallySmoothAdic R
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q))
      ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
            (Localization.AtPrime q)))) := by
  sorry

end AlgebraicGeometry
