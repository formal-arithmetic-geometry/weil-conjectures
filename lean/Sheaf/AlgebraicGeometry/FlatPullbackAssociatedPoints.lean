/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimesFlatBaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Associated points under flat pullback

Source: Stacks Project, Divisors, Tag 05DB (`lemma-bourbaki`), specialized to the
relatively flat structure sheaf (blueprint: lem-trf-flat-pullback-associated-points).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- For a flat morphism with locally Noetherian target, the associated points of the
pullback of any quasi-coherent module are the images of the associated points of the
structure sheaves of fibres over its associated points. Neither finite type of `G`
nor local Noetherianity of `Y` is assumed.
Source: Stacks Project, Divisors, Tag 05DB (`lemma-bourbaki`), with `F = O_Y`
(blueprint: lem-trf-flat-pullback-associated-points).

Proof:
1. Fix `y : Y`, put `z = h y`, `A = O_{Z,z}`, `B = O_{Y,y}`, and `M = G_z`.
   Flatness gives a flat local stalk map `A → B`. A Noetherian affine neighbourhood
   of `z`, the affine-open stalk localization lemma
   (`lem-weil-pbc-affine-open-stalk-localization`), and
   `lem-weil-pbc-localization-noetherian` make `A` Noetherian. No finiteness of `M`
   or Noetherianity of `B` is used.
2. By `lem-weil-pbc-module-stalk-pullback`, the pullback stalk is `M ⊗[A] B`.
   Module isomorphisms preserve element annihilators, so the definition of associated
   points translates association at `y` into association of the maximal ideal of `B`.
   By `lem-sbc-scheme-fibre-stalk-quotient`, the fibre stalk at `h.asFiber y` is
   `C = B / m_A B`, with maximal ideal `m_B / m_A B`.
3. Apply the equality clause of `lem-weil-pbc-associated-primes-flat-base-change`
   with `R = A`, `S = B`, `N = B`. It expresses association of `m_B` in
   `M ⊗[A] B` as association in `B / p B` for some associated prime `p` of `M`.
4. If `m_B` annihilates a nonzero element of `B / p B`, every `a` outside `p`
   acts injectively on this quotient: multiplication by `a` is injective on `A / p`,
   flat tensor exactness (`lem-weil-pbc-flat-tensor-exact`) preserves this, and
   `lem-weil-pbc-tensor-over-quotient-ring` identifies the tensor with `B / p B`.
   An element of `m_A` outside `p` would map into `m_B` by locality, a contradiction.
   Thus `m_A ≤ p`; since `p` is proper in the local ring `A`, `p = m_A`.
5. Under `B → C`, the annihilator over `B` is the inverse image of the annihilator
   over `C`. Surjectivity therefore identifies `Ann_B(v) = m_B` with
   `Ann_C(v) = m_B / m_A B`. This is precisely association in the fibre structure
   sheaf, even for non-Noetherian `B` and `C`.
6. The preceding steps identify association of `y` in the pullback with association
   of `h y` in `G` and of `h.asFiber y` in the fibre structure sheaf. The fibre
   projection identifies its points with `h ⁻¹' {z}` (`def-pc-scheme-fibre`), so this
   pointwise equivalence is exactly the displayed union equality. -/
theorem associatedPoints_tensorPullback_of_flat
    {Y Z : Scheme.{u}} (h : Y ⟶ Z) [Flat h] [IsLocallyNoetherian Z]
    (G : Z.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    associatedPoints ((tensorPullback h).obj G) =
      ⋃ z ∈ associatedPoints G,
        (h.fiberι z) '' associatedPoints (SheafOfModules.unit (h.fiber z).ringCatSheaf) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
