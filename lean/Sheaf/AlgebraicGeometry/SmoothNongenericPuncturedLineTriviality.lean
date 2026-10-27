/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PuncturedCurveBranches
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

/-! # Punctured local line bundles at nongeneric smooth-fibre points

Source: EGA IV4, Proposition 21.14.3(i), first assertion, and Proposition 21.13.8(ii)
(blueprint: lem-sfb-smooth-nongeneric-punctured-line-triviality).

The conclusion is the invertible-module consequence of parafactoriality. The point
need not be closed in its fibre and its residue extension need not be finite.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every invertible module on the punctured local spectrum at a nongeneric
smooth-fibre point of local dimension at least two is trivial.

Source: EGA IV4, Proposition 21.14.3(i), first assertion, interpreted using
Proposition 21.13.8(ii).
(blueprint: lem-sfb-smooth-nongeneric-punctured-line-triviality)

Proof:
1. Apply `lem-sfb-smooth-closure-fibre-avoidance-neighbourhood` to obtain an affine
   smooth finite-presentation neighbourhood `V = Spec B` over a Noetherian normal
   domain `A`. Its closed subset `Z`, the closure of `x` in `V`, avoids every fibre
   component and has generic-fibre local codimension at least two. The stalk at
   `x` remains the original local ring. No excellence of `A` is asserted.
2. Write this stalk as `B` localized at the prime `r` corresponding to `x`.
   The opens `D(t)`, for `t` outside `r`, form a small directed neighbourhood system.
   The inverse limit of `D(t)` minus `Z` is the punctured local spectrum: under
   localization the inverse image of `V(r)` consists of the maximal prime alone.
   Check the limit on the finite principal cover coming from generators of `r`.
   These opens are quasi-compact and separated and the transitions are affine.
   By `lem-trf-invertible-affine-limit-descent`, descend `L` to one such open
   complement. Shrink `V` accordingly; the closed-pair hypotheses persist.
3. Apply `lem-sfb-normal-arithmetic-closed-pair-approximation` to this pair.
   Its arithmetic models have quasi-compact quasi-separated open complements,
   affine transitions, and the required inverse limit. Apply the same invertible
   limit descent to obtain an invertible module at an arithmetic stage. The
   normality of local completions is asserted only at these arithmetic stages.
4. At every point of the closed subset at that stage, apply
   `lem-sfb-smooth-pair-closed-fibre-local-preparation`. The auxiliary closed
   specialization in its fibre supplies the local adically formally smooth map,
   finite residue extension, dimension inequality, prime extended maximal ideal,
   and strictly larger localization prime of local dimension at least two.
   The arithmetic base has normal local completions. Thus
   `lem-sfb-formally-smooth-ramanujam-samuel-localization` trivializes invertible
   modules on each punctured stalk. By `lem-sfb-smooth-normal-ascent` the stage is
   normal, and `lem-sfb-punctured-picard-local-extension-criterion` extends the
   descended invertible module across the closed subset.
5. Tensor-pull the extension back to `V` using `def-pc-module-pullback`; it is
   invertible by the tensor formula on trivializing opens, and restricts to `L`
   on the punctured stalk. By `def-sc-invertible-module`, it is trivial on an
   open neighbourhood of `x`. Every point of `Spec` of the stalk generalizes
   `x`, so its map into `V` factors through this neighbourhood. Pull the chosen
   trivialization back to the puncture. The finite residue extension in step 4
   belongs to the auxiliary point, imposing no restriction on the original `x`. -/
theorem smooth_nongeneric_punctured_line_triviality
    {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [Smooth f] (x : X)
    (hdim : 2 ≤ ringKrullDim (X.presheaf.stalk x))
    (hng : ∀ C : Set (f.fiber (f x)),
      C ∈ irreducibleComponents (f.fiber (f x)) → ¬ IsGenericPoint (f.asFiber x) C)
    (L : (puncturedSpectrum (X.presheaf.stalk x)).toScheme.Modules)
    [L.IsInvertible] : Nonempty (L ≅ SheafOfModules.unit _) := by
  sorry

end AlgebraicGeometry
