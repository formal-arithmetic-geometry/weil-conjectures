/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.ProjectiveFiniteGeometricFibres
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Finiteness of a projective coordinate boundary after shrinking

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-cbc`,
`lem-fin-projective-coordinate-boundary` (blueprint: lem-fin-projective-coordinate-boundary).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- After shrinking an integral Noetherian affine base to a nonempty principal open,
the reduced complement of the union of the chosen dense coordinate opens is finite.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-projective-coordinate-boundary`
(blueprint: lem-fin-projective-coordinate-boundary).

Proof:
1. Each closed affine-line complement has a radical vanishing ideal, by
   `lem-weil-pbc-reduced-induced-closed-subscheme`. Since the base is integral, the polynomial
   ring is a domain and its generic point belongs to every dense open. Choose a nonzero
   polynomial in each ideal, choosing 1 when the complement is empty.
2. Invert the product of the finitely many nonzero leading coefficients, with empty product
   1. Its principal open is nonempty. Divide each polynomial by its leading coefficient to
   make it monic. The localized base is Noetherian and the restricted scheme is projective
   by `lem-pc-projective-base-change`.
3. The union of coordinate inverse images is open. Form its reduced closed complement using
   `lem-weil-pbc-reduced-induced-closed-subscheme`. On each chart the coordinate polynomials
   vanish in every residue field of this complement, hence belong to its vanishing ideal.
   Its coordinate ring is therefore a quotient by the monic coordinate polynomials.
4. Bounded coordinate powers span that quotient as a module over the localized base. If a
   polynomial has degree zero, the quotient is zero. Tensoring with any geometric residue
   field preserves this finite spanning family. The resulting affine fibres have finitely
   many points by `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`; no geometric
   reducedness is required.
5. The finite chart cover gives finite geometric fibres globally. The reduced complement
   is a closed subscheme of a projective scheme, hence projective and quasi-compact. Apply
   `lem-fin-projective-finite-fibres` over the Noetherian localized base. -/
theorem exists_isFinite_projective_coordinate_boundary
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsIntegral (Spec (CommRingCat.of A))]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of A)) [IsProjective f]
    (ι : Type v) [Finite ι] (U : ι → Y.affineOpens)
    (hcover : (⨆ i : ι, (U i).1) = ⊤)
    (m : ι → ℕ) (hm : ∀ i, 1 ≤ m i)
    (e : ∀ i, (U i).1.toScheme ⟶
      AffineSpace (ULift.{u} (Fin (m i))) (Spec (CommRingCat.of A)))
    [he : ∀ i, IsClosedImmersion (e i)]
    (hover : ∀ i, e i ≫ AffineSpace (ULift.{u} (Fin (m i)))
      (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A) = (U i).1.ι ≫ f)
    (V : ∀ i, Fin (m i) →
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of A))).Opens)
    (hV : ∀ i r, Dense (V i r : Set
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of A))))) :
    ∃ a : A, Nonempty (PrimeSpectrum.basicOpen a) ∧
      ∃ T : TopologicalSpace.Closeds
        (pullback f (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a)) : Scheme.{u}),
        (T : Set (pullback f (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
          (PrimeSpectrum.basicOpen a)) : Scheme.{u})) =
          {x | ¬ ∃ (i : ι) (r : Fin (m i)) (y : (U i).1.toScheme),
            (U i).1.ι y = pullback.fst f
              (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
                (PrimeSpectrum.basicOpen a)) x ∧
            (e i ≫ AffineSpace.reindex
              (fun _ : ULift.{u} (Fin 1) ↦ (ULift.up r : ULift.{u} (Fin (m i))))
              (Spec (CommRingCat.of A))) y ∈ V i r} ∧
        IsFinite ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
          pullback.snd f (Scheme.Opens.ι (X := Spec (CommRingCat.of A))
            (PrimeSpectrum.basicOpen a))) := by
  sorry

end AlgebraicGeometry
