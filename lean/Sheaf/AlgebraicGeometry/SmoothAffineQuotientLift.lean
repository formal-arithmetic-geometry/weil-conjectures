module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.GroupTheory.MonoidLocalization.Away
import WeilConjectures.RingTheory.SmoothLocalCompleteIntersection
import WeilConjectures.RingTheory.FlatModuleAtPrime
import WeilConjectures.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime
import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.SingularIdealLocalizationSmooth

/-! # Smooth affine lifts across quotient maps of the base

Source: Stacks Project, Smoothing Ring Maps, Tag 07M8, `proposition-lift-smooth`,
assertion (2), translated to affine schemes
(blueprint: lem-sfb-smooth-affine-quotient-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth affine scheme over a quotient ring has a smooth affine lift over the original
ring, with its prescribed identification over the quotient base. No nilpotence, locality,
Noetherian, or nonzero condition is required.

Source: Stacks Project, Smoothing Ring Maps, Tag 07M8, `proposition-lift-smooth` (2)
(blueprint: lem-sfb-smooth-affine-quotient-lift).

Proof:
1. Choose an affine presentation `T₀ ≅ Spec B₀`. The specified map `f₀` determines the
   `R₀`-algebra structure on `B₀`. Invariance under isomorphism and the affine smoothness
   equivalence make this a smooth algebra. Write `I = ker φ`, so `R/I ≅ R₀`.
   Uses: def-pc-scheme, def-weil-affine-spectrum,
   lem-weil-pbc-smooth-restrict-open-subschemes,
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine.
2. Smoothness gives finite presentation and flatness. Every residue-field base change
   is smooth, hence a local complete intersection, so `B₀` is syntomic over `R₀`.
   Uses: def-weil-pbc-smooth-ring-map, lem-weil-pbc-smooth-ring-map-flat,
   lem-weil-pbc-smooth-ring-map-base-change-composition,
   lem-weil-pbc-smooth-over-field-local-complete-intersection.
3. Lift `B₀` to a syntomic `R`-algebra `B` with `β : B/IB ≅ B₀` over `R₀`, using
   lem-sfb-syntomic-algebra-surjection-lift. Thus `B` is flat and finitely presented.
4. At every prime of `B` containing `IB`, identify its fibre algebra with the corresponding
   fibre of `B₀` by the quotient-tensor comparison and `β`. This fibre is smooth.
   Localized flatness and finite presentation then imply smoothness at that prime.
   Uses: lem-weil-pbc-tensor-over-quotient-ring,
   lem-weil-pbc-smooth-ring-map-base-change-composition,
   lem-pc-affine-flat-module-local-criterion,
   lem-weil-pbc-flat-smooth-fibre-smooth-at-prime, def-weil-pbc-singular-ideal.
5. For the singular ideal `H`, the preceding step gives `V(H) ∩ V(IB) = ∅`.
   The zero-locus/radical equivalence gives `H + IB = B`. Choose `h ∈ H` with
   `h ≡ 1` modulo `IB`. Then `A = B[1/h]` is smooth over `R`.
   Uses: def-weil-pbc-singular-ideal, lem-weil-pbc-zero-locus-eq-iff-radical-eq,
   lem-weil-pbc-singular-ideal-localization-smooth.
6. Localization at `h` preserves the quotient because its image is `1`. The map
   `b/h^n ↦ β(b mod IB)` and the map sending `b₀` to any lifted class `b/1`
   give inverse `R₀`-algebra maps `A/IA ≅ B₀`. Independence of lifts follows since
   their differences lie in `IB`. Uses: def-weil-ring-localization-away.
7. Take `T = Spec A`. Affine smoothness makes its map to `Spec R` smooth. The affine
   fibre-product and quotient-tensor comparisons identify its base change with
   `Spec (A/IA) ≅ Spec B₀ ≅ T₀`. All comparisons respect `R₀`, giving the displayed
   projection equation. Uses: lem-weil-pbc-smooth-ring-map-iff-smooth-affine,
   lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-tensor-over-quotient-ring,
   def-weil-affine-spectrum. For the zero algebra, the prime-indexed arguments are
   vacuous and the same quotient and localization constructions apply. -/
theorem exists_affine_smooth_lift_of_surjective
    (R R₀ : CommRingCat.{u}) (φ : R ⟶ R₀) (hφ : Function.Surjective φ.hom)
    (T₀ : Scheme.{u}) [IsAffine T₀] (f₀ : T₀ ⟶ Spec R₀) [Smooth f₀] :
    ∃ (T : Scheme.{u}) (_ : IsAffine T) (f : T ⟶ Spec R), Smooth f ∧
      ∃ a : pullback f (Spec.map φ) ≅ T₀,
        a.hom ≫ f₀ = pullback.snd f (Spec.map φ) := by
  sorry

end AlgebraicGeometry
