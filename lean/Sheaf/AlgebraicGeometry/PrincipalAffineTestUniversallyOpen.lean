module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Principal-open affine tests for universal openness

Source: Stacks Project, Tag 0F31, proof of (3) implies (1), affine localization and
principal-open basis reduction; Tags 01JR, 01I4, 01JP and 01IT for the chart identifications
(blueprint: lem-sfb-principal-affine-test-universally-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Principal-open images after all affine base changes suffice for universal openness,
including the scheme identifications and image formula on every affine chart.

Source: Stacks Project, Tag 0F31, proof of (3) implies (1), first paragraph and
principal-open basis reduction; Tags 01JR, 01I4, 01JP and 01IT
(blueprint: lem-sfb-principal-affine-test-universally-open).

Here `Algebra A C` encodes the given ring map. The cartesian square `hP` permits any
representative of the fibre product, in particular Mathlib's chosen `pullback`.
The condition on `e` says exactly that the algebra structure on `B` is the one
corresponding to the restriction of `a` in the specified affine coordinates.

Proof plan:
1. By [lem-weil-pbc-spec-localization-away-basic-open], every open in the tensor
   spectrum is a union of principal opens. Images commute with arbitrary unions,
   so the hypothesis makes every affine tensor projection open, even for zero rings.
2. Apply [lem-weil-pbc-open-fibre-product] with the full opens in the base and source
   and with `W` in `T`. This identifies the restriction with the open inverse image
   of `W`. The universal property [def-pc-fibre-product] identifies it with
   `pullback q W.ι`, compatibly with both projections.
3. The coordinates `e` and [def-weil-affine-spectrum] give the unique map `A → B`.
   Interchange the two factors and apply [lem-weil-pbc-fibre-product-affine-spectra]
   to obtain the tensor-spectrum isomorphism and the displayed projection equation.
4. For an open `O`, a point of `q(O)` in `W` has a preimage already in the inverse
   image of `W`. This gives the displayed image identity. Step 1 makes this image
   open in `W`, hence in `T`. By [lem-weil-pbc-affine-opens-basis] these charts cover
   `T`, so `q(O)` is open. This proves universal openness. Empty schemes, empty
   opens and infinite affine covers are included: only arbitrary unions are used. -/
theorem principalAffineTest_universallyOpen
    (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B] (g : B ⊗[A] C),
      IsOpen ((Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C))) ''
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (B ⊗[A] C))))) :
    (∀ (B : Type u) [CommRing B] [Algebra A B],
      IsOpenMap (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C)))) ∧
    UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap A C))) ∧
    ∀ (T : Scheme.{u}) (a : T ⟶ Spec (CommRingCat.of A))
      (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of C)) (q : P ⟶ T),
      IsPullback p q (Spec.map (CommRingCat.ofHom (algebraMap A C))) a →
      IsOpenMap q ∧
      ∀ (W : T.Opens) (B : Type u) [CommRing B] [Algebra A B]
        (e : W.toScheme ≅ Spec (CommRingCat.of B)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = W.ι ≫ a →
        ∃ (i : pullback q W.ι ≅ Spec (CommRingCat.of (B ⊗[A] C))),
          i.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C)) =
              pullback.snd q W.ι ≫ e.hom ∧
          IsOpenImmersion (pullback.fst q W.ι) ∧
          Set.range (pullback.fst q W.ι) = q ⁻¹' (W : Set T) ∧
          ∀ (O : P.Opens),
            q '' (O : Set P) ∩ (W : Set T) =
              W.ι '' (e.inv '' ((Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C))) ''
                  (i.hom '' ((pullback.fst q W.ι) ⁻¹' (O : Set P))))) ∧
            IsOpen (e.inv '' ((Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C))) ''
                (i.hom '' ((pullback.fst q W.ι) ⁻¹' (O : Set P))))) ∧
            IsOpen (q '' (O : Set P) ∩ (W : Set T)) :=
  sorry

end AlgebraicGeometry
