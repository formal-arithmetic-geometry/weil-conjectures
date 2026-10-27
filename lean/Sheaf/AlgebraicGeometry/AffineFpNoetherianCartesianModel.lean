module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Noetherian cartesian model of a finitely presented affine morphism

Source: Stacks Project, Tag 00QJ, proof of
`lemma-dimension-fibres-bounded-quasi-compact-open-upstairs`, finite-coefficient model.
(blueprint: lem-trf-affine-fp-noetherian-cartesian-model)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-- A finitely presented ring map admits a finite-type Noetherian model. The tensor
isomorphism uses the right-factor `R`-algebra structure, sends pure tensors to the
product of their images, and identifies both projections of the affine base change.

Source: Stacks Project, Tag 00QJ, finite-coefficient paragraph in the proof of
`lemma-dimension-fibres-bounded-quasi-compact-open-upstairs`.

Proof:
1. Choose a finite presentation of `B` over `R`. Its finitely many relations have
   finitely many coefficients (def-weil-pbc-mv-polynomial-ring). Let `R₀` be the image
   in `R` of the integer polynomial algebra on these coefficients. Use the same
   relations over `R₀` to define `B₀`. Inclusion of coefficients and the presentation
   induce `β : B₀ →+* B` and the commutative square. The coefficient generators make
   `R₀` finite type over the integers; the variable classes make `B₀` finite type
   over `R₀` (def-weil-pbc-finite-type-algebra, def-weil-pbc-algebra-hom-quotient).
2. Every ideal of the integers is principal, by division by its least positive
   element (including the zero ideal). Apply finite-type-algebra-noetherian first
   to the integers and `R₀`, then to `R₀` and `B₀`, proving both Noetherian assertions.
3. Apply lem-weil-pbc-presentation-base-change to the quotient presentation of `B₀`.
   This gives the tensor isomorphism with `B`. Its formula is the canonical product
   formula because it agrees on the variable classes and the image of `R`; uniqueness
   is lem-weil-pbc-algebra-tensor-pushout-universal-property.
4. Apply lem-weil-pbc-fibre-product-affine-spectra. The spectrum of the tensor
   isomorphism followed by the inverse affine-pullback comparison has projections
   `Spec β` and `Spec (algebraMap R B)`, by the formula in step 3 and functoriality
   of def-weil-affine-spectrum.
5. The one-member affine neighbourhoods prove that `h₀` is locally of finite type
   by lem-weil-pbc-lft-pointwise-criterion. Both endpoints of `q` are affine, so
   lem-weil-pbc-morphism-affine-schemes-affine and clause (3) of
   lem-weil-pbc-affine-morphism-permanence make `q` quasi-compact. The one-member
   Noetherian affine cover proves that `Spec B₀` is locally Noetherian, and
   lem-weil-pbc-affine-scheme-qcqs gives its quasi-compactness.

(blueprint: lem-trf-affine-fp-noetherian-cartesian-model) -/
theorem exists_affine_fp_noetherian_cartesian_model
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] :
    ∃ (R₀ B₀ : CommRingCat.{u}) (_ : Algebra R₀ B₀) (_ : Algebra R₀ R)
      (β : B₀ →+* B),
      β.comp (algebraMap R₀ B₀) = (algebraMap R B).comp (algebraMap R₀ R) ∧
      (algebraMap ℤ R₀).FiniteType ∧ (algebraMap R₀ B₀).FiniteType ∧
      IsNoetherianRing R₀ ∧ IsNoetherianRing B₀ ∧
      ∃ e : @AlgEquiv R (B₀ ⊗[R₀] R) B _ _ _
          (Algebra.TensorProduct.rightAlgebra (R := R₀) (A := B₀) (B := R)) _,
        (∀ (b : B₀) (r : R), e (b ⊗ₜ[R₀] r) = β b * algebraMap R B r) ∧
        Spec.map (CommRingCat.ofHom
            (@AlgEquiv.toRingEquiv R (B₀ ⊗[R₀] R) B _ _ _
              (Algebra.TensorProduct.rightAlgebra (R := R₀) (A := B₀) (B := R)) _
              e).toRingHom) ≫
            (pullbackSpecIso R₀ B₀ R).inv ≫
              pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R₀ B₀)))
                (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) =
          Spec.map (CommRingCat.ofHom β) ∧
        Spec.map (CommRingCat.ofHom
            (@AlgEquiv.toRingEquiv R (B₀ ⊗[R₀] R) B _ _ _
              (Algebra.TensorProduct.rightAlgebra (R := R₀) (A := B₀) (B := R)) _
              e).toRingHom) ≫
            (pullbackSpecIso R₀ B₀ R).inv ≫
              pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R₀ B₀)))
                (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) =
          Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
        LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R₀ B₀))) ∧
        QuasiCompact (Spec.map (CommRingCat.ofHom β)) ∧
        IsLocallyNoetherian (Spec B₀) ∧ CompactSpace (Spec B₀) := by
  sorry

end AlgebraicGeometry
