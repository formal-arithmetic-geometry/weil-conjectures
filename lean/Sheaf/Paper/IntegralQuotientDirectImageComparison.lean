/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.IntegralQuotientProjectionMap
public import Sheaf.Paper.IntegralQuotientCoefficients
public import Sheaf.Paper.InternalDerivedScalarComparisons
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import Sheaf.Algebra.Homology.FlatScalarCyclicResolution
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Paper.SectionDerivedPushpullNormalization
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization

/-! # Integral quotient comparison for unbounded direct image

Source: blueprint main-20261015, integral proper base change proof, paragraphs (1), (3)
(blueprint: lem-sfb-integral-quotient-direct-image-comparison).

The mate is formed with the actual derived adjunctions. Quotient levels are indexed by
n + 1 and every tensor product is the ordinary, uncompleted derived tensor product.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProEtale.QuotientChange
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The quotient-linear unbounded direct-image comparison, its exact projection
normalization, the actual augmented two-term resolution, and compatibility at all
positive quotient levels. No condition is imposed on the scheme morphism or complex.

Source: blueprint main-20261015 integral proper-base-change proof, paragraphs (1), (3);
Stacks Tags 093M, 06YY, 0D6D, 0D6E, 0G7E, 07A6 and 0944
(blueprint: lem-sfb-integral-quotient-direct-image-comparison).

Proof:
1. The recorded coefficient ring is a Noetherian DVR; its positive uniformizer quotients
are finite. The integral-limit identification and completed-constant-sheaf reduction
identify the actual projection cokernel with the finite constant quotient. The scalar
cyclic-resolution lemma makes the cone of pi^(n+1) a flat-term K-flat resolution with
exactly the displayed augmentation equation.
2. Use the internal/section module tensor equivalence and the unbounded change-of-rings
model to compute extension on flat-term K-flat representatives. Balanced tensor
associativity gives the tensor normalization and the scalar/pullback comparison. Its
universal computation counit identity is PullNormalized, with the actual ordinary
pullIso, and hence fixes its pure-tensor formula and its inverse uniquely.
3. Form rho as the adjunction mate. Section-derived pushpull normalization preserves
both adjunction counits; ring-sheaf change adjunction identifies restriction of the mate
with the adjunct of the derived tensor comparison followed by the integral counit and
the cartesian coefficient map. This is precisely projectionMap, giving the displayed
equality after the normalized tensor identifications.
4. The perfect projection formula applies because every finite quotient has the
specified two-term free resolution. Thus the restricted rho is invertible on every
unbounded complex. Exact scalar restriction reflects isomorphisms, proving IsIso rho.
5. For n >= m, successive-derived-quotient normalization supplies beta with its actual
balanced representative map and scalar-unit normalization. Pullback balancing respects
composition by ringed derived monoidal coherence. Pasting the two adjunction-mate
squares gives the final equality in the S_m coefficient category. No flatness of the
finite quotient transition, nor invertibility of its mate on arbitrary inputs, is used.
Identity transitions, zero complexes and empty schemes are included. -/
theorem integral_quotient_direct_image_comparison :
    ∃ t : ∀ (T : Scheme.{u}) (n : ℕ), TensorNormalization (reduction l E n) T,
      (∀ (T : Scheme.{u}) (n : ℕ), TensorNormalized (reduction l E n) T (t T n)) ∧
      (∀ (T : Scheme.{u}) (n : ℕ),
        ∃ ε : resolution l E T n ⟶
            (CochainComplex.singleFunctor _ 0).obj (B₀ (reduction l E n) T),
          CochainComplex.mappingCone.inr
              ((CochainComplex.singleFunctor _ 0).map (multiplication l E T n)) ≫ ε =
            (CochainComplex.singleFunctor _ 0).map (projection l E T n) ∧
          QuasiIso ε ∧
          (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (resolution l E T n) ∧
          (∀ i : ℤ, ObjectProperty.flat ((resolution l E T n).X i))) ∧
      ∃ b : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
          D (reduction l E n) Y ⋙ L (finite l E n) f ≅
            L (integral l E) f ⋙ D (reduction l E n) X,
        (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
          PullNormalized (reduction l E n) f (b f n)) ∧
        (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
          IsIso (rho (reduction l E n) f (b f n))) ∧
        (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
            (K : DerivedCategory (Modules (integral l E) X)),
          (V (reduction l E n) Y).map ((rho (reduction l E n) f (b f n)).app K) ≫
              (restrictPush (reduction l E n) f (b f n)).hom.app
                ((D (reduction l E n) X).obj K) ≫
              (F (integral l E) f).map ((t X n).derived.hom.app K) =
            (t Y n).derived.hom.app ((F (integral l E) f).obj K) ≫
              projectionMap l E f n K) ∧
        (∀ (n m : ℕ) (h : m ≤ n),
          ∃ β : ∀ T : Scheme.{u},
              D (reduction l E n) T ⋙ D (finiteMap l E n m h) T ≅
                D (reduction l E m) T,
            (∀ T : Scheme.{u},
              SuccessiveNormalized (reduction l E n) (finiteMap l E n m h)
                (reduction l E m) (reduction_comp l E n m h) T (β T)) ∧
            ∃ c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
                D (finiteMap l E n m h) Y ⋙ L (finite l E m) f ≅
                  L (finite l E n) f ⋙ D (finiteMap l E n m h) X,
              (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
                PullNormalized (finiteMap l E n m h) f (c f)) ∧
              ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
                  (K : DerivedCategory (Modules (integral l E) X)),
                (β Y).hom.app ((F (integral l E) f).obj K) ≫
                    (rho (reduction l E m) f (b f m)).app K =
                  (D (finiteMap l E n m h) Y).map
                      ((rho (reduction l E n) f (b f n)).app K) ≫
                    (rho (finiteMap l E n m h) f (c f)).app
                      ((D (reduction l E n) X).obj K) ≫
                    (F (finite l E m) f).map ((β X).hom.app K)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralQuotient
