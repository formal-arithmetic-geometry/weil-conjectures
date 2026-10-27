/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SmoothPurityReductionMonoidalData

/-! # Strict tensor balancing for simultaneous reduction

Source: Stacks 03EL and 07A4; blueprint integral direct-image proof (3)
(blueprint: lem-sp-reduction-strict-tensor-balancing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The ordinary and signed-total comparison, before localization.
Source: Stacks 03EL, 07A4
(blueprint: lem-sp-reduction-strict-tensor-balancing). -/
structure SpReductionStrictTensor (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) where
  /-- Ordinary tensor balancing before any localization. -/
  ordinary : ∀ M N : spIntegralSectionModules l E T,
    (spMonoidalOrdinary l E T D r).obj
      (ordinaryTensor.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (spIntegralSectionRing l E T) M N) ≅
    ordinaryTensor.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (spMonoidalSystemRing l E T)
      ((spMonoidalOrdinary l E T D r).obj M) ((spMonoidalOrdinary l E T D r).obj N)
  /-- One isomorphism of actual strict-system complexes, natural before evaluation. -/
  chain :
    (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).prod
      ((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ))) ⋙
        spMonoidalSystemTotal l E T ≅
    spMonoidalIntegralTotal l E T ⋙
      (spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)

  /-- Forward balancing on all sheafified generators. -/
  forward :
    ∀ (M N : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
      (x : M.val.obj U) (y : N.val.obj U)
      (a : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U),
      ((ordinary M N).hom.val.app (op (n, U.unop)))
        (spMonoidalGenerator l E T D r _ n U a
          (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            (spIntegralSectionRing l E T) M N U x y)) =
      tensorSection.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (spMonoidalSystemRing l E T) _ _ (op (n, U.unop))
        (spMonoidalGenerator l E T D r M n U 1 x)
        (spMonoidalGenerator l E T D r N n U a y)
  /-- Inverse balancing multiplies the two quotient coefficients. -/
  inverse :
    ∀ (M N : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
      (x : M.val.obj U) (y : N.val.obj U)
      (a b : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U),
      ((ordinary M N).inv.val.app (op (n, U.unop)))
        (tensorSection.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
          (spMonoidalSystemRing l E T) _ _ (op (n, U.unop))
          (spMonoidalGenerator l E T D r M n U a x)
          (spMonoidalGenerator l E T D r N n U b y)) =
      spMonoidalGenerator l E T D r _ n U (a * b)
        (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (spIntegralSectionRing l E T) M N U x y)
  /-- The chain map restricts to inverse balancing on each total summand. -/
  summand :
    ∀ (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ)
      (p q k : ℤ) (h : p + q = k),
      tensorSummand.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (spMonoidalSystemRing l E T)
        (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P)
        (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj Q) p q k h ≫
          (chain.hom.app (P,Q)).f k =
      (ordinary (P.X p) (Q.X q)).inv ≫ (spMonoidalOrdinary l E T D r).map
        (tensorSummand.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (spIntegralSectionRing l E T) P Q p q k h)

/-- Simultaneous reduction has its normalized strict tensor comparison.
Source: Stacks 03EL, 07A4; original node, steps 1 and 4
(blueprint: lem-sp-reduction-strict-tensor-balancing).

Proof: identify the ordinary reduction with extension along the sequence projection.
Use its level identifications and the specified quotient transition on local tensor
sections; tensor generation and sheafification determine this identification on maps.
On each vertical slice define inverse balancing by
`(x tensor a) tensor (y tensor b) |-> (x tensor y) tensor (a*b)`.
Define forward balancing by inserting 1 in the first coefficient factor. Both maps
are balanced and descend through sheafification. Their composites are identities,
since balancing moves a to the second factor and `1*a=a`. Multiplicativity of each
quotient restriction makes these maps commute with every horizontal transition.
Naturality gives the ordinary comparison for all modules, with no flatness assumption.
Extension of scalars preserves the direct sums in totalization. Apply inverse
balancing on each total summand. The differential in the second degree has the
same sign `(-1)^p` on both sides, so the two inverse maps are chain maps.
The coproduct universal property proves naturality and the displayed summand formula.
This constructs an isomorphism of strict sequence-site complexes, before localization;
zero modules, the empty site and nonflat coefficient maps require no exceptions. -/
theorem sp_reduction_strict_tensor_balancing (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) : Nonempty (SpReductionStrictTensor l E T D r) := by
  sorry

end AlgebraicGeometry.ProEtale
