/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Paper.PointWeilHeartFlagData
import Sheaf.Paper.PointHeartFiniteStage
import Sheaf.LinearAlgebra.AutomorphismFlagFiniteCoefficients
import Sheaf.Paper.PointEquivariantDiagramLift

/-! # Algebraic point flags with a simultaneous finite coefficient model

Source: latest blueprint, `thm-zl-real-mixed-by-curves`, paragraph 7,
dimension-zero Jordan filtration, algebraic construction before assigning weights
(blueprint: lem-zl-point-weil-algebraic-flag).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (y : {y : (zlPointBase D).left // y ∈ closedPoints (zlPointBase D).left})
  (ι : (zlPointBase D).left.residueField y.val →+* D.k)
  (hι : ι.comp ((zlPointBase D).hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)

/-- The algebraic clauses of the full point flag, without an embedding into C or weights.
Source: paragraph 7, invariant Jordan filtration
(blueprint: lem-zl-point-weil-algebraic-flag). -/
def ZlPointWeilFlagAlgebraic
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω)
    (H : ZlPointWeilFlagDiagram D l hl Ω F) : Prop :=
  -- dimension
  (Module.finrank Ω ((zlPointWeilFiber D l hl Ω y ι hι).obj F) = H.d) ∧
  -- finite
  (FiniteDimensional Ω ((zlPointWeilFiber D l hl Ω y ι hι).obj F)) ∧
  -- into_mono
  (∀ j, Mono ((zlPointCommonHeart D l hl Ω).map (H.into j))) ∧
  -- into_step
  (∀ j : Fin H.d, H.step j ≫ H.into j.succ = H.into j.castSucc) ∧
  -- initial
  (IsZero (H.G 0)) ∧
  -- terminal
  (IsIso (H.into (Fin.last H.d))) ∧
  -- rank
  (∀ j, Module.finrank Ω ((zlPointWeilFiber D l hl Ω y ι hι).obj (H.G j)) = j.val) ∧
  -- shortExact
  (∀ j : Fin H.d,
    (ShortComplex.mk ((zlPointCommonHeart D l hl Ω).map (H.step j))
      ((zlPointCommonHeart D l hl Ω).map (H.projection j)) (H.zero j)).ShortExact) ∧
  -- quotient_rank
  (∀ j, Module.finrank Ω ((zlPointWeilFiber D l hl Ω y ι hι).obj (H.Q j)) = 1) ∧
  -- quotient_scalar
  (∀ (j : Fin H.d) (v : (zlPointWeilFiber D l hl Ω y ι hι).obj (H.Q j)),
    (zlPointWeilFrobenius D l hl Ω y ι hι (H.Q j)).hom v = (H.α j : Ω) • v) ∧
  -- flag_monotone
  (Monotone (fun j ↦
    LinearMap.range ((zlPointWeilFiber D l hl Ω y ι hι).map (H.into j)).hom)) ∧
  -- flag_invariant
  (∀ j,
    (LinearMap.range ((zlPointWeilFiber D l hl Ω y ι hι).map (H.into j)).hom).map
      (zlPointWeilFrobenius D l hl Ω y ι hι F).hom =
        LinearMap.range ((zlPointWeilFiber D l hl Ω y ι hι).map (H.into j)).hom) ∧
  -- frobenius_bijective
  (Function.Bijective (zlPointWeilFrobenius D l hl Ω y ι hι F).hom) ∧
  -- flag_bijective
  (∀ j,
    Function.Bijective (zlPointWeilFrobenius D l hl Ω y ι hι (H.G j)).hom) ∧
  -- quotient_bijective
  (∀ j,
    Function.Bijective (zlPointWeilFrobenius D l hl Ω y ι hι (H.Q j)).hom)

/-- Construct the algebraic Weil flag and descend its entire finite diagram to one field.
The specified quotients are cokernels in the Weil heart itself, as well as giving
short exact sequences in the underlying heart. No weight or complex embedding occurs.

Source: latest blueprint, `thm-zl-real-mixed-by-curves`, paragraph 7,
dimension-zero Jordan filtration; steps 1-3 and 5 of `lem-zl-point-weil-heart-flag`
(blueprint: lem-zl-point-weil-algebraic-flag).

Proof: apply zl_point_heart_finite_stage to descend the given Weil heart object and
its inverse Weil map to one finite field. Its specified H^0 fibre is finite dimensional,
and the local Frobenius is invertible, including point transport. Choose a basis and
apply LinearEquiv.exists_flag_finite_coefficients. Enlarge the initial coefficient
field to the finite intermediate field supplied there, using the Shrink equivalence
to pass to the library's coefficient model. Its adapted basis gives initial spans of
ranks j, quotient lines, invertible restrictions and quotient operators with unit scalars.
Apply zl_point_equivariant_diagram_lift to the finite diagram of these spaces,
inclusions and quotient maps, prescribing the scalar extension of the original Weil
object at the endpoint. Transport along the canonical geometric-point identification
and the prescribed endpoint isomorphism. Naturality and scalar compatibility of point
transport identify each lifted local operator with its original linear operator.
Exactness of the heart equivalence gives the displayed short exact sequences and
monomorphisms. For the cokernel universal property, lift the heart cokernel factorization;
its uniqueness forces it to intertwine Frobenius (cancel the Frobenius pullback of the
epimorphic quotient projection). Thus each quotient is also the Weil-heart cokernel.
Extend the whole finite diagram to Omega, retaining the prescribed endpoint. Exact
scalar extension preserves ranks, inclusions, quotients and inverse identities. All
comparison squares and scalars are those of this one finite coefficient stage.
For dimension zero the construction is the singleton zero endpoint, with no quotients;
no simplicity, semisimplicity or reality hypothesis is used. -/
theorem zl_point_weil_algebraic_flag
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) :
    ∃ (H : ZlPointWeilFlagDiagram D l hl Ω F)
      (T : ZlPointWeilFlagFiniteDiagram D l hl Ω F H),
      ZlPointWeilFlagAlgebraic D l hl Ω y ι hι F H ∧
      ZlPointWeilHeartFlagModel D l hl Ω y ι hι F H T ∧
      (∀ j, Mono (H.step j)) ∧
      (∀ j, Nonempty (cokernel (H.step j) ≅ H.Q j)) := by sorry

end WeilConjectures
