/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.CondensedGenericWeilData
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.AlgebraicClosure
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.PointCount
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Adjoin.FGBaseChange
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.FieldTheory.DeligneLaumon.SepClosedAlgebrasTensorIrreducible
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Field.IsField
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Topology.Connected.Clopen
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.BaseChangeField
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import Mathlib.Topology.Connected.Basic
import Mathlib.AlgebraicGeometry.Limits

/-! # The first-return cycle on the specified geometric component

Source: Deligne, Weil II (1.1.12), the cyclic component argument.
(blueprint: lem-dl-a1-native-weil-component-cycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]
variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]
variable (ell : ℕ) [Fact ell.Prime]

/-- Finite disjoint clopen Frobenius orbit with its first return, on the supplied component.
Source: Deligne, Weil II (1.1.12), constant-field decomposition.
(blueprint: lem-dl-a1-native-weil-component-cycle). -/
structure ComponentCycle (A : Geometry D U₀ t G) where
  n : ℕ
  returnIso : A.component.X ≅ A.component.X
  square : returnIso.hom ≫ A.inclusion =
    A.inclusion ≫ WeilConjectures.localPositivePower (D.geometricFrobenius U₀).hom n
  clopen : ∀ i : Fin (n + 1),
    IsOpenImmersion (A.inclusion ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom) ∧
    IsClosedImmersion (A.inclusion ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom)
  disjoint : Pairwise (fun i j : Fin (n + 1) ↦
    Disjoint (Set.range (A.inclusion ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom))
      (Set.range (A.inclusion ≫ (D.geometricFrobenius U₀ ^ (j : ℕ)).hom)))
  cover : (⋃ i : Fin (n + 1),
    Set.range (A.inclusion ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom)) = Set.univ

private theorem positivePower_iso_hom {X : Scheme.{u}} (g : Aut X) (n : ℕ) :
    WeilConjectures.localPositivePower g.hom n = (g ^ (n + 1)).hom := by
  induction n with
  | zero => simp [WeilConjectures.localPositivePower]
  | succ n ih =>
    simpa [WeilConjectures.localPositivePower, pow_succ', Aut.Aut_mul_def,
      Iso.trans_hom] using congrArg
      (fun f ↦ f ≫ g.hom) ih

/-- The component cycle is the actual finite coproduct cocone of schemes.
Source: Weil II (1.1.12), the disjoint clopen constant-field components.
(blueprint: lem-dl-a1-native-weil-component-cycle).

Proof: each translated inclusion is an open immersion. The cover equation gives
the supremum of their open ranges, and disjointness gives pairwise disjoint opens.
Apply the scheme coproduct criterion, using ULift for its universe-sized index. -/
theorem component_cycle_coproduct (A : Geometry D U₀ t G)
    (B : ComponentCycle D U₀ t G A) :
    Nonempty (IsColimit (Cofan.mk (D.geometricFiber U₀).left
      (fun i : ULift.{u} (Fin (B.n + 1)) ↦
        A.inclusion ≫ (D.geometricFrobenius U₀ ^ (i.down : ℕ)).hom))) := by
  let X := (D.geometricFiber U₀).left
  let Φ := D.geometricFrobenius U₀
  let j (i : ULift.{u} (Fin (B.n + 1))) := A.inclusion ≫ (Φ ^ (i.down : ℕ)).hom
  let (i : ULift.{u} (Fin (B.n + 1))) : IsOpenImmersion (j i) :=
    (B.clopen i.down).1
  apply nonempty_isColimit_cofanMk_of j
  · apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    change (⋃ i : ULift.{u} (Fin (B.n + 1)), Set.range (j i)) = Set.univ
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx : x ∈ ⋃ i : Fin (B.n + 1),
        Set.range (A.inclusion ≫ (Φ ^ (i : ℕ)).hom) := by
      rw [B.cover]
      trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨ULift.up i, hi⟩
  · intro i k hik
    exact (TopologicalSpace.Opens.coe_disjoint).mp (B.disjoint (fun h ↦ hik (ULift.ext _ _ h)))

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
