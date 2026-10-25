/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.TraceFormula.Specialization.PointsSupport

/-!

# Complexes supported at finitely many closed points

Let `V` be a separated scheme of finite type over a separably closed field `k` and `S` a finite
set of closed points of `V`. A bounded constructible `ℚ̄_ℓ`-complex `C` on `V` whose restriction to
`V ∖ S` vanishes, and whose global sections `RΓ(V, C)` vanish, is zero
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`, blueprint
`det-nearby-kunneth-finite-support`).

The closed points need not be rational: `k` need not be perfect. This generalises
`WeilConjectures.TraceFormula.Specialization.PointsSupport` (rational points). The residue field
`κ(z)` of a closed point is finite, hence purely inseparable, over `k`, so it is separably closed
(`ProEtale.CondensedRing.isSepClosed_of_locallyOfFiniteType`). Every bounded constructible complex
on `Spec κ(z)` is then a finite direct sum of shifts of the unit, and `RΓ(Spec κ(z), -)` detects
vanishing (`ProEtale.CondensedRing.isZero_of_isZero_lowerStar_toPoint_of_isSepClosed`): a summand
`𝟙⟦d⟧ = La^* 𝟙⟦d⟧ ⟶ E` is adjoint to a morphism into `Ra_* E = 0`. The open–closed triangle at a
closed point then splits as for rational points, and one concludes by induction on `S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Residue fields of closed points -/

section ResidueField

variable {k : Type u} [Field k] (K : Type u) [Field K]

/-- A field of finite type over a separably closed field `k` (through a morphism
`Spec K ⟶ Spec k` locally of finite type) is separably closed: it is finite, hence purely
inseparable, over `k`. -/
lemma isSepClosed_of_locallyOfFiniteType [IsSepClosed k] (g : Spec (.of K) ⟶ Spec (.of k))
    [LocallyOfFiniteType g] : IsSepClosed K := by
  let f : CommRingCat.of k ⟶ CommRingCat.of K := Spec.preimage g
  have hf : f.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map f) := by
      rw [Spec.map_preimage]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  letI := f.hom.toAlgebra
  have : Algebra.FiniteType k K := hf
  have := finite_of_finite_type_of_isJacobsonRing k K
  exact Algebra.IsAlgebraic.isSepClosed (F := k) (E := K)

/-- A field receiving a morphism from `k` has the characteristic of `k`. -/
lemma ringChar_eq_of_spec (g : Spec (.of K) ⟶ Spec (.of k)) : ringChar K = ringChar k := by
  letI := (Spec.preimage g).hom.toAlgebra
  exact (Algebra.ringChar_eq k K).symm

end ResidueField

/-! ### Closed points as schemes over `k` -/

section ClosedPoint

variable {k : Type u} [Field k] {V : Over (Spec (.of k))}

/-- The closed point `Spec κ(z)` of `V`, as a scheme over `k`. -/
noncomputable abbrev closedPointOver (z : V.left) : Over (Spec (.of k)) :=
  Over.mk (V.left.fromSpecResidueField z ≫ V.hom)

/-- The inclusion `Spec κ(z) ⟶ V` of a point. -/
noncomputable abbrev closedPointι (z : V.left) : closedPointOver z ⟶ V :=
  Over.homMk (V.left.fromSpecResidueField z)

lemma range_closedPointι (z : V.left) : Set.range (closedPointι z).left.base = {z} :=
  Scheme.range_fromSpecResidueField z

lemma isClosedImmersion_closedPointι {z : V.left} (hz : IsClosed {z}) :
    IsClosedImmersion (closedPointι z).left :=
  isClosed_singleton_iff_isClosedImmersion.1 hz

lemma locallyOfFiniteType_closedPointOver [LocallyOfFiniteType V.hom] {z : V.left}
    (hz : IsClosed {z}) : LocallyOfFiniteType (closedPointOver z).hom := by
  have : IsClosedImmersion (V.left.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.1 hz
  exact inferInstanceAs (LocallyOfFiniteType (V.left.fromSpecResidueField z ≫ V.hom))

lemma quasiCompact_closedPointOver [QuasiCompact V.hom] {z : V.left}
    (hz : IsClosed {z}) : QuasiCompact (closedPointOver z).hom := by
  have : IsClosedImmersion (V.left.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.1 hz
  exact inferInstanceAs (QuasiCompact (V.left.fromSpecResidueField z ≫ V.hom))

lemma isSeparated_closedPointOver [IsSeparated V.hom] {z : V.left}
    (hz : IsClosed {z}) : IsSeparated (closedPointOver z).hom := by
  have : IsClosedImmersion (V.left.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.1 hz
  exact inferInstanceAs (IsSeparated (V.left.fromSpecResidueField z ≫ V.hom))

end ClosedPoint

/-! ### Global sections on a separably closed point -/

section Point

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Global sections detect vanishing on a separably closed point**: let `P` be a `k`-scheme
of finite type whose underlying scheme is `Spec K` for a separably closed field `K`. A bounded
constructible complex `E` on `P` with `RΓ(P, E) = 0` vanishes. Indeed `E` is a finite direct sum of
shifts `𝟙⟦d⟧` of the unit, and every morphism `𝟙⟦d⟧ = La^* 𝟙⟦d⟧ ⟶ E` is adjoint to a morphism
`𝟙⟦d⟧ ⟶ Ra_* E = 0`. -/
theorem isZero_of_isZero_lowerStar_toPoint_of_isSepClosed {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (K : Type u) [Field K] [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
    (hP : P.left = Spec (.of K)) (E : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hE : IsZero ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (toPoint P)).obj E)) : IsZero E := by
  obtain ⟨P, f, rfl⟩ : ∃ (P' : Scheme.{u}) (f : P' ⟶ Spec (.of k)), P = Over.mk f :=
    ⟨P.left, P.hom, rfl⟩
  dsimp only [Over.mk_left] at hP
  subst hP
  let Dc := (nonempty_shiftDecomposition_point ℓ K E).some
  set adj := boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
    (toPoint (Over.mk f))
  have hincl : ∀ j, Dc.incl j = 0 := fun j ↦ by
    let e : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (toPoint (Over.mk f))).obj ((shiftFunctor _ (Dc.deg j)).obj (𝟙_ _)) ≅
        (shiftFunctor _ (Dc.deg j)).obj (𝟙_ _) :=
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (toPoint (Over.mk f))).commShiftIso (Dc.deg j)).app _ ≪≫
        (shiftFunctor _ (Dc.deg j)).mapIso (Functor.Monoidal.εIso _).symm
    have h0 : adj.homEquiv _ _ (e.hom ≫ Dc.incl j) = 0 := hE.eq_of_tgt _ _
    have h1 : e.hom ≫ Dc.incl j = 0 := by
      rw [← (adj.homEquiv _ _).symm_apply_apply (e.hom ≫ Dc.incl j), h0,
        Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
    simpa using h1
  refine (IsZero.iff_id_eq_zero E).2 ?_
  rw [← Dc.total]
  exact Finset.sum_eq_zero fun j _ ↦ by rw [hincl j, comp_zero]

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
